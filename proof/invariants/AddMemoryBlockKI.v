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

Require Import Proof.Isolation Proof.Hoare Proof.Consistency Proof.WeakestPreconditions
Proof.StateLib Proof.DependentTypeLemmas Proof.InternalLemmas.

Require Import Invariants.

Require Import Bool List EqNat Lia Compare_dec Coq.Logic.ProofIrrelevance.
Import List.ListNotations.

Require Import Model.Monad.

Module WP := WeakestPreconditions.

(* AddMemoryBlock security properties *)

Lemma AddMemoryBlockKI
idPDchild idBlockToShare
r w e
currentPart blockToShareInCurrPartAddr
addrIsNull
rcheck
isChildCurrPart
globalIdPDChild
nbfreeslots zero
isFull
childfirststructurepointer
slotIsNull
addrIsAccessible
addrIsPresent
vidtBlockGlobalId
blockstart blockend blockToShareChildEntryAddr

pdentry pdentry0 pdentry1
bentry bentry0 bentry1 bentry2 bentry3 bentry4 bentry5 bentry6
sceaddr
scentry
newBlockEntryAddr newFirstFreeSlotAddr
predCurrentNbFreeSlots
sh1eaddr
sh1entry sh1entry0 sh1entry1
sh1entrybts

s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10
s
 :

addrIsNull = false /\
negb rcheck = false /\
negb isChildCurrPart = false /\
isFull = false /\
negb addrIsAccessible = false /\
negb addrIsPresent = false /\
slotIsNull = false /\ 
beqAddr vidtBlockGlobalId blockToShareInCurrPartAddr = false


/\ (
 partitionsIsolation s0 /\
          kernelDataIsolation s0 /\
          verticalSharing s0 /\
          consistency s0 /\
          consistency s0 /\
          isPDT currentPart s0 /\
          currentPart = currentPartition s0 /\
          (blockToShareInCurrPartAddr = nullAddr \/
           (exists entry : BlockEntry,
              lookup blockToShareInCurrPartAddr (memory s0) beqAddr = Some (BE entry) /\
              blockToShareInCurrPartAddr = idBlockToShare)) /\
          beqAddr nullAddr blockToShareInCurrPartAddr = false /\
          (exists entry : BlockEntry,
             lookup blockToShareInCurrPartAddr (memory s0) beqAddr = Some (BE entry)) /\
          (isChildCurrPart = true ->
           exists sh1entryaddr : paddr,
             isChildCurrPart = checkChild idPDchild s0 sh1entryaddr /\
             (exists entry : BlockEntry,
                lookup idPDchild (memory s0) beqAddr = Some (BE entry) /\
                (exists sh1entry : Sh1Entry,
                   sh1entryAddr idPDchild sh1entryaddr s0 /\
                   lookup sh1entryaddr (memory s0) beqAddr = Some (SHE sh1entry)))) /\
          bentryStartAddr idPDchild globalIdPDChild s0 /\
          isPDT globalIdPDChild s0 /\
          pdentryNbFreeSlots globalIdPDChild nbfreeslots s0 /\
          zero = CIndex 0 /\
          false = StateLib.Index.leb nbfreeslots zero /\
          pdentryFirstFreeSlot globalIdPDChild childfirststructurepointer s0 /\
          beqAddr nullAddr childfirststructurepointer = false /\
          bentryAFlag blockToShareInCurrPartAddr addrIsAccessible s0 /\
          bentryPFlag blockToShareInCurrPartAddr addrIsPresent s0 /\
          pdentryVidt globalIdPDChild vidtBlockGlobalId s0 /\
          bentryStartAddr blockToShareInCurrPartAddr blockstart s0 /\
          bentryEndAddr blockToShareInCurrPartAddr blockend s0)

/\ (s =
     {|
       currentPartition := currentPartition s0;
       memory :=
         add sh1eaddr
           (SHE
              {|
                PDchild := PDchild sh1entry0;
                PDflag := PDflag sh1entry0;
                inChildLocation := blockToShareChildEntryAddr
              |})
           (add sh1eaddr
              (SHE
                 {|
                   PDchild := globalIdPDChild;
                   PDflag := PDflag sh1entry;
                   inChildLocation := inChildLocation sh1entry
                 |})
              (add sceaddr (SCE {| origin := blockstart; next := next scentry |})
                 (add newBlockEntryAddr
                    (BE
                       (CBlockEntry (read bentry5) (write bentry5) e
                          (present bentry5) (accessible bentry5) 
                          (blockindex bentry5) (blockrange bentry5)))
                    (add newBlockEntryAddr
                       (BE
                          (CBlockEntry (read bentry4) w (exec bentry4)
                             (present bentry4) (accessible bentry4)
                             (blockindex bentry4) (blockrange bentry4)))
                       (add newBlockEntryAddr
                          (BE
                             (CBlockEntry r (write bentry3) 
                                (exec bentry3) (present bentry3) 
                                (accessible bentry3) (blockindex bentry3)
                                (blockrange bentry3)))
                          (add newBlockEntryAddr
                             (BE
                                (CBlockEntry (read bentry2) 
                                   (write bentry2) (exec bentry2) true
                                   (accessible bentry2) (blockindex bentry2)
                                   (blockrange bentry2)))
                             (add newBlockEntryAddr
                                (BE
                                   (CBlockEntry (read bentry1) 
                                      (write bentry1) (exec bentry1)
                                      (present bentry1) true 
                                      (blockindex bentry1) 
                                      (blockrange bentry1)))
                                (add newBlockEntryAddr
                                   (BE
                                      (CBlockEntry (read bentry0) 
                                         (write bentry0) 
                                         (exec bentry0) (present bentry0)
                                         (accessible bentry0) 
                                         (blockindex bentry0)
                                         (CBlock (startAddr (blockrange bentry0))
                                            blockend)))
                                   (add newBlockEntryAddr
                                      (BE
                                         (CBlockEntry (read bentry) 
                                            (write bentry) 
                                            (exec bentry) 
                                            (present bentry) 
                                            (accessible bentry) 
                                            (blockindex bentry)
                                            (CBlock blockstart
                                               (endAddr (blockrange bentry)))))
                                      (add globalIdPDChild
                                         (PDT
                                            {|
                                              structure := structure pdentry0;
                                              firstfreeslot := firstfreeslot pdentry0;
                                              nbfreeslots := predCurrentNbFreeSlots;
                                              nbprepare := nbprepare pdentry0;
                                              parent := parent pdentry0;
                                              MPU := MPU pdentry0;
                                              vidtBlock := vidtBlock pdentry0
                                            |})
                                         (add globalIdPDChild
                                            (PDT
                                               {|
                                                 structure := structure pdentry;
                                                 firstfreeslot :=
                                                   newFirstFreeSlotAddr;
                                                 nbfreeslots :=
                                                   ADT.nbfreeslots pdentry;
                                                 nbprepare := nbprepare pdentry;
                                                 parent := parent pdentry;
                                                 MPU := MPU pdentry;
                                                 vidtBlock := vidtBlock pdentry
                                               |}) (memory s0) beqAddr) beqAddr)
                                      beqAddr) beqAddr) beqAddr) beqAddr) beqAddr)
                       beqAddr) beqAddr) beqAddr) beqAddr) beqAddr
     |})

/\ 
 (lookup sh1eaddr (memory s0) beqAddr = Some (SHE sh1entry) /\
         lookup sh1eaddr (memory s) beqAddr = Some (SHE sh1entry1) /\
         sh1entry1 =
         {|
           PDchild := PDchild sh1entry0;
           PDflag := PDflag sh1entry0;
           inChildLocation := blockToShareChildEntryAddr
         |} /\
         sh1entry0 =
         {|
           PDchild := globalIdPDChild;
           PDflag := PDflag sh1entry;
           inChildLocation := inChildLocation sh1entry
         |} /\
         newBlockEntryAddr = blockToShareChildEntryAddr /\
         lookup newBlockEntryAddr (memory s0) beqAddr = Some (BE bentry) /\
         lookup newBlockEntryAddr (memory s) beqAddr = Some (BE bentry6) /\
         bentry6 =
         CBlockEntry (read bentry5) (write bentry5) e (present bentry5)
           (accessible bentry5) (blockindex bentry5) (blockrange bentry5) /\
         bentry5 =
         CBlockEntry (read bentry4) w (exec bentry4) (present bentry4)
           (accessible bentry4) (blockindex bentry4) (blockrange bentry4) /\
         bentry4 =
         CBlockEntry r (write bentry3) (exec bentry3) (present bentry3)
           (accessible bentry3) (blockindex bentry3) (blockrange bentry3) /\
         bentry3 =
         CBlockEntry (read bentry2) (write bentry2) (exec bentry2) true
           (accessible bentry2) (blockindex bentry2) (blockrange bentry2) /\
         bentry2 =
         CBlockEntry (read bentry1) (write bentry1) (exec bentry1) 
           (present bentry1) true (blockindex bentry1) (blockrange bentry1) /\
         bentry1 =
         CBlockEntry (read bentry0) (write bentry0) (exec bentry0) 
           (present bentry0) (accessible bentry0) (blockindex bentry0)
           (CBlock (startAddr (blockrange bentry0)) blockend) /\
         bentry0 =
         CBlockEntry (read bentry) (write bentry) (exec bentry) 
           (present bentry) (accessible bentry) (blockindex bentry)
           (CBlock blockstart (endAddr (blockrange bentry))) /\
         sceaddr = CPaddr (newBlockEntryAddr + scoffset) /\
         lookup globalIdPDChild (memory s0) beqAddr = Some (PDT pdentry) /\
         lookup globalIdPDChild (memory s) beqAddr = Some (PDT pdentry1) /\
         pdentry1 =
         {|
           structure := structure pdentry0;
           firstfreeslot := firstfreeslot pdentry0;
           nbfreeslots := predCurrentNbFreeSlots;
           nbprepare := nbprepare pdentry0;
           parent := parent pdentry0;
           MPU := MPU pdentry0;
           vidtBlock := vidtBlock pdentry0
         |} /\
         pdentry0 =
         {|
           structure := structure pdentry;
           firstfreeslot := newFirstFreeSlotAddr;
           nbfreeslots := ADT.nbfreeslots pdentry;
           nbprepare := nbprepare pdentry;
           parent := parent pdentry;
           MPU := MPU pdentry;
           vidtBlock := vidtBlock pdentry
         |} /\
         pdentryNbFreeSlots globalIdPDChild predCurrentNbFreeSlots s /\
         StateLib.Index.pred nbfreeslots = Some predCurrentNbFreeSlots /\
         blockindex bentry6 = blockindex bentry5 /\
         blockindex bentry5 = blockindex bentry4 /\
         blockindex bentry4 = blockindex bentry3 /\
         blockindex bentry3 = blockindex bentry2 /\
         blockindex bentry2 = blockindex bentry1 /\
         blockindex bentry1 = blockindex bentry0 /\
         blockindex bentry0 = blockindex bentry /\
         blockindex bentry6 = blockindex bentry /\
         isPDT globalIdPDChild s0 /\
         isPDT globalIdPDChild s /\
         isBE newBlockEntryAddr s0 /\
         isBE newBlockEntryAddr s /\
         isBE blockToShareInCurrPartAddr s0 /\
         isSCE sceaddr s0 /\
         isSCE sceaddr s /\
         isSHE sh1eaddr s0 /\
         isSHE sh1eaddr s /\
         sceaddr = CPaddr (newBlockEntryAddr + scoffset) /\
         sh1eaddr = sh1eaddr /\
         firstfreeslot pdentry1 = newFirstFreeSlotAddr /\
         newBlockEntryAddr = firstfreeslot pdentry /\
         newBlockEntryAddr <> blockToShareInCurrPartAddr /\
         newFirstFreeSlotAddr <> globalIdPDChild /\
         newFirstFreeSlotAddr <> newBlockEntryAddr
				/\ newFirstFreeSlotAddr <> sh1eaddr
				/\ globalIdPDChild <> newBlockEntryAddr
				/\ globalIdPDChild <> blockToShareInCurrPartAddr
				/\ sh1eaddr <> sceaddr
				/\ sh1eaddr <> newBlockEntryAddr
				/\ sh1eaddr <> globalIdPDChild
				/\ sh1eaddr <> blockToShareInCurrPartAddr
				/\ sceaddr <> newBlockEntryAddr
				/\ sceaddr <> globalIdPDChild
				/\ sceaddr <> newFirstFreeSlotAddr
				/\ sceaddr <> blockToShareInCurrPartAddr
				(* pdinsertion's new free slots list and relation with list at s0 *)
)

/\ (

 exists
           (optionfreeslotslist : list optionPaddr) (s2 : state) 
         (n0 n1 n2 : nat) (nbleft : index),
           (nbleft = CIndex (nbfreeslots - 1) /\
            nbleft < maxIdx /\
            s =
            {|
              currentPartition := currentPartition s0;
              memory :=
                add sh1eaddr
                  (SHE
                     {|
                       PDchild := PDchild sh1entry0;
                       PDflag := PDflag sh1entry0;
                       inChildLocation := blockToShareChildEntryAddr
                     |}) (memory s2) beqAddr
            |} /\
            optionfreeslotslist =
            getFreeSlotsListRec n1 newFirstFreeSlotAddr s2 nbleft /\
            getFreeSlotsListRec n2 newFirstFreeSlotAddr s nbleft =
            optionfreeslotslist /\
            optionfreeslotslist =
            getFreeSlotsListRec n0 newFirstFreeSlotAddr s0 nbleft /\
            n0 <= n1 /\
            nbleft < n0 /\
            n1 <= n2 /\
            nbleft < n2 /\
            n2 <= maxIdx + 1 /\
            (wellFormedFreeSlotsList optionfreeslotslist = False -> False) /\
            NoDup (filterOptionPaddr optionfreeslotslist) /\
            (In newBlockEntryAddr (filterOptionPaddr optionfreeslotslist) -> False)) /\
           (exists optionentrieslist : list optionPaddr,
              optionentrieslist = getKSEntries globalIdPDChild s2 /\
              getKSEntries globalIdPDChild s = optionentrieslist /\
              optionentrieslist = getKSEntries globalIdPDChild s0 /\
              In (SomePaddr newBlockEntryAddr) optionentrieslist)
) /\ (
 getPartitions multiplexer s = getPartitions multiplexer s0 /\
                 getChildren globalIdPDChild s = getChildren globalIdPDChild s0 /\
                 getConfigBlocks globalIdPDChild s =
                 getConfigBlocks globalIdPDChild s0 /\
                 getConfigPaddr globalIdPDChild s = getConfigPaddr globalIdPDChild s0 /\
                 (forall block : paddr,
                  In block (getMappedBlocks globalIdPDChild s) ->
                  In block (newBlockEntryAddr :: getMappedBlocks globalIdPDChild s0)) /\
                 (forall addr : paddr,
                  In addr (getMappedPaddr globalIdPDChild s) ->
                  In addr
                    (getAllPaddrBlock (startAddr (blockrange bentry6))
                       (endAddr (blockrange bentry6)) ++
                     getMappedPaddr globalIdPDChild s0))

) /\ (
 lookup blockToShareInCurrPartAddr (memory s) beqAddr =
         lookup blockToShareInCurrPartAddr (memory s0) beqAddr

) /\ (

 s1 =
      {|
        currentPartition := currentPartition s0;
        memory :=
          add globalIdPDChild
            (PDT
               {|
                 structure := structure pdentry;
                 firstfreeslot := newFirstFreeSlotAddr;
                 nbfreeslots := ADT.nbfreeslots pdentry;
                 nbprepare := nbprepare pdentry;
                 parent := parent pdentry;
                 MPU := MPU pdentry;
                 vidtBlock := vidtBlock pdentry
               |}) (memory s0) beqAddr
      |}

) /\ (
 s2 =
      {|
        currentPartition := currentPartition s1;
        memory :=
          add globalIdPDChild
            (PDT
               {|
                 structure := structure pdentry0;
                 firstfreeslot := firstfreeslot pdentry0;
                 nbfreeslots := predCurrentNbFreeSlots;
                 nbprepare := nbprepare pdentry0;
                 parent := parent pdentry0;
                 MPU := MPU pdentry0;
                 vidtBlock := vidtBlock pdentry0
               |}) (memory s1) beqAddr
      |}

) /\ (

s3 =
      {|
        currentPartition := currentPartition s2;
        memory :=
          add newBlockEntryAddr
            (BE
               (CBlockEntry (read bentry) (write bentry) 
                  (exec bentry) (present bentry) (accessible bentry)
                  (blockindex bentry)
                  (CBlock blockstart (endAddr (blockrange bentry))))) 
            (memory s2) beqAddr
      |}

) /\ (

s4 =
      {|
        currentPartition := currentPartition s3;
        memory :=
          add newBlockEntryAddr
            (BE
               (CBlockEntry (read bentry0) (write bentry0) 
                  (exec bentry0) (present bentry0) (accessible bentry0)
                  (blockindex bentry0)
                  (CBlock (startAddr (blockrange bentry0)) blockend))) 
            (memory s3) beqAddr
      |}

) /\ (


 s5 =
      {|
        currentPartition := currentPartition s4;
        memory :=
          add newBlockEntryAddr
            (BE
               (CBlockEntry (read bentry1) (write bentry1) 
                  (exec bentry1) (present bentry1) true (blockindex bentry1)
                  (blockrange bentry1))) (memory s4) beqAddr
      |}

) /\ (


 s6 =
      {|
        currentPartition := currentPartition s5;
        memory :=
          add newBlockEntryAddr
            (BE
               (CBlockEntry (read bentry2) (write bentry2) 
                  (exec bentry2) true (accessible bentry2) 
                  (blockindex bentry2) (blockrange bentry2))) 
            (memory s5) beqAddr
      |}

) /\ (


s7 =
      {|
        currentPartition := currentPartition s6;
        memory :=
          add newBlockEntryAddr
            (BE
               (CBlockEntry r (write bentry3) (exec bentry3) 
                  (present bentry3) (accessible bentry3) 
                  (blockindex bentry3) (blockrange bentry3))) 
            (memory s6) beqAddr
      |}

) /\ (


 s8 =
      {|
        currentPartition := currentPartition s7;
        memory :=
          add newBlockEntryAddr
            (BE
               (CBlockEntry (read bentry4) w (exec bentry4) 
                  (present bentry4) (accessible bentry4) 
                  (blockindex bentry4) (blockrange bentry4))) 
            (memory s7) beqAddr
      |}
) /\ (

s9 =
      {|
        currentPartition := currentPartition s8;
        memory :=
          add newBlockEntryAddr
            (BE
               (CBlockEntry (read bentry5) (write bentry5) e 
                  (present bentry5) (accessible bentry5) 
                  (blockindex bentry5) (blockrange bentry5))) 
            (memory s8) beqAddr
      |}

) /\ (

 s10 =
       {|
         currentPartition := currentPartition s9;
         memory :=
           add sceaddr (SCE {| origin := blockstart; next := next scentry |})
             (memory s9) beqAddr
       |}

) /\ (


 consistency s10 /\
          isPDT globalIdPDChild s10 /\
          isSCE sceaddr s10 /\
          isSHE sh1eaddr s10 /\
          isBE newBlockEntryAddr s10 /\
          lookup sh1eaddr (memory s10) beqAddr = lookup sh1eaddr (memory s0) beqAddr

) /\ (

blockToShareInCurrPartAddr <> nullAddr
) /\ (
 sh1eaddr = CPaddr (blockToShareInCurrPartAddr + sh1offset)
) /\ (
isBE blockToShareInCurrPartAddr s0
) /\ (
 lookup blockToShareInCurrPartAddr (memory s) beqAddr =
              lookup blockToShareInCurrPartAddr (memory s0) beqAddr
) /\ (
 isBE blockToShareInCurrPartAddr s
) /\ (
 lookup sh1eaddr (memory s) beqAddr = Some (SHE sh1entrybts)
) /\ (
 blockindex bentry6 = blockindex bentry
) /\ (
 isBE newBlockEntryAddr s0
) /\ (
isBE newBlockEntryAddr s
) /\ (
 lookup newBlockEntryAddr (memory s0) beqAddr = Some (BE bentry)
) /\ (
 lookup newBlockEntryAddr (memory s) beqAddr = Some (BE bentry6)
) /\ (
lookup globalIdPDChild (memory s0) beqAddr = Some (PDT pdentry)
) /\ (
lookup globalIdPDChild (memory s) beqAddr = Some (PDT pdentry1)
) /\ (
 isPDT globalIdPDChild s0
) /\ (
 isPDT globalIdPDChild s
) /\ (
 sceaddr = CPaddr (newBlockEntryAddr + scoffset)
) /\ (
 isSCE sceaddr s0
) /\ (
isSCE sceaddr s
) /\ (
 beqAddr globalIdPDChild newBlockEntryAddr = false
) /\ (
 beqAddr newBlockEntryAddr sceaddr = false
) /\ (
beqAddr sceaddr sh1eaddr = false
) /\ (
 beqAddr newBlockEntryAddr sh1eaddr = false
) /\ (
 beqAddr sh1eaddr blockToShareInCurrPartAddr = false
) /\ (
firstfreeslot pdentry1 = newFirstFreeSlotAddr
) /\ (
 newBlockEntryAddr = firstfreeslot pdentry
) /\ (
 nullAddrExists s
) /\ (
 s =
       {|
         currentPartition := currentPartition s10;
         memory :=
           add sh1eaddr
             (SHE
                {|
                  PDchild := PDchild sh1entry0;
                  PDflag := PDflag sh1entry0;
                  inChildLocation := blockToShareChildEntryAddr
                |})
             (add sh1eaddr
                (SHE
                   {|
                     PDchild := globalIdPDChild;
                     PDflag := PDflag sh1entry;
                     inChildLocation := inChildLocation sh1entry
                   |}) (memory s10) beqAddr) beqAddr
       |}
) /\ (
 isPDT globalIdPDChild s10
) /\ (
 isSCE sceaddr s10
) /\ (
 isSHE sh1eaddr s10
) /\ (
 isBE newBlockEntryAddr s10
) /\ (
 lookup sh1eaddr (memory s10) beqAddr =
            lookup sh1eaddr (memory s0) beqAddr
) /\ (
 lookup blockToShareInCurrPartAddr (memory s) beqAddr =
                       lookup blockToShareInCurrPartAddr (memory s10) beqAddr
) /\ (
 consistency s
) /\ (
 consistency2 s
) (*/\ (
verticalSharing s
)*)
-> 
kernelDataIsolation s.
Proof.
(*reconstuct hypotheses *)
intro hyps.
destruct hyps as
[HaddrIsNull (Hcheck & (HchildCurrPart & (HFull & (Haccessible & (Hpresent & (HslotIsNull & (beqBToShareVIDT & hyps)))))))].
destruct hyps as
[Hprops0 (Hs & (Hprops & (Hlists & (Hblockcurrpart & (HbtsEq & (Hs1 & (Hs2 & (Hs3 & (Hs4 & ( Hs5 & (Hs6
& (Hs7 & (Hs8 & (Hs9 & (Hs10 & (Hstates & (HbtsNotNull & (HSh1Offset & (HBEbtss0 & (Hlookupbtss & (HBEbts & (
HSHEs & (Hblockindex & (HBEs0 & (HBEs & (HlookupnewBs0 & (HlookupnewBs & (Hpdinsertions0 & (
Hpdinsertions & (HPDTs0 & (HPDTs & (HSceOffset & (HSCEs0 & (HSCEs & (beqpdnewB & (beqnewBsce & (
beqscesh1 & (beqnewBsh1 & (beqsh1bts & (HnewFirstFree & (HnewB & (HnullAddrExists & (HsEq &(
HPDTs10 & (HSCEs10 & (HSHEs10 & (HBEs10 & (HSHEs10Eq & (HlookupbtscurrpartEq & (Hcons & Hcons2) (*& Hvert)*) )))))))))))))))))))))))))))))))))))))))))))))))))].



	 (* kernelDataIsolation s*)
		unfold kernelDataIsolation.

		intros part1 part2 Hpart1PartTree Hpart2PartTree.

		assert(HKIs0: kernelDataIsolation s0) by intuition.
		unfold kernelDataIsolation in HKIs0.

		assert(HparentEq : getPartitions multiplexer s = getPartitions multiplexer s0)
			by admit.
		rewrite HparentEq in *.

		assert(Hidpdchildmapped : forall addr, 
		In addr (getMappedPaddr globalIdPDChild s) <->
		In addr
		(getAllPaddrBlock (startAddr (blockrange bentry6)) (endAddr (blockrange bentry6))
				++ getMappedPaddr globalIdPDChild s0)) by admit. (* constructed along the way *)

assert(Hidpdchildconfig : getConfigBlocks globalIdPDChild s = getConfigBlocks globalIdPDChild s0).
{
	admit.
}

assert(Hidpdchildconfigaddr : getConfigPaddr globalIdPDChild s = getConfigPaddr globalIdPDChild s0).
{
	admit.
}

assert(Hidpdchildmappedblocks : forall block,
In block (
getMappedBlocks globalIdPDChild s) <->
In block (
newBlockEntryAddr::getMappedBlocks globalIdPDChild s0) /\ NoDup(newBlockEntryAddr::getMappedBlocks globalIdPDChild s0)
/\ NoDup (getMappedBlocks globalIdPDChild s)).
{
	admit. (* constructed along the way*)
}

destruct (beqAddr part1 globalIdPDChild) eqn:beqpart1pd ; try(exfalso ; congruence).
	- (* part1 = globalIdPDChild *)
			rewrite <- DependentTypeLemmas.beqAddrTrue in beqpart1pd.
			rewrite beqpart1pd in *.
			destruct (beqAddr part2 globalIdPDChild) eqn:beqpart2pd ; try(exfalso ; congruence).
			-- (* part2 = globalIdPDChild *)
					rewrite <- DependentTypeLemmas.beqAddrTrue in beqpart2pd.
					rewrite beqpart2pd in *.

					(* addr is (because of NoDup) either in the initial list -> leads to s0
											either in newB -> then it must belong also to the
												accessible list at s0 which is false -> contradiction *)

				(* we use the faculty that the property holds for whatever partition couple
							so it's also true for globalIdPDChild's parent (the currentPart) and
								globalIdPDChild, e.g. whatever address in the parent is disjoint
									from the configPaddr of globalIdPDChild.
						Since the property was true at s0, and all addresses in globalIdPDChild
							are contained in currentPart, then the property is still true.
					 since :
							(getAllPaddrAux [blockToShareInCurrPartAddr] s0) = (getAllPaddrAux [newB] s0) ->
								Lib.disjoint (getAccessibleMappedPaddr parent s0) (getConfigPaddr part2 s0) ->
								In addr ((getAllPaddrBlock (startAddr (blockrange bentry6))
										              (endAddr (blockrange bentry6))) ->
								~ In addr (getConfigPaddr part2 s0).

*)

					specialize (HKIs0 globalIdPDChild globalIdPDChild Hpart1PartTree Hpart2PartTree).

					(*assert(HNoDupUseds : noDupUsedPaddrList s) by admit.
					unfold noDupUsedPaddrList in *.
					specialize (HNoDupUseds globalIdPDChild HPDTs).
					apply Lib.NoDupSplit in HNoDupUseds.
					destruct HNoDupUseds as [HNoDupConfigs HNoDupMappeds].

					assert(HNoDupUseds0 : noDupUsedPaddrList s0) by admit.
					unfold noDupUsedPaddrList in *.
					specialize (HNoDupUseds0 globalIdPDChild HPDTs0).
					apply Lib.NoDupSplit in HNoDupUseds0.
					destruct HNoDupUseds0 as [HNoDupConfigs0 HNoDupMappeds0].*)

					rewrite Hidpdchildconfigaddr in *.
					unfold Lib.disjoint in *.
					intros addr HaccessiblePaddr.

					assert(HMappedPaddrEq : In addr (getAccessibleMappedPaddr globalIdPDChild s) ->
									In addr (getAllPaddrBlock (startAddr (blockrange bentry6))
                                      (endAddr (blockrange bentry6)) ++
											(getAccessibleMappedPaddr globalIdPDChild s0))).
					{
						admit. (* constructed along the way *)
					}
					(*assert(HNoDupPaddrNoDupAccessibleMapped :
							NoDup (getAllPaddrBlock (startAddr (blockrange bentry6))
                      (endAddr (blockrange bentry6)) ++
                    getAccessibleMappedPaddr globalIdPDChild s0)) by admit. (* constructed along the way *)*)
					specialize (HMappedPaddrEq HaccessiblePaddr).
					apply in_app_or in HMappedPaddrEq.
					(*apply Lib.NoDupSplitInclIff in HNoDupPaddrNoDupAccessibleMapped.*)
					assert(HKIparentglobals0 : kernelDataIsolation s0) by intuition.
					assert(HcurrPartPartitionTree : In currentPart (getPartitions multiplexer s0))
							by admit. (* consistency ? and equal to value at s0*)
					specialize (HKIparentglobals0 currentPart globalIdPDChild
							 HcurrPartPartitionTree Hpart1PartTree).
					assert(HaddrInAccessibleParent : In addr (getAccessibleMappedPaddr currentPart s0)).
					{
								assert(blockInclLemma : forall block addr partition,
								In block (getMappedBlocks partition s0) -> (* by block found *)
								In addr (getAllPaddrAux [block] s0) ->
								In addr (getAccessibleMappedPaddr partition s0)) by admit.
								assert(HblockInMappedParent : In blockToShareInCurrPartAddr (getMappedBlocks currentPart s0))
									by admit. (* block found *)
								assert(HaddrInBTS : In addr (getAllPaddrAux [blockToShareInCurrPartAddr] s0))
										by admit.
								specialize (blockInclLemma blockToShareInCurrPartAddr addr currentPart
										HblockInMappedParent HaddrInBTS).
								assumption.
					}
					specialize (HKIparentglobals0 addr HaddrInAccessibleParent).
					assumption.


					(*destruct HMappedPaddrEq as [HaddrInnewB | HaddrIns0].
					(*destruct (HNoDupPaddrNoDupAccessibleMapped) as [HNoDup Hdisjoint].*)
					unfold Lib.disjoint in *.
					specialize (Hdisjoint addr HaddrInnewB).
					assert(HnewBNotInConfigPaddr : Lib.disjoint (getAllPaddrBlock (startAddr (blockrange bentry6))
              (endAddr (blockrange bentry6))) (getConfigPaddr globalIdPDChild s0)).
					{
						admit. (* constructed along the way *)
					}
					unfold Lib.disjoint in *. specialize (HnewBNotInConfigPaddr addr HaddrInnewB).
					intuition.

 					specialize (HKIs0 addr).
					apply HKIs0. intuition.*)

					(*unfold getAccessibleMappedPaddr in *.
					(*unfold getMappedPaddr in *.*)
					unfold getAccessibleMappedBlocks in *.
					unfold isPDT in HPDTs.
					destruct (lookup globalIdPDChild (memory s) beqAddr) eqn:Hlookupglobals ; try(exfalso ; congruence).
					destruct v ; try(exfalso ; congruence).
					unfold isPDT in HPDTs0.
					destruct (lookup globalIdPDChild (memory s0) beqAddr) eqn:Hlookupglobals0 ; try(exfalso ; congruence).
					destruct v ; try(exfalso ; congruence).


					assert(HNoDupListNoDupAccessibleLemma : NoDup (getAllPaddrAux (filterAccessible (getMappedBlocks globalIdPDChild s) s) s)).
					{
						apply NoDupPaddrListNoDupPaddrFilterAccessible ;
							intuition.
					}

					assert(HNoDupListNoDupAccessibleLemmas0 : NoDup (getAllPaddrAux (filterAccessible (getMappedBlocks globalIdPDChild s0) s0) s0)).
					{
						apply NoDupPaddrListNoDupPaddrFilterAccessible  ;
							intuition.
					}


					unfold Lib.disjoint in *.
					intros addr HaccessibleBlocks. specialize (HKIs0 addr).
					apply HKIs0. unfold isPDT in HPDTs0.

					assert(In addr
                      (getAllPaddrAux
                         (filterAccessible (getMappedBlocks globalIdPDChild s) s) s) ->
In addr
                      (getAllPaddrAux
                         (filterAccessible (getMappedBlocks globalIdPDChild s) s) s)


					assert(HInPaddrAccessibleListInPaddrListLemma : In addr
                      (getAllPaddrAux
                         (filterAccessible (getMappedBlocks globalIdPDChild s) s) s) ->
								In addr
                      (getAllPaddrAux (getMappedBlocks globalIdPDChild s) s)).
					{
						eapply NotInPaddrListNotInPaddrFilterAccessibleContra ; intuition.
					}
					specialize (HInPaddrAccessibleListInPaddrListLemma HaccessibleBlocks).


					assert(HInPaddrAccessibleListInPaddrListLemmas0 : In addr
                      (getAllPaddrAux
                         (filterAccessible (getMappedBlocks globalIdPDChild s0) s0) s0) ->
								In addr
                      (getAllPaddrAux (getMappedBlocks globalIdPDChild s0) s0)).
					{
						eapply NotInPaddrListNotInPaddrFilterAccessibleContra ; intuition.
					}

					specialize (Hidpdchildmapped addr).
					destruct Hidpdchildmapped as [Hidpdchildmapped HidpdchildmappedR].
					specialize (Hidpdchildmapped HInPaddrAccessibleListInPaddrListLemma).
					(*apply in_app_iff in Hidpdchildmapped.*)
					(*clear HInPaddrAccessibleListInPaddrListLemmas0.*)
					assert(HnewBNotInListAts0 : ~In newBlockEntryAddr (getMappedBlocks globalIdPDChild s0)).
					{
						admit. (*aldready done elsewhere*)
					}


assert(HAccessibleTrue : accessible bentry6 = true).
							{		clear Hprops0.

									assert(Hbentry6 : bentry6 =
      CBlockEntry (read bentry5) (write bentry5) e (present bentry5)
        (accessible bentry5) (blockindex bentry5) (blockrange bentry5)) by intuition.
									assert(Hbentry5 : bentry5 =
      CBlockEntry (read bentry4) w (exec bentry4) (present bentry4)
        (accessible bentry4) (blockindex bentry4) (blockrange bentry4)) by intuition.
									assert(Hbentry4 : bentry4 =
      CBlockEntry r (write bentry3) (exec bentry3) (present bentry3)
        (accessible bentry3) (blockindex bentry3) (blockrange bentry3)) by intuition.
									assert(Hbentry3 : bentry3 =
      CBlockEntry (read bentry2) (write bentry2) (exec bentry2) true
        (accessible bentry2) (blockindex bentry2) (blockrange bentry2)) by intuition.
									assert(Hbentry2 : bentry2 =
      CBlockEntry (read bentry1) (write bentry1) (exec bentry1) 
        (present bentry1) true (blockindex bentry1) (blockrange bentry1)) by intuition.
									assert(Haccs6Eq : accessible bentry6 = accessible bentry5).
									{
											subst bentry6. unfold CBlockEntry.
											destruct (lt_dec (blockindex bentry5) kernelStructureEntriesNb) ; intuition.
											destruct blockentry_d. destruct bentry5.
											intuition.
									}
									assert(Haccs5Eq : accessible bentry5 = accessible bentry4).
									{
											rewrite Hbentry5. unfold CBlockEntry.
											destruct (lt_dec (blockindex bentry4) kernelStructureEntriesNb) ; intuition.
											destruct blockentry_d. destruct bentry4.
											intuition.
									}
									assert(Haccs4Eq : accessible bentry4 = accessible bentry3).
									{
											rewrite Hbentry4. unfold CBlockEntry.
											destruct (lt_dec (blockindex bentry3) kernelStructureEntriesNb) ; intuition.
											destruct blockentry_d. destruct bentry3.
											intuition.
									}

									assert(Haccs3Eq : accessible bentry3 = accessible bentry2).
									{
											rewrite Hbentry3. unfold CBlockEntry.
											destruct (lt_dec (blockindex bentry2) kernelStructureEntriesNb) ; intuition.
											destruct blockentry_d. destruct bentry2.
											intuition.
									}
									assert(Haccs2Eq : accessible bentry2 = true).
									{		rewrite Hbentry2. simpl.
											unfold CBlockEntry.
											destruct (lt_dec (blockindex bentry1) kernelStructureEntriesNb) ; intuition.
											destruct blockentry_d. destruct bentry1.
											intuition.
									}
									rewrite Haccs6Eq. rewrite Haccs5Eq. rewrite Haccs4Eq. rewrite Haccs3Eq.
									rewrite Haccs2Eq. trivial.
							}

					simpl in *. rewrite HlookupnewBs in *.



					assert(HfilterAccessibleListEq : (filterAccessible (getMappedBlocks globalIdPDChild s) s) =
									newBlockEntryAddr ::(filterAccessible (getMappedBlocks globalIdPDChild s0) s0)).
					{
						(*induction (getMappedBlocks globalIdPDChild s).
						- intuition.
						- simpl in *.
							destruct (beqAddr a newBlockEntryAddr) eqn:beqanewB.
							-- (* a = newB *)
									rewrite <- DependentTypeLemmas.beqAddrTrue in beqanewB.
									subst a. specialize (Hidpdchildmappedblocks newBlockEntryAddr).
									rewrite HlookupnewBs in *.
									rewrite HAccessibleTrue in *.
									f_equal.
									induction (getMappedBlocks globalIdPDChild s0).
									--- intuition.

									destruct Hidpdchildmappedblocks.
									simpl in *. intuition. rewrite HlookupnewBs in *.
									admit.
									apply NoDup_cons_iff in H100.
									apply NoDup_cons_iff in H94.
									intuition.
							-- (* a <> newB *)
									rewrite beqAddrFalse in *.
									assert(HlookupaEq : lookup a (memory s) beqAddr = lookup a (memory s0) beqAddr )
											by admit.
									rewrite HlookupaEq in *.
									destruct (lookup a (memory s0) beqAddr) eqn:Hlookupas0 ; intuition.
									destruct ( *)
							admit.
					}
					rewrite HfilterAccessibleListEq in *.


					assert(HPaddrAccessibleListEq : (getAllPaddrAux ([newBlockEntryAddr] ++(filterAccessible (getMappedBlocks globalIdPDChild s0) s0)) s) =
											getAllPaddrBlock (startAddr (blockrange bentry6))
                                      (endAddr (blockrange bentry6)) ++(getAllPaddrAux (filterAccessible (getMappedBlocks globalIdPDChild s0) s0)s)).
					{
						simpl. rewrite HlookupnewBs in *. f_equal.
					}
					rewrite HPaddrAccessibleListEq in *.

					induction (getMappedBlocks globalIdPDChild s).
					* intuition.
					* simpl in *.
						destruct (beqAddr a newBlockEntryAddr) eqn:beqa1block.
						** (* a = block *)
							rewrite <- DependentTypeLemmas.beqAddrTrue in beqa1block.
							rewrite beqa1block in *. subst a.
							rewrite HlookupnewBs in *.
							specialize (Hidpdchildmappedblocks newBlockEntryAddr).
							destruct Hidpdchildmappedblocks as [Hidpdchildmappedblocks HidpdchildmappedblocksR].
							
							rewrite HAccessibleTrue in *.
							simpl in *.
							(*rewrite HlookupnewBs in *.*)
							destruct HidpdchildmappedblocksR ; intuition.
							induction (getMappedBlocks globalIdPDChild s0).
							*** simpl in *. intuition.


							apply Lib.NoDupSplitInclIff in HNoDupListNoDupAccessibleLemma.
							apply Lib.NoDupSplitInclIff in HNoDupMappeds.
							assert(HfilterEq : getAllPaddrAux l s = getAllPaddrAux l s0).
							{
									(*induction l.
									- intuition.
									-*)
									admit.
							}
							rewrite HfilterEq in *.

							apply in_app_or in Hidpdchildmapped.
							destruct Hidpdchildmapped as [HAddrInNewB | HaddrIns0].
							*** (* addr in NewB *)
									admit.
							*** (* addr in s0 *)
									apply in_app_or in HInPaddrAccessibleListInPaddrListLemma.
									apply IHl ; intuition.
							assert(HNoDupAllPaddr : 
 ; intuition.

						** (* a <> block -> lookup s = lookup s0*)

						-
						destruct (lookup a1 (memory s) beqAddr) eqn:Hlookupa1s ; intuition.
						destruct v ; intuition.
						destruct (accessible blockentry).
						apply H32 ; intuition.
						intuition.


					destruct Hidpdchildmappedblocks as [Hidpdchildmappedblocks HidpdchildmappedblocksR].
*)

	-- (* part2 <> globalIdPDChild *)
		
assert(Hconfigchild2Eq : getConfigPaddr part2 s = getConfigPaddr part2 s0)
	by admit.
rewrite Hconfigchild2Eq in *.

assert(Hidpart2configaddr : getConfigPaddr part2 s = getConfigPaddr part2 s0).
{
	admit.
}
(*DUP of previous *)
(* split case addr in [newB] or address in initial (getAccessibleMappedPaddr globalIdPDChild s)*)

(* specialize for parent partition (currentPart) where newB's addresses were disjoint
		from configPaddr of part2. As all addresses of globalidPDchild
			are included in the parent partition, they are disjoint *)

					specialize (HKIs0 globalIdPDChild part2 Hpart1PartTree Hpart2PartTree).

					rewrite Hidpart2configaddr in *.
					unfold Lib.disjoint in *.
					intros addr HaccessiblePaddr.

					assert(HMappedPaddrEq : In addr (getAccessibleMappedPaddr globalIdPDChild s) ->
									In addr (getAllPaddrBlock (startAddr (blockrange bentry6))
                                      (endAddr (blockrange bentry6)) ++
											(getAccessibleMappedPaddr globalIdPDChild s0))).
					{
						admit. (* constructed along the way *)
					}
					specialize (HMappedPaddrEq HaccessiblePaddr).
					apply in_app_or in HMappedPaddrEq.
					assert(HKIparentglobals0 : kernelDataIsolation s0) by intuition.
					assert(HcurrPartPartitionTree : In currentPart (getPartitions multiplexer s0))
							by admit. (* consistency ? and equal to value at s0*)
					specialize (HKIparentglobals0 currentPart part2
							 HcurrPartPartitionTree Hpart2PartTree).
					assert(HaddrInAccessibleParent : In addr (getAccessibleMappedPaddr currentPart s0)).
					{
								assert(blockInclLemma : forall block addr partition,
								In block (getMappedBlocks partition s0) -> (* by block found *)
								In addr (getAllPaddrAux [block] s0) ->
								In addr (getAccessibleMappedPaddr partition s0)) by admit.
								assert(HblockInMappedParent : In blockToShareInCurrPartAddr (getMappedBlocks currentPart s0))
									by admit. (* block found *)
								assert(HaddrInBTS : In addr (getAllPaddrAux [blockToShareInCurrPartAddr] s0))
										by admit.
								specialize (blockInclLemma blockToShareInCurrPartAddr addr currentPart
										HblockInMappedParent HaddrInBTS).
								assumption.
					}
					specialize (HKIparentglobals0 addr HaddrInAccessibleParent).
					assumption.

	- (* part1 <> globalIdPDChild *)

assert(Haccessible1Eq : getAccessibleMappedPaddr part1 s = getAccessibleMappedPaddr part1 s0)
	by admit.
rewrite Haccessible1Eq in *.

		destruct (beqAddr part2 globalIdPDChild) eqn:beqpart2pd ; try(exfalso ; congruence).
		-- (* part2 = globalIdPDChild *)
				rewrite <- DependentTypeLemmas.beqAddrTrue in beqpart2pd.
				rewrite beqpart2pd in *.

				rewrite Hidpdchildconfigaddr in *.

				specialize (HKIs0 part1 globalIdPDChild Hpart1PartTree Hpart2PartTree).
				intuition.

		-- (* part2 <> globalIdPDChild *)

assert(Hconfig2Eq : getConfigPaddr part2 s = getConfigPaddr part2 s0)
	by admit.
rewrite Hconfig2Eq in *.

				specialize (HKIs0 part1 part2 Hpart1PartTree Hpart2PartTree).
				intuition.

Admitted.