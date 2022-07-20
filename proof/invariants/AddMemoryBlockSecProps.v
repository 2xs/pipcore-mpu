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
(*  software by the user in light of its specific status of free software,      *)
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

Definition AddMemoryBlockPropagatedProperties
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
PDChildAddr
pdchildIsNull
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
Hoptionlists
olds
n0 n1 n2
nbleft
s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12
s
 :=

addrIsNull = false /\
negb rcheck = false /\
negb isChildCurrPart = false /\
isFull = false /\
negb addrIsAccessible = false /\
negb addrIsPresent = false /\
negb pdchildIsNull = false /\
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
              blockToShareInCurrPartAddr = idBlockToShare /\
              bentryPFlag blockToShareInCurrPartAddr true s0)) /\
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
          (exists (sh1entry : Sh1Entry) (sh1entryaddr : paddr),
             lookup sh1entryaddr (memory s0) beqAddr = Some (SHE sh1entry) /\
             sh1entryPDchild sh1entryaddr PDChildAddr s0 /\
             sh1entryAddr blockToShareInCurrPartAddr sh1entryaddr s0) /\
          beqAddr nullAddr PDChildAddr = pdchildIsNull /\
          pdentryVidt globalIdPDChild vidtBlockGlobalId s0 /\
          bentryStartAddr blockToShareInCurrPartAddr blockstart s0 /\
          bentryEndAddr blockToShareInCurrPartAddr blockend s0
)
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
							(nbleft = CIndex (nbfreeslots - 1) /\ nbleft < maxIdx) /\
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
                       |}) (memory olds) beqAddr
              |} /\
              (Hoptionlists = getFreeSlotsListRec n1 newFirstFreeSlotAddr olds nbleft /\
               getFreeSlotsListRec n2 newFirstFreeSlotAddr s nbleft = Hoptionlists /\
               Hoptionlists = getFreeSlotsListRec n0 newFirstFreeSlotAddr s0 nbleft /\
               n0 <= n1 /\
               nbleft < n0 /\
               n1 <= n2 /\
               nbleft < n2 /\
               n2 <= maxIdx + 1 /\
               (wellFormedFreeSlotsList Hoptionlists = False -> False) /\
               NoDup (filterOptionPaddr Hoptionlists) /\
               (In newBlockEntryAddr (filterOptionPaddr Hoptionlists) -> False) /\
               (exists optionentrieslist : list optionPaddr,
                  optionentrieslist = getKSEntries globalIdPDChild olds /\
                  getKSEntries globalIdPDChild s = optionentrieslist /\
                  optionentrieslist = getKSEntries globalIdPDChild s0 /\
                  In (SomePaddr newBlockEntryAddr) optionentrieslist)) /\
             ( isPDT multiplexer s /\
		            (*getPartitions multiplexer olds = getPartitions multiplexer s0 /\
		            getPartitions multiplexer s = getPartitions multiplexer olds /\
		            getChildren globalIdPDChild olds = getChildren globalIdPDChild s0 /\
		            getChildren globalIdPDChild s = getChildren globalIdPDChild olds /\
		            getConfigBlocks globalIdPDChild olds =
		            getConfigBlocks globalIdPDChild s0 /\
		            getConfigBlocks globalIdPDChild s =
		            getConfigBlocks globalIdPDChild olds /\
		            getConfigPaddr globalIdPDChild olds = getConfigPaddr globalIdPDChild s0 /\
		            getConfigPaddr globalIdPDChild s = getConfigPaddr globalIdPDChild olds /\
		            (forall block : paddr,
		             In block (getMappedBlocks globalIdPDChild olds) <->
		             In block (newBlockEntryAddr :: getMappedBlocks globalIdPDChild s0)) /\
		            (forall block : paddr,
		             In block (getMappedBlocks globalIdPDChild s) <->
		             In block (newBlockEntryAddr :: getMappedBlocks globalIdPDChild s0)) /\
		            (forall addr : paddr,
		             In addr (getMappedPaddr globalIdPDChild olds) <->
		             In addr
		               (getAllPaddrBlock (startAddr (blockrange bentry6))
		                  (endAddr (blockrange bentry6)) ++
		                getMappedPaddr globalIdPDChild s0)) /\
		            (forall addr : paddr,
		             In addr (getMappedPaddr globalIdPDChild s) <->
		             In addr
		               (getAllPaddrBlock (startAddr (blockrange bentry6))
		                  (endAddr (blockrange bentry6)) ++
		                getMappedPaddr globalIdPDChild s0))*)
		            getPartitions multiplexer s = getPartitions multiplexer s0 /\
		            getChildren globalIdPDChild s = getChildren globalIdPDChild s0 /\
		            getConfigBlocks globalIdPDChild s = getConfigBlocks globalIdPDChild s0 /\
		            getConfigPaddr globalIdPDChild s = getConfigPaddr globalIdPDChild s0 /\
		            (forall block : paddr,
		             In block (getMappedBlocks globalIdPDChild s) <->
		             In block (newBlockEntryAddr :: getMappedBlocks globalIdPDChild s0)) /\
		            (forall addr : paddr,
		             In addr (getMappedPaddr globalIdPDChild s) <->
		             In addr
		               (getAllPaddrBlock (startAddr (blockrange bentry6))
		                  (endAddr (blockrange bentry6)) ++
		                getMappedPaddr globalIdPDChild s0)) /\
								In blockToShareInCurrPartAddr (getMappedBlocks currentPart s0) /\
							(forall addr : paddr, In addr (getAllPaddrBlock
						(startAddr (blockrange bentry6)) (endAddr (blockrange bentry6))) <->
														In addr (getAllPaddrAux [blockToShareInCurrPartAddr] s0)) /\
							In globalIdPDChild (getChildren currentPart s0) /\
							In globalIdPDChild (getPartitions multiplexer s0) /\
						NoDup (getAllPaddrBlock (startAddr (blockrange bentry6))
                    (endAddr (blockrange bentry6)) ++
                  getMappedPaddr globalIdPDChild s0)
							)
		)
/\ (
 lookup blockToShareInCurrPartAddr (memory s) beqAddr =
         lookup blockToShareInCurrPartAddr (memory s0) beqAddr

) /\ (
			sh1entryPDchild sh1eaddr nullAddr s0 /\
			sh1entryPDflag sh1eaddr false s0
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
s11 = {|
		   currentPartition := currentPartition s10;
		   memory := add sh1eaddr
                (SHE
                   {|
                     PDchild := globalIdPDChild;
                     PDflag := PDflag sh1entry;
                     inChildLocation := inChildLocation sh1entry
                   |}) (memory s10) beqAddr |}
)	/\ (
s12 = {|
		   currentPartition := currentPartition s11;
		   memory := add sh1eaddr
             (SHE
                {|
                  PDchild := PDchild sh1entry0;
                  PDflag := PDflag sh1entry0;
                  inChildLocation := blockToShareChildEntryAddr
                |}) (memory s11) beqAddr |}
) /\ (

s = s12

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
)
/\ (
		(endAddr (blockrange bentry6) = blockend) /\
		(startAddr (blockrange bentry6) = blockstart) /\
		(forall addr : paddr,
				In addr (getAccessibleMappedPaddr globalIdPDChild s) ->
					In addr ((getAllPaddrBlock (startAddr (blockrange bentry6))
                              (endAddr (blockrange bentry6))) ++
							(getAccessibleMappedPaddr globalIdPDChild s0)))
		)
/\ (
				 	(
							forall partition : paddr,
								partition <> globalIdPDChild ->
								isPDT partition s0 ->
								 getMappedPaddr partition s = getMappedPaddr partition s0
					) /\
					(
							forall partition : paddr,
							partition <> globalIdPDChild ->
							isPDT partition s0 ->
							getConfigPaddr partition s = getConfigPaddr partition s0

					) /\
					(
							forall partition : paddr,
							partition <> globalIdPDChild ->
							isPDT partition s0 ->
							getUsedPaddr partition s = getUsedPaddr partition s0
					) /\
					(

							forall partition : paddr,
							partition <> globalIdPDChild ->
							isPDT partition s0 ->
							getChildren partition s = getChildren partition s0
					) /\
					(
							forall partition : paddr,
							partition <> globalIdPDChild ->
							isPDT partition s0 ->
							(getMappedBlocks partition s) = getMappedBlocks partition s0
					) /\
					(
							forall partition : paddr,
							partition <> globalIdPDChild ->
							isPDT partition s0 ->
							(getAccessibleMappedPaddr partition s) = getAccessibleMappedPaddr partition s0
					)
	)
.

Lemma AddMemoryBlockVS
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
PDChildAddr
pdchildIsNull
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
Hoptionlists olds n0 n1 n2 nbleft 
s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12
s :

AddMemoryBlockPropagatedProperties
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
PDChildAddr
pdchildIsNull
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
Hoptionlists olds n0 n1 n2 nbleft
s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12
s
->
verticalSharing s.
Proof.
(*reconstuct hypotheses *)
intro hyps. unfold AddMemoryBlockPropagatedProperties in *.
destruct hyps as
[HaddrIsNull (Hcheck & (HchildCurrPart & (HFull & (Haccessible & (Hpresent &(HpdchildNull & (HslotIsNull & (beqBToShareVIDT & hyps))))))))].
destruct hyps as
[Hprops0 (Hs & (Hprops & ((Hnbleft & (Hs2Eq & Hlists)) & (HbtsEq & (Hpdchildflags0 & (Hs1 & (Hs2 & (Hs3 & (Hs4 & ( Hs5 & (Hs6
& (Hs7 & (Hs8 & (Hs9 & (Hs10 & (Hs11 & (Hs12 & (Hs12Eq & (HbtsNotNull & (HSh1Offset & (HBEbtss0 & (Hlookupbtss & (HBEbts & (
HSHEs & (Hblockindex & (HBEs0 & (HBEs & (HlookupnewBs0 & (HlookupnewBs & (Hpdinsertions0 & (
Hpdinsertions & (HPDTs0 & (HPDTs & (HSceOffset & (HSCEs0 & (HSCEs & (beqpdnewB & (beqnewBsce & (
beqscesh1 & (beqnewBsh1 & (beqsh1bts & (HnewFirstFree & (HnewB & (HnullAddrExists & (HsEq &(
HPDTs10 & (HSCEs10 & (HSHEs10 & (HBEs10 & (HSHEs10Eq & (HlookupbtscurrpartEq & (Hcons & (Hcons2 & (HstartendbtsEq & (
HMappedPaddrEqNotInParts0 & (HConfigPaddrEqNotInParts0 & (HUsedPaddrEqNotInParts0 & (
HChildrenEqNotInParts0 & (HMappedBlocksEqNotInParts0 & HAccessibleMappedPaddrEqNotInParts0))))))))) (*& Hvert)*) ))))))))))))))))))))))))))))))))))))))))))))))))))].

{ (* verticalSharing s*)
		unfold verticalSharing.

		assert(HcurrPartEq : currentPart = currentPartition s0) by intuition.

		intros parent child HparentPartTree HchildIsChild addr HnAddrInUsedChild.

		assert(HVs0: verticalSharing s0) by intuition.
		unfold verticalSharing in HVs0.

		assert(HparentEq : getPartitions multiplexer s = getPartitions multiplexer s0)
			by intuition. (* constructed along the way *)
		rewrite HparentEq in *.

		assert(HpdchildrenEq : getChildren globalIdPDChild s = getChildren globalIdPDChild s0)
			by intuition. (* constructed along the way *)

		assert(Hidpdchildmapped : forall addr, 
			In addr (getMappedPaddr globalIdPDChild s) <->
			In addr
			(getAllPaddrBlock (startAddr (blockrange bentry6)) (endAddr (blockrange bentry6))
					++ getMappedPaddr globalIdPDChild s0))
			by intuition. (* constructed along the way *)

		assert(Hidpdchildconfig : getConfigBlocks globalIdPDChild s = getConfigBlocks globalIdPDChild s0)
			by intuition. (* constructed along the way *)

		assert(Hidpdchildconfigaddr : getConfigPaddr globalIdPDChild s = getConfigPaddr globalIdPDChild s0)
			by intuition. (* constructed along the way *)

		destruct (beqAddr child globalIdPDChild) eqn:beqchildpd ; try(exfalso ; congruence).
		- (* child = globalIdPDChild *)
				rewrite <- DependentTypeLemmas.beqAddrTrue in beqchildpd.
				rewrite beqchildpd in *.

				assert(HparentidpdNotEq : parent <> globalIdPDChild). (* child not currentPart *)
				{
					intro Hf. subst globalIdPDChild. subst child.
					assert(HNoDupPartitionTree : noDupPartitionTree s0)
						by (unfold consistency in * ; unfold consistency1 in * ; intuition).
					unfold noDupPartitionTree in *.
					specialize (HNoDupPartitionTree parent).
					contradict HNoDupPartitionTree.
					unfold getPartitions. simpl.
					unfold PDTFilter.
					apply isPDTLookupEq in HPDTs0. destruct HPDTs0 as [pdcurrparts0 Hlookuppdcurrs0].
					rewrite Hlookuppdcurrs0 in *.
					assert(Hnext : maxAddr+1 = S maxAddr).
					{ lia. }
					rewrite Hnext. simpl.
					unfold PDTFilter. rewrite Hlookuppdcurrs0 in *.
					intro Hf.
					apply NoDup_cons_iff in Hf. intuition.
				}

				assert(HPDTparents0 : isPDT parent s0)
						by (apply partitionsArePDT with multiplexer ; intuition).
				assert(HchildrenparentEq : getChildren parent s = getChildren parent s0).
				{ apply HChildrenEqNotInParts0 ; intuition. }
				rewrite HchildrenparentEq in *.

				assert(Hparent : parent = currentPart).
				{	
					assert(HisParents0 : isParent s0) 
						by (unfold consistency in * ; unfold consistency1 in * ; intuition). (* consistency *)
					assert(HisChilds0 : isChild s0) 
						by (unfold consistency in * ; unfold consistency1 in * ; intuition). (* consistency *)
					assert(In currentPart (getPartitions multiplexer s0)) 
						by (rewrite HcurrPartEq in * ; unfold consistency in * ; unfold consistency1 in * ; intuition). (* consistency s0*)
					apply uniqueParent with globalIdPDChild s0; intuition.
				}
				subst parent.

				assert(HmappedparentEq : getMappedPaddr currentPart s = getMappedPaddr currentPart s0).
				{
					eapply HMappedPaddrEqNotInParts0 ; intuition.
				}
				rewrite HmappedparentEq in *.

				specialize (HVs0 currentPart globalIdPDChild HparentPartTree HchildIsChild).
				unfold getUsedPaddr in HnAddrInUsedChild.
				specialize (HVs0 addr).
				unfold getUsedPaddr in HVs0.
				rewrite Hidpdchildconfigaddr in *.

				apply in_app_or in HnAddrInUsedChild.

				destruct HnAddrInUsedChild as [HnAddrInUsedChild | HnAddrInUsedChild].
				(* Case getConfigPaddr s0 *)
				apply HVs0. apply in_app_iff. left. assumption.

				specialize (Hidpdchildmapped addr).
				destruct Hidpdchildmapped as [Hidpdchildmapped HidpdchildmappedR].
				specialize(Hidpdchildmapped HnAddrInUsedChild).
				apply in_app_or in Hidpdchildmapped.
				destruct Hidpdchildmapped as [Hidpdchildmapped | Hidpdchildmapped].
				(* Case (getAllPaddrBlock (startAddr (blockrange bentry6))
							                (endAddr (blockrange bentry6))) *)

				(* prove newB's addresses are included in the parent *)
				(* DUP from main *)
				assert(HaddrInParentBlock : In addr (getAllPaddrAux [blockToShareInCurrPartAddr] s0)).
				{
						assert(HaddrInBTS : (forall addr : paddr,
				      In addr
				        (getAllPaddrBlock (startAddr (blockrange bentry6))
				           (endAddr (blockrange bentry6))) <->
				      In addr (getAllPaddrAux [blockToShareInCurrPartAddr] s0))) by intuition.
						specialize (HaddrInBTS addr) ; intuition.
				}
				assert(HparentInMappedlist : In blockToShareInCurrPartAddr (getMappedBlocks currentPart s0))
						by intuition. (* by found block or showing no modifs from s*)
				unfold getMappedPaddr.
				induction (getMappedBlocks currentPart s0).
				* intuition.
				* simpl. simpl in HparentInMappedlist. simpl in HaddrInParentBlock.
					destruct HparentInMappedlist as [HparentInMappedlist | HparentInMappedlist].
					subst a.
					unfold isBE in HBEbtss0.
					destruct (lookup blockToShareInCurrPartAddr (memory s0) beqAddr) ; try(exfalso ; congruence).
					destruct v ; try(exfalso ; congruence). 
					apply in_app_iff. left. rewrite app_nil_r in *. assumption.
					destruct (lookup a (memory s0) beqAddr) ; intuition.
					destruct v ; intuition.

				*	(* Case (getMappedPaddr globalIdPDChild s0) *)
					apply HVs0. apply in_app_iff. right. assumption.

	- (* child <> globalIdPDChild *)
		destruct (beqAddr parent globalIdPDChild) eqn:beqparentpd ; try(exfalso ; congruence).
		-- (* parent = globalIdPDChild *)
				rewrite <- DependentTypeLemmas.beqAddrTrue in beqparentpd.
				rewrite beqparentpd in *.

				assert(HNoDupPartTree : noDupPartitionTree s) 
						by (unfold consistency in * ; unfold consistency1 in * ; intuition). (* consistency s*)
				assert(HglobalChildNotEq : globalIdPDChild <> child).
				{ eapply childparentNotEq with s ; try (rewrite HparentEq in *) ; intuition. }

				assert(HusedchildEq : getUsedPaddr child s = getUsedPaddr child s0).
				{ eapply HUsedPaddrEqNotInParts0 ; intuition.
					eapply childrenArePDT with globalIdPDChild ; intuition.
					unfold consistency in * ; unfold consistency1 in * ; intuition.
					rewrite HpdchildrenEq in *. intuition.
				}
				rewrite HusedchildEq in *.
				rewrite HpdchildrenEq in *.
					specialize (HVs0 globalIdPDChild child HparentPartTree HchildIsChild addr HnAddrInUsedChild).

					specialize (Hidpdchildmapped addr).
					rewrite Hidpdchildmapped.
					apply in_or_app. right. assumption.

					-- (* parent <> globalIdPDChild *)
							rewrite <- beqAddrFalse in *.
							assert(Hparent : isPDT parent s0)
								by (apply partitionsArePDT with multiplexer ; intuition).
							assert(HchildrenparentEq : getChildren parent s = getChildren parent s0).
							{ apply HChildrenEqNotInParts0 ; intuition. }
							assert(Hchild : isPDT child s0).
							{ eapply childrenArePDT with parent ; intuition.
								unfold consistency in * ; unfold consistency1 in * ; intuition.
								rewrite HchildrenparentEq in * ; intuition.
							}
							assert(HusedchildEq : getUsedPaddr child s = getUsedPaddr child s0).
							{ apply HUsedPaddrEqNotInParts0 ; intuition.
							}

							assert(HmappedparentEq : getMappedPaddr parent s = getMappedPaddr parent s0)
								by (apply HMappedPaddrEqNotInParts0 ; intuition).

							rewrite HusedchildEq in *. rewrite HmappedparentEq in *.
							rewrite HchildrenparentEq in*.
							specialize (HVs0 parent child HparentPartTree HchildIsChild addr HnAddrInUsedChild).
							assumption.
}
Qed.


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
PDChildAddr
pdchildIsNull
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
Hoptionlists olds n0 n1 n2 nbleft
s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12
s :

AddMemoryBlockPropagatedProperties
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
PDChildAddr
pdchildIsNull
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
Hoptionlists olds n0 n1 n2 nbleft
s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12
s
->
kernelDataIsolation s.
Proof.
(*reconstuct hypotheses *)
intro hyps. unfold AddMemoryBlockPropagatedProperties in *.
destruct hyps as
[HaddrIsNull (Hcheck & (HchildCurrPart & (HFull & (Haccessible & (Hpresent &(HpdchildNull & (HslotIsNull & (beqBToShareVIDT & hyps))))))))].
destruct hyps as
[Hprops0 (Hs & (Hprops & ((Hnbleft & (Hs2Eq & Hlists)) & (HbtsEq & (Hpdchildflags0 & (Hs1 & (Hs2 & (Hs3 & (Hs4 & ( Hs5 & (Hs6
& (Hs7 & (Hs8 & (Hs9 & (Hs10 & (Hs11 & (Hs12 & (Hs12Eq & (HbtsNotNull & (HSh1Offset & (HBEbtss0 & (Hlookupbtss & (HBEbts & (
HSHEs & (Hblockindex & (HBEs0 & (HBEs & (HlookupnewBs0 & (HlookupnewBs & (Hpdinsertions0 & (
Hpdinsertions & (HPDTs0 & (HPDTs & (HSceOffset & (HSCEs0 & (HSCEs & (beqpdnewB & (beqnewBsce & (
beqscesh1 & (beqnewBsh1 & (beqsh1bts & (HnewFirstFree & (HnewB & (HnullAddrExists & (HsEq &(
HPDTs10 & (HSCEs10 & (HSHEs10 & (HBEs10 & (HSHEs10Eq & (HlookupbtscurrpartEq & (Hcons & (Hcons2 & (HstartendbtsEq & (
HMappedPaddrEqNotInParts0 & (HConfigPaddrEqNotInParts0 & (HUsedPaddrEqNotInParts0 & (
HChildrenEqNotInParts0 & (HMappedBlocksEqNotInParts0 & HAccessibleMappedPaddrEqNotInParts0))))))))) (*& Hvert)*) ))))))))))))))))))))))))))))))))))))))))))))))))))].

{
	 (* kernelDataIsolation s*)
		unfold kernelDataIsolation.

		assert(HcurrPartEq : currentPart = currentPartition s0) by intuition.
		rewrite HcurrPartEq in *.

		intros part1 part2 Hpart1PartTree Hpart2PartTree.

		assert(HKIs0: kernelDataIsolation s0) by intuition.
		unfold kernelDataIsolation in HKIs0.

				assert(HparentEq : getPartitions multiplexer s = getPartitions multiplexer s0)
			by intuition. (* constructed along the way *)
		rewrite HparentEq in *.

		assert(HpdchildrenEq : getChildren globalIdPDChild s = getChildren globalIdPDChild s0)
			by intuition. (* constructed along the way *)
		rewrite HpdchildrenEq in *.

		assert(Hidpdchildmapped : forall addr, 
			In addr (getMappedPaddr globalIdPDChild s) <->
			In addr
			(getAllPaddrBlock (startAddr (blockrange bentry6)) (endAddr (blockrange bentry6))
					++ getMappedPaddr globalIdPDChild s0))
			by intuition. (* constructed along the way *)

		assert(Hidpdchildconfig : getConfigBlocks globalIdPDChild s = getConfigBlocks globalIdPDChild s0)
			by intuition. (* constructed along the way *)

		assert(Hidpdchildconfigaddr : getConfigPaddr globalIdPDChild s = getConfigPaddr globalIdPDChild s0)
			by intuition. (* constructed along the way *)

		assert(HblockInMappedParent : In blockToShareInCurrPartAddr (getMappedBlocks currentPart s0))
			by (rewrite HcurrPartEq in * ; intuition). (* block found *)
		assert(HaddrInBTS : forall addr, In addr (getAllPaddrBlock
						(startAddr (blockrange bentry6)) (endAddr (blockrange bentry6))) <->
														In addr (getAllPaddrAux [blockToShareInCurrPartAddr] s0))
			by intuition.

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

					rewrite Hidpdchildconfigaddr in *.
					unfold Lib.disjoint in *.
					intros addr HaccessiblePaddr.

					assert(HMappedPaddrEq : In addr (getAccessibleMappedPaddr globalIdPDChild s) ->
									In addr ((getAllPaddrBlock (startAddr (blockrange bentry6))
                                      (endAddr (blockrange bentry6))) ++
											(getAccessibleMappedPaddr globalIdPDChild s0)))
						by intuition.

					specialize (HMappedPaddrEq HaccessiblePaddr).
					apply in_app_or in HMappedPaddrEq.

					assert(HKIparentglobals0 : kernelDataIsolation s0) by intuition.
					assert(HcurrPartPartitionTree : In currentPart (getPartitions multiplexer s0))
							by (rewrite HcurrPartEq in *; unfold consistency in * ; unfold consistency1 in * ; intuition).
					specialize (HKIparentglobals0 currentPart globalIdPDChild
							 HcurrPartPartitionTree Hpart1PartTree).

					assert(HNoDupidpdchild : NoDup (getAllPaddrBlock (startAddr (blockrange bentry6))
                    (endAddr (blockrange bentry6)) ++
                  getMappedPaddr globalIdPDChild s0)) by intuition.
					apply Lib.NoDupSplitInclIff in HNoDupidpdchild.

					assert(HaddrInAccessibleParent : In addr (getAccessibleMappedPaddr currentPart s0)).
					{
						rewrite HcurrPartEq in *.
						specialize (HaddrInBTS addr).
						assert(addrIsAccessible = true) by (apply negb_false_iff in Haccessible ; intuition).
						subst addrIsAccessible.
						destruct HNoDupidpdchild as [HNoDup Hdisjoint].
						unfold Lib.disjoint in Hdisjoint.
						specialize (Hdisjoint addr).
						destruct HMappedPaddrEq as [HaddrInNewB | HaddrInMappedPaddrs0].
						(* case newB*)
						(*assert(HAccesibleIsMappedPaddr : forall (partition addr : paddr) s, In addr (getAccessibleMappedPaddr partition s) ->
								In addr (getMappedPaddr partition s)) by admit.*)
						specialize (addrInAccessibleMappedIsIsMappedPaddr globalIdPDChild addr s0).
						intro HaddrIsMapped.
						apply addrInAccessibleBlockIsAccessibleMapped
									with blockToShareInCurrPartAddr ; intuition.
						(* cnosistency s0 : accessible in child -> accessible in parent *)
						(* case s0 *)
						assert(HaccessibleInParents0 :
									accessibleChildPaddrIsAccessibleIntoParent s0)
							by (unfold consistency in * ; unfold consistency1 in * ; intuition). (* consistency s0*)
						eapply HaccessibleInParents0 with globalIdPDChild ; intuition.
					}

					specialize (HKIparentglobals0 addr HaddrInAccessibleParent).
					assumption.

	-- (* part2 <> globalIdPDChild *)

			rewrite <- beqAddrFalse in *.

			assert(HPDTpart2s0 : isPDT part2 s0)
				by (apply partitionsArePDT with multiplexer ; intuition).
			assert(Hconfigchild2Eq : getConfigPaddr part2 s = getConfigPaddr part2 s0).
			{ eapply HConfigPaddrEqNotInParts0 ; intuition. }
			rewrite Hconfigchild2Eq in *.

			assert(Hidpart2configaddr : getConfigPaddr part2 s = getConfigPaddr part2 s0)
				by (eapply HConfigPaddrEqNotInParts0 ; intuition).
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
											(getAccessibleMappedPaddr globalIdPDChild s0)))
						by intuition. (* constructed along the way *)

					specialize (HMappedPaddrEq HaccessiblePaddr).
					apply in_app_or in HMappedPaddrEq.
					assert(HKIparentglobals0 : kernelDataIsolation s0) by intuition.
					assert(HcurrPartPartitionTree : In currentPart (getPartitions multiplexer s0))
							by (rewrite HcurrPartEq in * ; unfold consistency in * ; unfold consistency1 in * ; intuition).
					specialize (HKIparentglobals0 currentPart part2
							 HcurrPartPartitionTree Hpart2PartTree).

					assert(HNoDupidpdchild : NoDup (getAllPaddrBlock (startAddr (blockrange bentry6))
                    (endAddr (blockrange bentry6)) ++
                  getMappedPaddr globalIdPDChild s0)) by intuition.
					apply Lib.NoDupSplitInclIff in HNoDupidpdchild.

					assert(HaddrInAccessibleParent : In addr (getAccessibleMappedPaddr currentPart s0)).
					{
								rewrite HcurrPartEq in *.
								specialize (HaddrInBTS addr).
								assert(addrIsAccessible = true) by (apply negb_false_iff in Haccessible ; intuition).
								subst addrIsAccessible.
								destruct HNoDupidpdchild as [HNoDup Hdisjoint].
								unfold Lib.disjoint in Hdisjoint.
								specialize (Hdisjoint addr).
								destruct HMappedPaddrEq as [HaddrInNewB | HaddrInMappedPaddrs0].
								(* case newB*)
								(*assert(HAccesibleIsMappedPaddr : forall (partition addr : paddr) s, In addr (getAccessibleMappedPaddr partition s) ->
										In addr (getMappedPaddr partition s)) by admit.*)
								specialize (addrInAccessibleMappedIsIsMappedPaddr globalIdPDChild addr s0).
								intro HaddrIsMapped.
								apply addrInAccessibleBlockIsAccessibleMapped
											with blockToShareInCurrPartAddr ; intuition.
								(* consistency s0 : accessible in child -> accessible in parent *)
								(* case s0 *)
								assert(HaccessibleInParents0 :
											accessibleChildPaddrIsAccessibleIntoParent s0)
									by (unfold consistency in * ; unfold consistency1 in * ; intuition). (* consistency s0*)
								eapply HaccessibleInParents0 with globalIdPDChild ; intuition.
					}

					specialize (HKIparentglobals0 addr HaddrInAccessibleParent).
					assumption.

	- (* part1 <> globalIdPDChild *)
		rewrite <- beqAddrFalse in *.
		assert(HPDTpart1s0 : isPDT part1 s0)
			by (apply partitionsArePDT with multiplexer ; intuition).
		assert(Haccessible1Eq : getAccessibleMappedPaddr part1 s = getAccessibleMappedPaddr part1 s0)
			by (eapply HAccessibleMappedPaddrEqNotInParts0 ; intuition).
		rewrite Haccessible1Eq in *.

		destruct (beqAddr part2 globalIdPDChild) eqn:beqpart2pd ; try(exfalso ; congruence).
		-- (* part2 = globalIdPDChild *)
				rewrite <- DependentTypeLemmas.beqAddrTrue in beqpart2pd.
				rewrite beqpart2pd in *.

				rewrite Hidpdchildconfigaddr in *.

				specialize (HKIs0 part1 globalIdPDChild Hpart1PartTree Hpart2PartTree).
				intuition.

		-- (* part2 <> globalIdPDChild *)
				rewrite <- beqAddrFalse in *.
				assert(HPDTpart2s0 : isPDT part2 s0)
							by (apply partitionsArePDT with multiplexer ; intuition).
				assert(Hconfig2Eq : getConfigPaddr part2 s = getConfigPaddr part2 s0)
					by (eapply HConfigPaddrEqNotInParts0 ; intuition).
				rewrite Hconfig2Eq in *.

				specialize (HKIs0 part1 part2 Hpart1PartTree Hpart2PartTree).
				intuition.
}
Qed.


Lemma AddMemoryBlockHI
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
PDChildAddr
pdchildIsNull
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
Hoptionlists olds n0 n1 n2 nbleft 
s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12
s :

AddMemoryBlockPropagatedProperties
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
PDChildAddr
pdchildIsNull
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
Hoptionlists olds n0 n1 n2 nbleft 
s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12
s
->
partitionsIsolation s.
Proof.
(*reconstuct hypotheses *)
intro hyps. unfold AddMemoryBlockPropagatedProperties in *.
destruct hyps as
[HaddrIsNull (Hcheck & (HchildCurrPart & (HFull & (Haccessible & (Hpresent &(HpdchildNull & (HslotIsNull & (beqBToShareVIDT & hyps))))))))].
destruct hyps as
[Hprops0 (Hs & (Hprops & ((Hnbleft & (Hs2Eq & Hlists)) & (HbtsEq & (Hpdchildflags0 & (Hs1 & (Hs2 & (Hs3 & (Hs4 & ( Hs5 & (Hs6
& (Hs7 & (Hs8 & (Hs9 & (Hs10 & (Hs11 & (Hs12 & (Hs12Eq & (HbtsNotNull & (HSh1Offset & (HBEbtss0 & (Hlookupbtss & (HBEbts & (
HSHEs & (Hblockindex & (HBEs0 & (HBEs & (HlookupnewBs0 & (HlookupnewBs & (Hpdinsertions0 & (
Hpdinsertions & (HPDTs0 & (HPDTs & (HSceOffset & (HSCEs0 & (HSCEs & (beqpdnewB & (beqnewBsce & (
beqscesh1 & (beqnewBsh1 & (beqsh1bts & (HnewFirstFree & (HnewB & (HnullAddrExists & (HsEq &(
HPDTs10 & (HSCEs10 & (HSHEs10 & (HBEs10 & (HSHEs10Eq & (HlookupbtscurrpartEq & (Hcons & (Hcons2 & (HstartendbtsEq & (
HMappedPaddrEqNotInParts0 & (HConfigPaddrEqNotInParts0 & (HUsedPaddrEqNotInParts0 & (
HChildrenEqNotInParts0 & (HMappedBlocksEqNotInParts0 & HAccessibleMappedPaddrEqNotInParts0))))))))) (*& Hvert)*) ))))))))))))))))))))))))))))))))))))))))))))))))))].

	{ (* partitionsIsolation s*)
		unfold partitionsIsolation.

		assert(HcurrPartEq : currentPart = currentPartition s0) by intuition.
		rewrite HcurrPartEq in *.

		intros parent child1 child2 HparentPartTree Hchild1IsChild Hchild2IsChild Hchild1child2NotEq.

		assert(Hpartisolations0: partitionsIsolation s0) by intuition.
		unfold partitionsIsolation in Hpartisolations0.


		assert(HPDTparents : isPDT parent s).
		{ eapply partitionsArePDT. apply HparentPartTree. }
		assert(HPDTchild1s : isPDT child1 s).
		{ eapply childrenArePDT.
			unfold consistency in * ; unfold consistency1 in * ; intuition.
			apply Hchild1IsChild. }
		assert(HPDTchild2s : isPDT child2 s).
		{ eapply childrenArePDT.
			unfold consistency in * ; unfold consistency1 in * ; intuition.
			apply Hchild2IsChild. }
		assert(beqnewBparent : beqAddr newBlockEntryAddr parent = false).
		{ rewrite <- beqAddrFalse ; intro Hf.
			subst parent ; unfold isPDT in * ; unfold isBE in *.
			rewrite HlookupnewBs in *. exfalso ; congruence.
		}
		assert(beqsceparent : beqAddr sceaddr parent = false).
		{ rewrite <- beqAddrFalse ; intro Hf.
			subst parent ; unfold isPDT in * ; unfold isSCE in *.
			destruct (lookup sceaddr (memory s) beqAddr) ; try (exfalso ; congruence).
			destruct v ; try (exfalso ; congruence).
		}

		assert(beqsh1parent : beqAddr sh1eaddr parent = false).
		{ rewrite <- beqAddrFalse ; intro Hf.
			subst parent ; unfold isPDT in * ; unfold isSHE in *.
			destruct (lookup sh1eaddr (memory s) beqAddr) ; try (exfalso ; congruence).
			destruct v ; try (exfalso ; congruence).
		}

		assert(beqnewBchild1 : beqAddr newBlockEntryAddr child1 = false).
		{ rewrite <- beqAddrFalse ; intro Hf.
			subst child1 ; unfold isPDT in * ; unfold isBE in *.
			rewrite HlookupnewBs in *. exfalso ; congruence.
		}
		assert(beqscechild1 : beqAddr sceaddr child1 = false).
		{ rewrite <- beqAddrFalse ; intro Hf.
			subst child1 ; unfold isPDT in * ; unfold isSCE in *.
			destruct (lookup sceaddr (memory s) beqAddr) ; try (exfalso ; congruence).
			destruct v ; try (exfalso ; congruence).
		}
		assert(beqsh1child1 : beqAddr sh1eaddr child1 = false).
		{ rewrite <- beqAddrFalse ; intro Hf.
			subst child1 ; unfold isPDT in * ; unfold isSHE in *.
			destruct (lookup sh1eaddr (memory s) beqAddr) ; try (exfalso ; congruence).
			destruct v ; try (exfalso ; congruence).
		}

		assert(beqnewBchild2 : beqAddr newBlockEntryAddr child2 = false).
		{ rewrite <- beqAddrFalse ; intro Hf.
			subst child2 ; unfold isPDT in * ; unfold isBE in *.
			rewrite HlookupnewBs in *. exfalso ; congruence.
		}
		assert(beqscechild2 : beqAddr sceaddr child2 = false).
		{ rewrite <- beqAddrFalse ; intro Hf.
			subst child2 ; unfold isPDT in * ; unfold isSCE in *.
			destruct (lookup sceaddr (memory s) beqAddr) ; try (exfalso ; congruence).
			destruct v ; try (exfalso ; congruence).
		}
		assert(beqsh1child2 : beqAddr sh1eaddr child2 = false).
		{ rewrite <- beqAddrFalse ; intro Hf.
			subst child2 ; unfold isPDT in * ; unfold isSHE in *.
			destruct (lookup sh1eaddr (memory s) beqAddr) ; try (exfalso ; congruence).
			destruct v ; try (exfalso ; congruence).
		}

		assert(HparentEq : getPartitions multiplexer s = getPartitions multiplexer s0)
			by intuition. (* constructed along the way *)
		rewrite HparentEq in *.

		assert(HpdchildrenEq : getChildren globalIdPDChild s = getChildren globalIdPDChild s0)
			by intuition. (* constructed along the way *)
		rewrite HpdchildrenEq in *.

		assert(Hidpdchildmapped : forall addr, 
			In addr (getMappedPaddr globalIdPDChild s) <->
			In addr
			(getAllPaddrBlock (startAddr (blockrange bentry6)) (endAddr (blockrange bentry6))
					++ getMappedPaddr globalIdPDChild s0))
			by intuition. (* constructed along the way *)

		assert(Hidpdchildconfig : getConfigBlocks globalIdPDChild s = getConfigBlocks globalIdPDChild s0)
			by intuition. (* constructed along the way *)

		assert(Hidpdchildconfigaddr : getConfigPaddr globalIdPDChild s = getConfigPaddr globalIdPDChild s0)
			by intuition. (* constructed along the way *)

		destruct (beqAddr child1 globalIdPDChild) eqn:beqchild1pd ; try(exfalso ; congruence).
			- (* child1 = globalIdPDChild *)
					rewrite <- DependentTypeLemmas.beqAddrTrue in beqchild1pd.
					rewrite beqchild1pd in *.

			(* newB mapped in child, is isolated from child2 if child 2 didn't have the block
					at s0
					-> if it had the block at s0, then it was shared from the parent so
						pdchild = child1, however at s0 pdchild = null so contradiction *)
			assert(HNoDupPartTree : noDupPartitionTree s)
				by (unfold consistency in * ; unfold consistency1 in * ; intuition). (* consistency s*)
			assert(HPDTparent : isPDT parent s0)
				by (apply partitionsArePDT with multiplexer ; intuition).
			assert(HglobalChildNotEq : parent <> globalIdPDChild).
			{ eapply childparentNotEq with s ; try (rewrite HparentEq in *) ; intuition. }
			assert(HchildrenparentEq : getChildren parent s = getChildren parent s0).
			{ apply HChildrenEqNotInParts0 ; intuition. }
			rewrite HchildrenparentEq in *.
			assert(Hchild2 : isPDT child2 s0).
			{ eapply childrenArePDT with parent ; intuition.
				unfold consistency in * ; unfold consistency1 in * ; intuition.
			}
			assert(Husedchild2Eq : getUsedPaddr child2 s = getUsedPaddr child2 s0).
			{ apply HUsedPaddrEqNotInParts0 ; intuition.
			}

			assert(HmappedparentEq : getMappedPaddr parent s = getMappedPaddr parent s0)
				by (apply HMappedPaddrEqNotInParts0 ; intuition).

				assert(Hparent : parent = currentPart).
				{
					assert(HisParents0 : isParent s0)
						by (unfold consistency in * ; unfold consistency1 in * ; intuition). (* consistency s0*)
					assert(HisChilds0 : isChild s0)
						by (unfold consistency in * ; unfold consistency1 in * ; intuition). (* consistency s0*)
					assert(In currentPart (getPartitions multiplexer s0)) 
						by (rewrite HcurrPartEq in * ; unfold consistency in * ; unfold consistency1 in * ; intuition). (* consistency s0*)
					apply uniqueParent with globalIdPDChild s0; intuition.
					rewrite HcurrPartEq in *. assumption.
				}
				subst parent.

			unfold Lib.disjoint.
			intros addr HaddrInchildused.

			unfold getUsedPaddr in HaddrInchildused.
			specialize (Hidpdchildmapped addr).

			rewrite Husedchild2Eq in *.

			specialize (Hpartisolations0 	currentPart globalIdPDChild child2
																		HparentPartTree Hchild1IsChild Hchild2IsChild
																		Hchild1child2NotEq).

			rewrite Hidpdchildconfigaddr in *.

			apply in_app_or in HaddrInchildused.
			destruct HaddrInchildused.
			(* Case In addr configpaddr *)
			unfold Lib.disjoint in Hpartisolations0.
			specialize (Hpartisolations0 addr ).
			apply Hpartisolations0.
			unfold getUsedPaddr. intuition.

			(* Case In addr mappedpaddr : newB or (mapped at s0) *)
			destruct Hidpdchildmapped as [Hidpdchildmapped HidpdchildmappedR].
			specialize (Hidpdchildmapped H). (*In addr (getMappedPaddr globalIdPDChild s)*)
			apply in_app_or in Hidpdchildmapped.
			destruct Hidpdchildmapped.

			* (* In addr [NewB] *)
				(* if in child2, then exists a block in parent that holds the address
					-> but not shared at s0 -> contradiction *)
					intro HaddrInChild2s0.

					assert(HVs0 : verticalSharing s0) by intuition.
					specialize (HVs0 currentPart child2 HparentPartTree Hchild2IsChild).
					unfold incl in *.
					specialize (HVs0 addr HaddrInChild2s0).

					assert(HsharedInChilds0 : sharedBlockPointsToChild s0)
						by (unfold consistency in * ; unfold consistency1 in * ; intuition).
					unfold sharedBlockPointsToChild in HsharedInChilds0.

					assert(HaddrInParentBlock : In addr (getAllPaddrAux [blockToShareInCurrPartAddr] s0)).
					{
							assert(HaddrInBTS : (forall addr : paddr,
							  In addr
							    (getAllPaddrBlock (startAddr (blockrange bentry6))
							       (endAddr (blockrange bentry6))) <->
							  In addr (getAllPaddrAux [blockToShareInCurrPartAddr] s0))) by intuition.
							specialize (HaddrInBTS addr) ; intuition.
					}
					assert(HparentInMappedlist : In blockToShareInCurrPartAddr (getMappedBlocks currentPart s0))
							by (rewrite HcurrPartEq in * ; intuition). (* by found block or showing no modifs from s*)

					assert(Hsh1entryaddr : sh1entryAddr blockToShareInCurrPartAddr sh1eaddr s0).
					{
						unfold sh1entryAddr. unfold isBE in *.
						destruct (lookup blockToShareInCurrPartAddr (memory s0) beqAddr) ; try(exfalso ; congruence).
						destruct v ; try (exfalso ; congruence).
						trivial.
					}

					specialize (HsharedInChilds0 currentPart child2 addr blockToShareInCurrPartAddr sh1eaddr
														HparentPartTree Hchild2IsChild HaddrInChild2s0 HaddrInParentBlock
														HparentInMappedlist Hsh1entryaddr).

					(* prepare contradiction : bts's first shadow entry is null, while
							we have in hypothesis that it points to child2 or that the PDflag is set *)
					destruct Hpdchildflags0 as [Hsh1entrypdchilds0 sh1entrypdflags0].
					destruct HsharedInChilds0 as [Hsh1entryaddrs0 | Hsh1entrychilds0].
		(* congruence with Hsh1entrychild after bug fix in addMemoryBlock
							-> should end with child2 = nullAddr which is false because not shared at s0 *)
					+ (* case pdchild = child2 *)
						rewrite <- HSh1Offset in *.
						unfold sh1entryPDchild in *.
						unfold sh1entryAddr in *.
						destruct (lookup sh1eaddr (memory s0) beqAddr) eqn:Hlookupsh1 ; try(exfalso ; congruence).
						destruct v ; try(exfalso ; congruence).
						subst child2. rewrite <- Hsh1entrypdchilds0 in *. (* nullAddr *)
						assert(HnullAddrExists0 : nullAddrExists s0)
							by (unfold consistency in * ; unfold consistency1 in * ; intuition).
						unfold nullAddrExists in *. unfold isPADDR in *.
						unfold isPDT in *.
						destruct (lookup nullAddr (memory s0) beqAddr) ; try(exfalso ; congruence).
						destruct v ; try(exfalso ; congruence).
					+ (* case pdflag is set *)
						rewrite <- HSh1Offset in *.
						unfold sh1entryPDflag in *.
						unfold sh1entryAddr in *.
						destruct (lookup sh1eaddr (memory s0) beqAddr) eqn:Hlookupsh1 ; try(exfalso ; congruence).
						destruct v ; try(exfalso ; congruence).
					* (* In addr getMappedPaddr s0 -> leads to s0 *)
						unfold Lib.disjoint in Hpartisolations0.
						specialize (Hpartisolations0 addr ).
						apply Hpartisolations0.
						unfold getUsedPaddr. intuition.

- (* child1 <> globalIdPDChild *)
	destruct (beqAddr child2 globalIdPDChild) eqn:beqchild2pd ; try(exfalso ; congruence).
	--- (* child2 = globalIdPDChild *)
			rewrite <- DependentTypeLemmas.beqAddrTrue in beqchild2pd.
			rewrite beqchild2pd in *.

			(* DUP with child1 *)
			assert(HNoDupPartTree : noDupPartitionTree s)
				by (unfold consistency in * ; unfold consistency1 in * ; intuition). (* consistency s*)
			assert(HPDTparent : isPDT parent s0)
				by (apply partitionsArePDT with multiplexer ; intuition).
			assert(HglobalChildNotEq : parent <> globalIdPDChild).
			{ eapply childparentNotEq with s ; try (rewrite HparentEq in *) ; intuition. }
			assert(HchildrenparentEq : getChildren parent s = getChildren parent s0).
			{ apply HChildrenEqNotInParts0 ; intuition. }
			rewrite HchildrenparentEq in *.
			assert(Hchild2 : isPDT child1 s0).
			{ eapply childrenArePDT with parent ; intuition.
				unfold consistency in * ; unfold consistency1 in * ; intuition.
			}
			assert(Husedchild1Eq : getUsedPaddr child1 s = getUsedPaddr child1 s0).
			{ apply HUsedPaddrEqNotInParts0 ; intuition.
			}

			assert(Hparent : parent = currentPart).
			{	
				assert(HisParents0 : isParent s0)
						by (unfold consistency in * ; unfold consistency1 in * ; intuition).  (* consistency *)
				assert(HisChilds0 : isChild s0)
						by (unfold consistency in * ; unfold consistency1 in * ; intuition).  (* consistency *)
				assert(In currentPart (getPartitions multiplexer s0))
						by (rewrite HcurrPartEq in * ; unfold consistency in * ; unfold consistency1 in * ; intuition).  (* consistency s0*)
				apply uniqueParent with globalIdPDChild s0; intuition.
				rewrite HcurrPartEq in*. trivial.
			}
			subst parent.


			unfold Lib.disjoint.
			intros addr HaddrInchildused.

			rewrite Husedchild1Eq in *.

			specialize (Hpartisolations0 	currentPart child1 globalIdPDChild
																		HparentPartTree Hchild1IsChild Hchild2IsChild
																		Hchild1child2NotEq).
			unfold getUsedPaddr.
			rewrite Hidpdchildconfigaddr in *.
			specialize (Hidpdchildmapped addr).

			(* Case In addr mappedpaddr : newB or (mapped at s0) *)
			intro HaddrInGlobalFalse.
			apply in_app_or in HaddrInGlobalFalse.
 			rewrite Hidpdchildmapped in HaddrInGlobalFalse.
			assert(HlistEq : 	In addr
						               (getConfigPaddr globalIdPDChild s0) \/
						                In addr	
														(getAllPaddrBlock (startAddr (blockrange bentry6))
						                   (endAddr (blockrange bentry6)) ++ 
															(getMappedPaddr globalIdPDChild s0)) ->
														In addr (
						               (getConfigPaddr globalIdPDChild s0 ++
						                	getMappedPaddr globalIdPDChild s0) ++
														(getAllPaddrBlock (startAddr (blockrange bentry6))
						                   (endAddr (blockrange bentry6))))).
			{ simpl.
				intros HIn. destruct HIn.
			 	apply in_app_iff. rewrite in_app_iff. intuition.
				apply in_app_or in H. destruct H.
			 	apply in_app_iff. rewrite in_app_iff. intuition.
				rewrite in_app_iff.
				intuition.
			}
			specialize (HlistEq HaddrInGlobalFalse).

			apply in_app_or in HlistEq.
			destruct HlistEq as [Haddrs0 | HaddrnewB].

			* (* In addr getMappedPaddr s0 -> leads to s0 *)
				unfold Lib.disjoint in Hpartisolations0.
				specialize (Hpartisolations0 addr HaddrInchildused).
				apply Hpartisolations0.
				unfold getUsedPaddr. intuition.

			* (* In addr [NewB] *)
				(* if in child1, then exists a block in parent that holds the address
					-> but not shared at s0 -> contradiction *)

				assert(HVs0 : verticalSharing s0) by intuition.
				specialize (HVs0 currentPart child1 HparentPartTree Hchild1IsChild).
				unfold incl in *.
				specialize (HVs0 addr HaddrInchildused).
				assert(HsharedInChilds0 : sharedBlockPointsToChild s0)
					by (unfold consistency in * ; unfold consistency1 in * ; intuition).
				unfold sharedBlockPointsToChild in HsharedInChilds0.

				assert(HaddrInParentBlock : In addr (getAllPaddrAux [blockToShareInCurrPartAddr] s0)).
				{
						assert(HaddrInBTS : (forall addr : paddr,
					    In addr
					      (getAllPaddrBlock (startAddr (blockrange bentry6))
					         (endAddr (blockrange bentry6))) <->
					    In addr (getAllPaddrAux [blockToShareInCurrPartAddr] s0))) by intuition.
						specialize (HaddrInBTS addr) ; intuition.
				}
				assert(HparentInMappedlist : In blockToShareInCurrPartAddr (getMappedBlocks currentPart s0))
						by (rewrite HcurrPartEq in * ; intuition). (* by found block or showing no modifs from s*)

				assert(Hsh1entryaddr : sh1entryAddr blockToShareInCurrPartAddr sh1eaddr s0).
				{
					unfold sh1entryAddr. unfold isBE in *.
					destruct (lookup blockToShareInCurrPartAddr (memory s0) beqAddr) ; try(exfalso ; congruence).
					destruct v ; try (exfalso ; congruence).
					trivial.
				}

				specialize (HsharedInChilds0 currentPart child1 addr blockToShareInCurrPartAddr sh1eaddr
													HparentPartTree Hchild1IsChild HaddrInchildused HaddrInParentBlock
													HparentInMappedlist Hsh1entryaddr).

(* prepare contradiction : bts's first shadow entry is null, while
					we have in hypothesis that it points to child2 or that the PDflag is set *)
				destruct Hpdchildflags0 as [Hsh1entrypdchilds0 sh1entrypdflags0].
				destruct HsharedInChilds0 as [Hsh1entryaddrs0 | Hsh1entrychilds0].
	(* congruence with Hsh1entrychild after bug fix in addMemoryBlock
						-> should end with child2 = nullAddr which is false because not shared at s0 *)
				+ (* case pdchild = child1 *)
						rewrite <- HSh1Offset in *.
						unfold sh1entryPDchild in *.
						unfold sh1entryAddr in *.
						destruct (lookup sh1eaddr (memory s0) beqAddr) eqn:Hlookupsh1 ; try(exfalso ; congruence).
						destruct v ; try(exfalso ; congruence).
						subst child1. rewrite <- Hsh1entrypdchilds0 in *. (* nullAddr *)
						assert(HnullAddrExists0 : nullAddrExists s0)
							by (unfold consistency in * ; unfold consistency1 in * ; intuition).
						unfold nullAddrExists in *. unfold isPADDR in *.
						unfold isPDT in *.
						destruct (lookup nullAddr (memory s0) beqAddr) ; try(exfalso ; congruence).
						destruct v ; try(exfalso ; congruence).
					+ (* case pdflag is set *)
						rewrite <- HSh1Offset in *.
						unfold sh1entryPDflag in *.
						unfold sh1entryAddr in *.
						destruct (lookup sh1eaddr (memory s0) beqAddr) eqn:Hlookupsh1 ; try(exfalso ; congruence).
						destruct v ; try(exfalso ; congruence).

--- (* child1 <> globalIdPDchild *)

		rewrite <- beqAddrFalse in *.
		assert(HPDTparent : isPDT parent s0)
			by (apply partitionsArePDT with multiplexer ; intuition).
		assert(HNoDupPartTree : noDupPartitionTree s)
				by (unfold consistency in * ; unfold consistency1 in * ; intuition). (* consistency s*)
		assert(HglobalChildNotEq1 : parent <> child1).
		{ eapply childparentNotEq with s ; try (rewrite HparentEq in *) ; intuition. }
		assert(HglobalChildNotEq2 : parent <> child2).
		{ eapply childparentNotEq with s ; try (rewrite HparentEq in *) ; intuition. }

		destruct (beqAddr globalIdPDChild parent) eqn:beqparentidpd; try(exfalso ; congruence).
		---- (* globalIdPDChild = parent *)
					rewrite <- DependentTypeLemmas.beqAddrTrue in beqparentidpd.
					rewrite <- beqparentidpd in *.
				(*assert(HchildrenparentEq : getChildren parent s = getChildren parent s0).
				{ apply HChildrenEqNotInParts0 ; intuition. }*)
				rewrite HpdchildrenEq in *.
				assert(Hchild1 : isPDT child1 s0).
				{ eapply childrenArePDT with globalIdPDChild ; intuition.
					unfold consistency in * ; unfold consistency1 in * ; intuition.
				}
				assert(Hchild2 : isPDT child2 s0).
				{ eapply childrenArePDT with globalIdPDChild ; intuition.
					unfold consistency in * ; unfold consistency1 in * ; intuition.
				}
				assert(Husedchild1Eq : getUsedPaddr child1 s = getUsedPaddr child1 s0).
				{ apply HUsedPaddrEqNotInParts0 ; intuition.
				}
				assert(Husedchild2Eq : getUsedPaddr child2 s = getUsedPaddr child2 s0).
				{ apply HUsedPaddrEqNotInParts0 ; intuition.
				}

				specialize (Hpartisolations0 globalIdPDChild child1 child2 HparentPartTree Hchild1IsChild Hchild2IsChild
										Hchild1child2NotEq).
				rewrite Husedchild1Eq. rewrite Husedchild2Eq.
				assumption.

		---- (* globalIdPDChild <> parent *)
				(* DUP *)
				rewrite <- beqAddrFalse in *.
				assert(HchildrenparentEq : getChildren parent s = getChildren parent s0).
				{ apply HChildrenEqNotInParts0 ; intuition. }
				rewrite HchildrenparentEq in *.
				assert(Hchild1 : isPDT child1 s0).
				{ eapply childrenArePDT with parent ; intuition.
					unfold consistency in * ; unfold consistency1 in * ; intuition.
				}
				assert(Hchild2 : isPDT child2 s0).
				{ eapply childrenArePDT with parent ; intuition.
					unfold consistency in * ; unfold consistency1 in * ; intuition.
				}
				assert(Husedchild1Eq : getUsedPaddr child1 s = getUsedPaddr child1 s0).
				{ apply HUsedPaddrEqNotInParts0 ; intuition.
				}
				assert(Husedchild2Eq : getUsedPaddr child2 s = getUsedPaddr child2 s0).
				{ apply HUsedPaddrEqNotInParts0 ; intuition.
				}

				specialize (Hpartisolations0 parent child1 child2 HparentPartTree Hchild1IsChild Hchild2IsChild
										Hchild1child2NotEq).
				rewrite Husedchild1Eq. rewrite Husedchild2Eq.
				assumption.

} (*end of PartitionsIsolation *)
Qed.

