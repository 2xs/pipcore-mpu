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
Require Import Core.Services.

Require Import Proof.Isolation Proof.Hoare Proof.Consistency Proof.WeakestPreconditions
Proof.StateLib Proof.InternalLemmas Proof.DependentTypeLemmas.

Require Import Invariants (*GetTableAddr UpdateShadow2Structure UpdateShadow1Structure
               PropagatedProperties MapMMUPage*) Proof.invariants.findBlockInKSWithAddr.

Require Import isBuiltFromWriteAccessibleRec writeAccessibleToAncestorsIfNotCutRec (*insertNewEntry*)
                removeBlockFromPhysicalMPUIfAlreadyMapped.

Require Import Bool List EqNat Lia Coq.Logic.ProofIrrelevance.
Import List.ListNotations.

Require Import Model.Monad.

Module WP := WeakestPreconditions.

Lemma insertNewEntry 	(pdinsertion startaddr endaddr origin: paddr)
									 (r w e : bool) (currnbfreeslots : index) (P : state -> Prop):
{{ fun s => consistency s
(* to retrieve the fields in pdinsertion *)
/\ (exists pdentry, lookup pdinsertion (memory s) beqAddr = Some (PDT pdentry)
          /\ (pdinsertion <> constantRootPartM ->
                  isPDT (parent pdentry) s
                  /\ (forall addr, In addr (getAllPaddrBlock startaddr endaddr)
                              -> In addr (getMappedPaddr (parent pdentry) s))
                  /\ (exists blockParent endParent,
                          In blockParent (getMappedBlocks (parent pdentry) s)
                          /\ bentryStartAddr blockParent origin s
                          /\ bentryEndAddr blockParent endParent s
                          /\ origin <= startaddr /\ endParent >= endaddr)))
(* to show the first free slot pointer is not NULL *)
/\ (pdentryNbFreeSlots pdinsertion currnbfreeslots s /\ currnbfreeslots > 0)
/\ (exists firstfreepointer, pdentryFirstFreeSlot pdinsertion firstfreepointer s /\
 firstfreepointer <> nullAddr)
/\ 	((startaddr < endaddr) /\ (Constants.minBlockSize <= (endaddr - startaddr)))
/\ P s
}}

Internal.insertNewEntry pdinsertion startaddr endaddr origin r w e currnbfreeslots

{{fun newentryaddr s =>
(exists s0, P s0 /\ consistency1 s (* only propagate the 1st batch*)
(* expected new state after memory writes and associated properties on the new state s *)
/\ (exists pdentry : PDTable, exists pdentry0 pdentry1: PDTable,
 exists bentry bentry0 bentry1 bentry2 bentry3 bentry4 bentry5 bentry6: BlockEntry,
 exists sceaddr, exists scentry : SCEntry,
 exists newBlockEntryAddr newFirstFreeSlotAddr predCurrentNbFreeSlots,
s = {|
currentPartition := currentPartition s0;
memory := add sceaddr
							 (SCE {| origin := origin; next := next scentry |})
					 (add newBlockEntryAddr
		  (BE
			 (CBlockEntry (read bentry5) (write bentry5) e (present bentry5)
				(accessible bentry5) (blockindex bentry5) (blockrange bentry5)))
					 (add newBlockEntryAddr
		  (BE
			 (CBlockEntry (read bentry4) w (exec bentry4) (present bentry4)
				(accessible bentry4) (blockindex bentry4) (blockrange bentry4)))
					 (add newBlockEntryAddr
		  (BE
			 (CBlockEntry r (write bentry3) (exec bentry3) (present bentry3)
				(accessible bentry3) (blockindex bentry3) (blockrange bentry3)))
					 (add newBlockEntryAddr
		  (BE
			 (CBlockEntry (read bentry2) (write bentry2) (exec bentry2)
				(present bentry2) true (blockindex bentry2) (blockrange bentry2)))
					 (add newBlockEntryAddr
		  (BE
			 (CBlockEntry (read bentry1) (write bentry1) (exec bentry1) true
				(accessible bentry1) (blockindex bentry1) (blockrange bentry1)))
					 (add newBlockEntryAddr
		  (BE
			 (CBlockEntry (read bentry0) (write bentry0) (exec bentry0)
				(present bentry0) (accessible bentry0) (blockindex bentry0)
				(CBlock (startAddr (blockrange bentry0)) endaddr)))
					 (add newBlockEntryAddr
			  (BE
				 (CBlockEntry (read bentry) (write bentry)
					(exec bentry) (present bentry) (accessible bentry)
					(blockindex bentry)
					(CBlock startaddr (endAddr (blockrange bentry)))))
						 (add pdinsertion
		  (PDT
			 {|
			 structure := structure pdentry0;
			 firstfreeslot := firstfreeslot pdentry0;
			 nbfreeslots := predCurrentNbFreeSlots;
			 nbprepare := nbprepare pdentry0;
			 parent := parent pdentry0;
			 MPU := MPU pdentry0;
								 vidtAddr := vidtAddr pdentry0 |})
						 (add pdinsertion
		  (PDT
			 {|
			 structure := structure pdentry;
			 firstfreeslot := newFirstFreeSlotAddr;
			 nbfreeslots := nbfreeslots pdentry;
			 nbprepare := nbprepare pdentry;
			 parent := parent pdentry;
			 MPU := MPU pdentry;
								 vidtAddr := vidtAddr pdentry |}) (memory s0) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr)
                            beqAddr) beqAddr) beqAddr) beqAddr) beqAddr |}
/\ newBlockEntryAddr = newentryaddr
/\ lookup newBlockEntryAddr (memory s0) beqAddr = Some (BE bentry)
/\ lookup newBlockEntryAddr (memory s) beqAddr = Some (BE bentry6) /\
bentry6 = (CBlockEntry (read bentry5) (write bentry5) e (present bentry5)
					  (accessible bentry5) (blockindex bentry5) (blockrange bentry5))
/\
bentry5 = (CBlockEntry (read bentry4) w (exec bentry4) (present bentry4)
					  (accessible bentry4) (blockindex bentry4) (blockrange bentry4))
/\
bentry4 = (CBlockEntry r (write bentry3) (exec bentry3) (present bentry3)
					  (accessible bentry3) (blockindex bentry3) (blockrange bentry3))
/\
bentry3 = (CBlockEntry (read bentry2) (write bentry2) (exec bentry2)
					  (present bentry2) true (blockindex bentry2) (blockrange bentry2))
/\
bentry2 = (CBlockEntry (read bentry1) (write bentry1) (exec bentry1) true
					  (accessible bentry1) (blockindex bentry1) (blockrange bentry1))
/\
bentry1 = (CBlockEntry (read bentry0) (write bentry0) (exec bentry0)
					  (present bentry0) (accessible bentry0) (blockindex bentry0)
					  (CBlock (startAddr (blockrange bentry0)) endaddr))
/\
bentry0 = (CBlockEntry (read bentry) (write bentry)
						  (exec bentry) (present bentry) (accessible bentry)
						  (blockindex bentry)
						  (CBlock startaddr (endAddr (blockrange bentry))))
/\ lookup pdinsertion (memory s0) beqAddr = Some (PDT pdentry)
/\ lookup pdinsertion (memory s) beqAddr = Some (PDT pdentry1) /\
pdentry1 = {|     structure := structure pdentry0;
				   firstfreeslot := firstfreeslot pdentry0;
				   nbfreeslots := predCurrentNbFreeSlots;
				   nbprepare := nbprepare pdentry0;
				   parent := parent pdentry0;
				   MPU := MPU pdentry0;
									 vidtAddr := vidtAddr pdentry0 |} /\
pdentry0 = {|    structure := structure pdentry;
				   firstfreeslot := newFirstFreeSlotAddr;
				   nbfreeslots := nbfreeslots pdentry;
				   nbprepare := nbprepare pdentry;
				   parent := parent pdentry;
				   MPU := MPU pdentry;
									 vidtAddr := vidtAddr pdentry|}
(* propagate new s0 properties *)
/\ pdentryFirstFreeSlot pdinsertion newBlockEntryAddr s0
/\ bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr s0
/\ lookup sceaddr (memory s0) beqAddr = Some (SCE scentry)

(* propagate new properties (copied from last step) *)
/\ pdentryNbFreeSlots pdinsertion predCurrentNbFreeSlots s
/\ StateLib.Index.pred currnbfreeslots = Some predCurrentNbFreeSlots
/\ blockindex bentry6 = blockindex bentry5
/\ blockindex bentry5 = blockindex bentry4
/\ blockindex bentry4 = blockindex bentry3
/\ blockindex bentry3 = blockindex bentry2
/\ blockindex bentry2 = blockindex bentry1
/\ blockindex bentry1 = blockindex bentry0
/\ blockindex bentry0 = blockindex bentry
/\ blockindex bentry6 = blockindex bentry
/\ isPDT pdinsertion s0
/\ isPDT pdinsertion s
/\ isBE newBlockEntryAddr s0
/\ isBE newBlockEntryAddr s
/\ isSCE sceaddr s0
/\ isSCE sceaddr s
/\ sceaddr = CPaddr (newBlockEntryAddr + scoffset)
/\ firstfreeslot pdentry1 = newFirstFreeSlotAddr
/\ newBlockEntryAddr = (firstfreeslot pdentry)
/\ newFirstFreeSlotAddr <> pdinsertion
/\ pdinsertion <> newBlockEntryAddr
/\ newFirstFreeSlotAddr <> newBlockEntryAddr
/\ sceaddr <> newBlockEntryAddr
/\ sceaddr <> pdinsertion
/\ sceaddr <> newFirstFreeSlotAddr
(* pdinsertion's new free slots list and relation with list at s0 *)
/\ (exists (optionfreeslotslist : list optionPaddr) (s2 : state)
			 (n0 n1 n2 : nat) (nbleft : index),
 nbleft = CIndex (currnbfreeslots - 1) /\
 nbleft < maxIdx /\
 s =
 {|
   currentPartition := currentPartition s0;
   memory :=
	 add sceaddr (SCE {| origin := origin; next := next scentry |})
	   (memory s2) beqAddr
 |} /\
	 ( optionfreeslotslist = getFreeSlotsListRec n1 newFirstFreeSlotAddr s2 nbleft /\
		   getFreeSlotsListRec n2 newFirstFreeSlotAddr s nbleft = optionfreeslotslist /\
		   optionfreeslotslist = getFreeSlotsListRec n0 newFirstFreeSlotAddr s0 nbleft /\
		   n0 <= n1 /\
		   nbleft < n0 /\
		   n1 <= n2 /\
		   nbleft < n2 /\
		   n2 <= maxIdx + 1 /\
		   (wellFormedFreeSlotsList optionfreeslotslist = False -> False) /\
		   NoDup (filterOptionPaddr optionfreeslotslist) /\
		   (In newBlockEntryAddr (filterOptionPaddr optionfreeslotslist) -> False) /\
		   (exists optionentrieslist : list optionPaddr,
			  optionentrieslist = getKSEntries pdinsertion s2 /\
			  getKSEntries pdinsertion s = optionentrieslist /\
			  optionentrieslist = getKSEntries pdinsertion s0 /\
					 (* newB in free slots list at s0, so in optionentrieslist *)
					 In newBlockEntryAddr (filterOptionPaddr optionentrieslist)
				 )
		 )

	 /\ (	isPDT multiplexer s
			 /\ getPartitions multiplexer s2 = getPartitions multiplexer s0
			 /\ getPartitions multiplexer s = getPartitions multiplexer s2
			 /\ getChildren pdinsertion s2 = getChildren pdinsertion s0
			 /\ getChildren pdinsertion s = getChildren pdinsertion s2
			 /\ getConfigBlocks pdinsertion s2 = getConfigBlocks pdinsertion s0
			 /\ getConfigBlocks pdinsertion s = getConfigBlocks pdinsertion s2
			 /\ getConfigPaddr pdinsertion s2 = getConfigPaddr pdinsertion s0
			 /\ getConfigPaddr pdinsertion s = getConfigPaddr pdinsertion s2
			 /\ (forall block, In block (getMappedBlocks pdinsertion s) <->
								 In block (newBlockEntryAddr:: (getMappedBlocks pdinsertion s0)))
			 /\ ((forall addr, In addr (getMappedPaddr pdinsertion s) <->
						 In addr (getAllPaddrBlock (startAddr (blockrange bentry6)) (endAddr (blockrange bentry6))
							  ++ getMappedPaddr pdinsertion s0)) /\
						 length (getMappedPaddr pdinsertion s) =
						 length (getAllPaddrBlock (startAddr (blockrange bentry6))
								  (endAddr (blockrange bentry6)) ++ getMappedPaddr pdinsertion s0))
			 /\ (forall block, In block (getAccessibleMappedBlocks pdinsertion s) <->
								 In block (newBlockEntryAddr:: (getAccessibleMappedBlocks pdinsertion s0)))
			 /\ (forall addr, In addr (getAccessibleMappedPaddr pdinsertion s) <->
						 In addr (getAllPaddrBlock (startAddr (blockrange bentry6)) (endAddr (blockrange bentry6))
							  ++ getAccessibleMappedPaddr pdinsertion s0))

			 /\ (* if not concerned *)
				 (forall partition : paddr,
						 partition <> pdinsertion ->
						 isPDT partition s0 ->
						 getKSEntries partition s = getKSEntries partition s0)
			 /\ (forall partition : paddr,
						 partition <> pdinsertion ->
						 isPDT partition s0 ->
						  getMappedPaddr partition s = getMappedPaddr partition s0)
			 /\ (forall partition : paddr,
						 partition <> pdinsertion ->
						 isPDT partition s0 ->
						 getConfigPaddr partition s = getConfigPaddr partition s0)
			 /\ (forall partition : paddr,
													 partition <> pdinsertion ->
													 isPDT partition s0 ->
													 getPartitions partition s = getPartitions partition s0)
			 /\ (forall partition : paddr,
													 partition <> pdinsertion ->
													 isPDT partition s0 ->
													 getChildren partition s = getChildren partition s0)
			 /\ (forall partition : paddr,
													 partition <> pdinsertion ->
													 isPDT partition s0 ->
													 getMappedBlocks partition s = getMappedBlocks partition s0)
			 /\ (forall partition : paddr,
													 partition <> pdinsertion ->
													 isPDT partition s0 ->
													 getAccessibleMappedBlocks partition s = getAccessibleMappedBlocks partition s0)
			 /\ (forall partition : paddr,
						 partition <> pdinsertion ->
						 isPDT partition s0 ->
						  getAccessibleMappedPaddr partition s = getAccessibleMappedPaddr partition s0)

		 )
	 /\ (forall partition : paddr,
				 isPDT partition s = isPDT partition s0
			 )
 )




(* intermediate steps *)
/\ exists s1 s2 s3 s4 s5 s6 s7 s8 s9 s10,
s1 = {|
currentPartition := currentPartition s0;
memory := add pdinsertion
		 (PDT
			{|
			  structure := structure pdentry;
			  firstfreeslot := newFirstFreeSlotAddr;
			  nbfreeslots := nbfreeslots pdentry;
			  nbprepare := nbprepare pdentry;
			  parent := parent pdentry;
			  MPU := MPU pdentry;
			  vidtAddr := vidtAddr pdentry
			|}) (memory s0) beqAddr |}
/\ s2 = {|
currentPartition := currentPartition s1;
memory := add pdinsertion
			(PDT
			   {|
				 structure := structure pdentry0;
				 firstfreeslot := firstfreeslot pdentry0;
				 nbfreeslots := predCurrentNbFreeSlots;
				 nbprepare := nbprepare pdentry0;
				 parent := parent pdentry0;
				 MPU := MPU pdentry0;
				 vidtAddr := vidtAddr pdentry0
			   |}
		  ) (memory s1) beqAddr |}
/\ s3 = {|
currentPartition := currentPartition s2;
memory := add newBlockEntryAddr
		 (BE
			(CBlockEntry (read bentry) 
			   (write bentry) (exec bentry) 
			   (present bentry) (accessible bentry)
			   (blockindex bentry)
			   (CBlock startaddr (endAddr (blockrange bentry))))
		  ) (memory s2) beqAddr |}
/\ s4 = {|
currentPartition := currentPartition s3;
memory := add newBlockEntryAddr
		(BE
		   (CBlockEntry (read bentry0) 
			  (write bentry0) (exec bentry0) 
			  (present bentry0) (accessible bentry0)
			  (blockindex bentry0)
			  (CBlock (startAddr (blockrange bentry0)) endaddr))
		  ) (memory s3) beqAddr |}
/\ s5 = {|
currentPartition := currentPartition s4;
memory := add newBlockEntryAddr
	   (BE
		  (CBlockEntry (read bentry1) 
			 (write bentry1) (exec bentry1) true
			 (accessible bentry1) (blockindex bentry1)
			 (blockrange bentry1))
		  ) (memory s4) beqAddr |}
/\ s6 = {|
currentPartition := currentPartition s5;
memory := add newBlockEntryAddr
		(BE
		   (CBlockEntry (read bentry2) (write bentry2) 
			  (exec bentry2) (present bentry2) true
			  (blockindex bentry2) (blockrange bentry2))
		  ) (memory s5) beqAddr |}
/\ s7 = {|
currentPartition := currentPartition s6;
memory := add newBlockEntryAddr
	   (BE
		  (CBlockEntry r (write bentry3) (exec bentry3)
			 (present bentry3) (accessible bentry3) 
			 (blockindex bentry3) (blockrange bentry3))
		  ) (memory s6) beqAddr |}
/\ s8 = {|
currentPartition := currentPartition s7;
memory := add newBlockEntryAddr
		  (BE
			 (CBlockEntry (read bentry4) w (exec bentry4) 
				(present bentry4) (accessible bentry4) 
				(blockindex bentry4) (blockrange bentry4))
		  ) (memory s7) beqAddr |}
/\ s9 = {|
currentPartition := currentPartition s8;
memory := add newBlockEntryAddr
	   (BE
		  (CBlockEntry (read bentry5) (write bentry5) e 
			 (present bentry5) (accessible bentry5) 
			 (blockindex bentry5) (blockrange bentry5))
		  ) (memory s8) beqAddr |}
/\ s10 = {|
currentPartition := currentPartition s9;
memory := add sceaddr 
						 (SCE {| origin := origin; next := next scentry |}
		  ) (memory s9) beqAddr |}
)
/\ (forall part pdentryPart parentsList, lookup part (memory s0) beqAddr = Some (PDT pdentryPart)
          -> isParentsList s parentsList part -> isParentsList s0 parentsList part)
/\ (forall part kernList, isListOfKernels kernList part s -> isListOfKernels kernList part s0))
}}.
Proof.
Admitted.

(*Lemma filterPresentIsPresent block s l:
In block (filterPresent l s)
-> In block l
   /\ exists blockBentry : BlockEntry,
      lookup block (memory s) beqAddr = Some (BE blockBentry) /\ present blockBentry = true.
Proof.
induction l.
- simpl. intuition.
- intro HisInFilter. simpl in HisInFilter. destruct (lookup a (memory s) beqAddr) eqn:Hlookupa.
  + destruct v eqn:Hlookupa2.
    * destruct (present b) eqn:Hpresentb.
      -- simpl in HisInFilter. destruct HisInFilter as [HisBlock | HisNotBlock].
         ++ split. simpl. left. assumption. exists b. subst a. intuition.
         ++ split. simpl. right. apply IHl. intuition. apply IHl. intuition.
      -- split. simpl. right. apply IHl. intuition. apply IHl. intuition.
    * split. simpl. right. apply IHl. intuition. apply IHl. intuition.
    * split. simpl. right. apply IHl. intuition. apply IHl. intuition.
    * split. simpl. right. apply IHl. intuition. apply IHl. intuition.
    * split. simpl. right. apply IHl. intuition. apply IHl. intuition.
  + split. simpl. right. apply IHl. intuition. apply IHl. intuition.
Qed.

Lemma presentIsInFilterPresent block s l :
In block l
-> (exists blockBentry : BlockEntry,
      lookup block (memory s) beqAddr = Some (BE blockBentry) /\ present blockBentry = true)
-> In block (filterPresent l s).
Proof.
induction l.
- simpl. intuition.
- intros HinList Hbentry. simpl in HinList.
  destruct HinList as [HisBlock | HinList].
  + subst a. simpl. destruct Hbentry as [blockBentry (HlookupBlock & HisPresent)]. rewrite HlookupBlock.
    rewrite HisPresent. intuition.
  + simpl. destruct (lookup a (memory s) beqAddr).
    * destruct v; try(apply IHl; assumption).
      destruct (present b); try(apply IHl; assumption).
      simpl. right. apply IHl; assumption.
    * apply IHl; assumption.
Qed.*)


(*Require Import insertNewEntry.*)

(** * Summary 
    This file contains the invariant of [addVaddr]. 
    We prove that this PIP service preserves the isolation property *)

Lemma cutMemoryBlock (idBlockToCut cutAddr : paddr) (MPURegionNb : index) :
{{fun s => partitionsIsolation s   /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s }} 
cutMemoryBlock idBlockToCut cutAddr MPURegionNb
{{fun _ s  => partitionsIsolation s   /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s }}.
Proof.
unfold cutMemoryBlock.
(** getCurPartition **)
eapply WP.bindRev.
eapply WP.weaken. 
apply Invariants.getCurPartition.
cbn.
intros.
(*destruct H as (HI&KI&VS&HC). apply (conj HI (conj KI VS)).*) apply H.
intro currentPart.
(** readPDNbFreeSlots *)
eapply WP.bindRev.
{
	eapply weaken.
-	apply Invariants.readPDNbFreeSlots.
- intros. simpl. split. apply H. intuition.
  unfold consistency in H4. unfold consistency1 in H4.
  subst currentPart. apply currentPartIsPDT; intuition.
}
	intro nbFreeSlots.
	eapply WP.bindRev. apply Invariants.Index.zero.

	intro zero.

	eapply bindRev.
{ (*MALInternal.Index.leb nbfreeslots zero *)
	eapply weaken. apply Invariants.Index.leb.
	intros. simpl. apply H.
}
	intro isFull.
	case_eq (isFull).
	{ (*case_eq isFull = false *)
		intros. eapply weaken. apply WP.ret.
		intros. simpl. intuition.
	}
	(*case_eq isFull = true *)
	intros.

(** findBlockInKSWithAddr **)
eapply WP.bindRev.
{
  eapply weaken.
  eapply findBlockInKSWithAddr.
  intros s Hprops.
  simpl. split. apply Hprops. (* ? *)
  intuition. unfold consistency in H8. unfold consistency1 in H8.
  subst currentPart. apply currentPartIsPDT; intuition.
}
intro blockToShareInCurrPartAddr.
(** compareAddrToNull **)
eapply WP.bindRev.
eapply Invariants.compareAddrToNull.
intro addrIsNull.
case_eq addrIsNull.
{intros. eapply WP.weaken.
  eapply WP.ret.
  simpl. intros.
  intuition. }

	intros. eapply bindRev.
{
	eapply weaken. apply readBlockAccessibleFromBlockEntryAddr. 
	intros. simpl. split. apply H1.
	unfold isBE. intuition.
  rewrite <-beqAddrFalse in H3. apply not_eq_sym in H3. contradiction.
  destruct H11. intuition.
	rewrite -> H11. trivial.

}
	intro addrIsAccessible.
	case_eq (addrIsAccessible).
	2 : { (*case_eq addrIsAccessible = false *)
		intros. simpl. eapply weaken. apply WP.ret.
		intros. simpl. intuition.
	}
	(*case_eq addrIsAccessible = true *)
	intros. simpl. eapply bindRev.
		{ eapply weaken. apply Invariants.readSh1PDChildFromBlockEntryAddr. intros.
			intros. simpl. split. apply H2. 
			intros. simpl.

			split. apply H2. destruct H2 ; destruct H2. destruct H2 ; destruct H5.
      intuition. rewrite <-beqAddrFalse in H4. apply not_eq_sym in H4. contradiction.
      destruct H13.

	 		exists x. apply H6.
 		}
		intro PDChildAddr.
(** compareAddrToNull **)
eapply WP.bindRev.
{ eapply weaken. apply Invariants.compareAddrToNull.
	intros. simpl. apply H2.
}
intro PDChildAddrIsNull.
case_eq PDChildAddrIsNull.
2 : {	(* PDChildAddrIsNull = false -> shared *) 
	intros. simpl. eapply WP.weaken.
  eapply WP.ret.
  simpl. intros.
  intuition.
}

	intros. simpl.
	(** readBlockStartFromBlockEntryAddr **)
	eapply bindRev.
{	eapply weaken. apply readBlockStartFromBlockEntryAddr.
	intros. simpl. split. apply H3.
	unfold isBE. intuition. rewrite <-beqAddrFalse in H8. apply not_eq_sym in H8. contradiction.
  destruct H16. intuition.
	rewrite -> H16. trivial.
}
	intro blockToCutStartAddr.
	eapply WP.bindRev.
{ eapply weaken. apply Invariants.Paddr.leb.
	intros. simpl. apply H3.
}
	intro isCutAddrBelowStart.
	case_eq (isCutAddrBelowStart).
{ (*case_eq isCutAddrBelowStart = true *)
		intros. simpl. eapply weaken. apply WP.ret.
		intros. simpl. intuition.
}
	(*case_eq isCutAddrBelowStart = false *)
	intros. simpl.
	eapply bindRev.
{	eapply weaken. apply readBlockEndFromBlockEntryAddr.
	intros. simpl. split. apply H4.
	unfold isBE. intuition.
  rewrite <-beqAddrFalse in H11. apply not_eq_sym in H11. contradiction.
  destruct H19. intuition. rewrite -> H19. trivial.
}
	intro blockToCutEndAddr.
	(* leb *)
	eapply WP.bindRev.
{ eapply weaken. apply Invariants.Paddr.leb.
	intros. simpl. apply H4.
}
	intro isCutAddrAboveEnd.
	case_eq (isCutAddrAboveEnd).
{ (*case_eq isCutAddrAboveEnd = true *)
		intros. simpl. eapply weaken. apply WP.ret.
		intros. simpl. intuition.
}
	(*case_eq isCutAddrAboveEnd = false *)
	intros. simpl.
	(** Paddr.subPaddr cutAddr blockToCutStartAddr **)
	eapply bindRev.
{	eapply weaken. apply Invariants.Paddr.subPaddr.
	intros. simpl. split. apply H5. split. lia. split. lia.
  assert(cutAddr <= maxIdx) by (rewrite maxIdxEqualMaxAddr; apply Hp). lia.
}
	intro subblock1Size.

	(** Paddr.subPaddr blockToCutEndAddr cutAddr **)
	eapply bindRev.
{	eapply weaken. apply Invariants.Paddr.subPaddr.
	intros. simpl. split. apply H5. split. lia. split. lia.
  assert(blockToCutEndAddr <= maxIdx) by (rewrite maxIdxEqualMaxAddr; apply Hp). lia.
}
	intro subblock2Size.
	(** getMinBlockSize **)
	eapply bindRev.
{	eapply weaken. apply Invariants.getMinBlockSize.
	intros. simpl. apply H5.
}
	intro minBlockSize.
	(* MALInternal.Index.ltb *)
	eapply bindRev.
{ eapply weaken. apply Invariants.Index.ltb.
	intros. simpl. apply H5.
}
	intro isBlock1TooSmall.
	(* MALInternal.Index.ltb *)
	eapply bindRev.
{ eapply weaken. apply Invariants.Index.ltb.
	intros. simpl. apply H5.
}
	intro isBlock2TooSmall.
	case_eq (isBlock1TooSmall || isBlock2TooSmall).
{	(* case_eq isBlock1TooSmall || isBlock2TooSmall = true *)
		intros. simpl. eapply weaken. apply WP.ret.
		intros. simpl. intuition.
}
	(*case_eq isCutAddrAboveEnd = false *)
	intros. simpl.
	(*check32Aligned *)
	eapply bindRev.
{ eapply weaken. apply check32Aligned.
	intros. simpl.
	split. apply H6. lia.
}
	intro isCutAddrValid.
	case_eq(negb isCutAddrValid).
{ (* case_eq negb isCutAddrValid = true *)
	intros. simpl. eapply weaken. apply WP.ret.
	intros. simpl. intuition.
}
	(*case_eq negb isCutAddrValid = false *)
	intros. simpl.
	eapply bindRev.
{ (* Internal.writeAccessibleToAncestorsIfNotCutRec *)
  eapply weaken. eapply writeAccessibleToAncestorsIfNotCutRec.
	intros s Hprops. simpl.
  assert(HcurrentPart: currentPartitionInPartitionsList s)
      by (unfold consistency in *; unfold consistency1 in *; intuition).
  assert(HPDflag: PDTIfPDFlag s)
      by (unfold consistency in *; unfold consistency1 in *; intuition).
  assert(HmultiPDT: multiplexerIsPDT s)
      by (unfold consistency in *; unfold consistency1 in *; intuition).
  assert(HcurrentIsPDT: isPDT (currentPartition s) s) by (apply currentPartIsPDT; intuition).
  assert(HcurrEq: currentPart = currentPartition s) by intuition.
  rewrite <- HcurrEq in *.
  assert(HpropsPlus: partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s
                    /\ currentPart = currentPartition s /\ pdentryNbFreeSlots currentPart nbFreeSlots s
                    /\ zero = CIndex 0 /\ false = StateLib.Index.leb nbFreeSlots zero
                    /\ (exists entry : BlockEntry,
                           lookup blockToShareInCurrPartAddr (memory s) beqAddr = Some (BE entry))
                    /\ blockToShareInCurrPartAddr = idBlockToCut
                    /\ bentryPFlag blockToShareInCurrPartAddr true s
                    /\ In blockToShareInCurrPartAddr (getMappedBlocks currentPart s)
                    /\ bentryAFlag blockToShareInCurrPartAddr true s
                    /\ (exists (sh1entry : Sh1Entry) (sh1entryaddr : paddr),
                         lookup sh1entryaddr (memory s) beqAddr = Some (SHE sh1entry) /\
                         sh1entryPDchild sh1entryaddr PDChildAddr s /\
                         sh1entryAddr blockToShareInCurrPartAddr sh1entryaddr s)
                    /\ beqAddr nullAddr PDChildAddr = true
                    /\ bentryStartAddr blockToShareInCurrPartAddr blockToCutStartAddr s
                    /\ false = StateLib.Paddr.leb cutAddr blockToCutStartAddr
                    /\ bentryEndAddr blockToShareInCurrPartAddr blockToCutEndAddr s
                    /\ false = StateLib.Paddr.leb blockToCutEndAddr cutAddr
                    /\ StateLib.Paddr.subPaddr cutAddr blockToCutStartAddr = Some subblock1Size
                    /\ StateLib.Paddr.subPaddr blockToCutEndAddr cutAddr = Some subblock2Size
                    /\ minBlockSize = Constants.minBlockSize
                    /\ isBlock1TooSmall = StateLib.Index.ltb subblock1Size minBlockSize
                    /\ isBlock2TooSmall = StateLib.Index.ltb subblock2Size minBlockSize
                    /\ isCutAddrValid = is32Aligned cutAddr
                    /\ isPDT currentPart s).
  {
    rewrite <-beqAddrFalse in *.
    assert(HbeqNullBlock: nullAddr <> blockToShareInCurrPartAddr) by intuition.
    assert(HBE: blockToShareInCurrPartAddr = nullAddr
                  \/ (exists entry,
                         lookup blockToShareInCurrPartAddr (memory s) beqAddr = Some (BE entry) /\
                         blockToShareInCurrPartAddr = idBlockToCut /\
                         bentryPFlag blockToShareInCurrPartAddr true s /\
                         In blockToShareInCurrPartAddr (getMappedBlocks currentPart s))) by intuition.
    destruct HBE as [Hcontra | HBE]; try(exfalso; congruence).
    destruct HBE as [bentry HpropsBE].
    assert(exists bentry, lookup blockToShareInCurrPartAddr (memory s) beqAddr = Some (BE bentry)).
    { exists bentry. intuition. }
    intuition; try(congruence).
  }
  split. intuition. split. intuition. split. intuition.
  split. apply HpropsPlus. split. intuition. apply isPDTLookupEq in HcurrentIsPDT.
  rewrite <-beqAddrFalse in *.
  assert(HcurrIsPart: currentPartitionInPartitionsList s)
        by (unfold consistency in *; unfold consistency1 in *; intuition).
  unfold currentPartitionInPartitionsList in HcurrIsPart. rewrite <-HcurrEq in HcurrIsPart.
  instantiate(1 := blockToCutEndAddr).
  instantiate(1 := blockToCutStartAddr). intuition; try(congruence).
}
	intro writeAccessibleToAncestorsIfNotCutRecCompleted. simpl.
	eapply bindRev.
{ (* MAL.readBlockEndFromBlockEntryAddr *)
	eapply weaken. apply readBlockEndFromBlockEntryAddr.
	intros s Hprops. simpl. split. apply Hprops. apply isBELookupEq.
  destruct Hprops as (HPI & HKDI & HVS & Hconsist & [s0 [pdentry [blokOrigin
          [blockNext [parentsList [statesList [blockBase [bentryBase [bentryBases0 Hprops]]]]]]]]]).
  assert(HBE: exists entry, lookup blockToShareInCurrPartAddr (memory s0) beqAddr = Some (BE entry)) by intuition.
  destruct HBE as [bentry Hlookup].
  assert(HBE: isBE blockToShareInCurrPartAddr s0) by (unfold isBE; rewrite Hlookup; trivial).
  assert(HBEs: isBE blockToShareInCurrPartAddr s).
  {
    apply stableBEIsBuilt with statesList s0 parentsList currentPart blockToCutStartAddr blockToCutEndAddr false;
      intuition.
  }
  apply isBELookupEq. assumption.
}
	intro blockEndAddr.
	eapply bindRev.
{ (* readSCOriginFromBlockEntryAddr *)
	eapply weaken. apply readSCOriginFromBlockEntryAddr.
	intros s Hprops. simpl. split. apply Hprops. split. intuition.
  destruct Hprops as ((HPI & HKDI & HVS & Hconsist & [s0 [pdentry [blokOrigin
          [blockNext [parentsList [statesList [blockBase [bentryBase [bentryBases0 Hprops]]]]]]]]]) & _).
  assert(HBE: exists entry, lookup blockToShareInCurrPartAddr (memory s0) beqAddr = Some (BE entry)) by intuition.
  destruct HBE as [bentry Hlookup].
  assert(HBE: isBE blockToShareInCurrPartAddr s0) by (unfold isBE; rewrite Hlookup; trivial).
  assert(HBEs: isBE blockToShareInCurrPartAddr s).
  {
    apply stableBEIsBuilt with statesList s0 parentsList currentPart blockToCutStartAddr blockToCutEndAddr false;
      intuition.
  }
  apply isBELookupEq. assumption.
}
	intro blockOrigin.
	eapply bindRev.
{ (* MAL.readBlockRFromBlockEntryAddr *)
	eapply weaken. apply readBlockRFromBlockEntryAddr.
	intros s Hprops. simpl. split. apply Hprops.
  destruct Hprops as (((HPI & HKDI & HVS & Hconsist & [s0 [pdentry [blokOrigin
          [blockNext [parentsList [statesList [blockBase [bentryBase [bentryBases0 Hprops]]]]]]]]]) & _) & _).
  assert(HBE: exists entry, lookup blockToShareInCurrPartAddr (memory s0) beqAddr = Some (BE entry)) by intuition.
  destruct HBE as [bentry Hlookup].
  assert(HBE: isBE blockToShareInCurrPartAddr s0) by (unfold isBE; rewrite Hlookup; trivial).
  apply stableBEIsBuilt with statesList s0 parentsList currentPart blockToCutStartAddr blockToCutEndAddr false;
    intuition.
}
	intro blockR.
	eapply bindRev.
{ (*MAL.readBlockWFromBlockEntryAddr *)
	eapply weaken. apply readBlockWFromBlockEntryAddr.
	intros s Hprops. simpl. split. apply Hprops.
  destruct Hprops as ((((HPI & HKDI & HVS & Hconsist & [s0 [pdentry [blokOrigin
          [blockNext [parentsList [statesList [blockBase [bentryBase [bentryBases0 Hprops]]]]]]]]]) & _) & _)
          & _).
  assert(HBE: exists entry, lookup blockToShareInCurrPartAddr (memory s0) beqAddr = Some (BE entry)) by intuition.
  destruct HBE as [bentry Hlookup].
  assert(HBE: isBE blockToShareInCurrPartAddr s0) by (unfold isBE; rewrite Hlookup; trivial).
  apply stableBEIsBuilt with statesList s0 parentsList currentPart blockToCutStartAddr blockToCutEndAddr false;
    intuition.
}
	intro blockW.
	eapply bindRev.
{ (* MAL.readBlockXFromBlockEntryAddr *)
	eapply weaken. apply readBlockXFromBlockEntryAddr.
	intros s Hprops. simpl. split. apply Hprops.
  destruct Hprops as (((((HPI & HKDI & HVS & Hconsist & [s0 [pdentry [blokOrigin [blockNext [parentsList
          [statesList [blockBase [bentryBase [bentryBases0 Hprops]]]]]]]]])
          & _) & _) & _) & _).
  assert(HBE: exists entry, lookup blockToShareInCurrPartAddr (memory s0) beqAddr = Some (BE entry)) by intuition.
  destruct HBE as [bentry Hlookup].
  assert(HBE: isBE blockToShareInCurrPartAddr s0) by (unfold isBE; rewrite Hlookup; trivial).
  apply stableBEIsBuilt with statesList s0 parentsList currentPart blockToCutStartAddr blockToCutEndAddr false;
    intuition.
}
	intro blockX.
	eapply bindRev.
{ (* Internal.insertNewEntry *)
	eapply weaken. apply insertNewEntry.
	intros s Hprops. simpl. pose proof Hprops as HpropsCopy.
  destruct Hprops as ((((((HPI & HKDI & HVS & Hconsist & [s0 [pdentry [blockOriginBis
      [blockNext [parentsList [statesList [blockBase [bentryBase [bentryBases0 Hprops]]]]]]]]]) &
      HendBlock) & Hscentry) & HRFlag) & HWFlag) & HXFlag). split. assumption. split.
  {
    assert(HlookupCurr: lookup currentPart (memory s) beqAddr = Some (PDT pdentry)) by intuition. exists pdentry.
    split. assumption.
    assert(HparentOfPart: parentOfPartitionIsPartition s)
        by (unfold consistency in *; unfold consistency1 in *; intuition).
    specialize(HparentOfPart currentPart pdentry HlookupCurr). destruct HparentOfPart as (HparentIsPart & _).
    assert(HblockEquivParent: blockInChildHasAtLeastEquivalentBlockInParent s)
        by (unfold consistency in *; unfold consistency1 in *; intuition).
    assert(HwellFormed: wellFormedBlock s) by (unfold consistency in *; unfold consistency1 in *; intuition).
    assert(Horigin: originIsParentBlocksStart s)
        by (unfold consistency in *; unfold consistency1 in *; intuition).
    assert(HcurrIsPart: In currentPart (getPartitions multiplexer s)).
    {
      assert(Hcurr: currentPart = currentPartition s0) by intuition.
      assert(HcurrEq: currentPartition s = currentPartition s0).
      {
        assert(HisBuilt: isBuiltFromWriteAccessibleRec s0 s statesList parentsList currentPart
            blockToCutStartAddr blockToCutEndAddr false) by intuition. revert HisBuilt.
        apply currentPartitionEqIsBuilt.
      }
      rewrite <-HcurrEq in Hcurr. assert(Hres: currentPartitionInPartitionsList s)
        by (unfold consistency in *; unfold consistency1 in *; intuition).
      unfold currentPartitionInPartitionsList in Hres. rewrite <-Hcurr in Hres. assumption.
    }
    assert(HeqTriv: (CPaddr (blockToShareInCurrPartAddr + scoffset))
                    = (CPaddr (blockToShareInCurrPartAddr + scoffset))) by reflexivity.
    assert(HblockMapped: In blockToShareInCurrPartAddr (getMappedBlocks currentPart s0)) by intuition.
    assert(HmappedEq: getMappedBlocks currentPart s = getMappedBlocks currentPart s0).
    {
      unfold consistency in *; unfold consistency1 in *; unfold consistency2 in *;
      apply getMappedBlocksEqBuiltWithWriteAcc with statesList parentsList blockToCutStartAddr
          blockToCutEndAddr currentPart false blockBase bentryBases0; intuition.
    }
    rewrite <-HmappedEq in HblockMapped.
    specialize(Horigin currentPart pdentry blockToShareInCurrPartAddr
        (CPaddr (blockToShareInCurrPartAddr + scoffset)) blockOrigin HcurrIsPart HlookupCurr HblockMapped
        HeqTriv Hscentry). destruct Horigin as (Horigin & HstartAbove).
    assert(Hstarts0: bentryStartAddr blockToShareInCurrPartAddr blockToCutStartAddr s0) by intuition.
    assert(Hstart: bentryStartAddr blockToShareInCurrPartAddr blockToCutStartAddr s).
    {
      unfold bentryStartAddr in Hstarts0.
      destruct (lookup blockToShareInCurrPartAddr (memory s0) beqAddr) eqn:HlookupBlocks0;
          try(exfalso; congruence). destruct v; try(exfalso; congruence).
      assert(HisBuilt: isBuiltFromWriteAccessibleRec s0 s statesList parentsList currentPart
          blockToCutStartAddr blockToCutEndAddr false) by intuition.
      pose proof (stableBEFieldsIsBuilt statesList s0 parentsList currentPart blockToCutStartAddr
          blockToCutEndAddr false s blockToShareInCurrPartAddr b HlookupBlocks0 HisBuilt) as Hres.
      destruct Hres as [bentrys (HlookupBlocks & _ & _ & _ & _ & _ & HrangeEq)].
      unfold bentryStartAddr. rewrite HlookupBlocks. rewrite HrangeEq. assumption.
    }
    specialize(HstartAbove blockToCutStartAddr Hstart).
    assert(HleCutStart: StateLib.Paddr.leb cutAddr blockToCutStartAddr = false) by intuition.
    unfold StateLib.Paddr.leb in HleCutStart. apply PeanoNat.Nat.leb_gt in HleCutStart.
    intro HcurrNotRoot. specialize(HparentIsPart HcurrNotRoot).
    destruct HparentIsPart as ([parentEntry HlookupParent] & HparentIsPart). split. unfold isPDT.
    rewrite HlookupParent. trivial.
    split.
    - intros addr HaddrInRange.
      assert(HaddrInParent: childPaddrIsIntoParent s) by (apply blockInclImpliesAddrIncl; assumption).
      unfold childPaddrIsIntoParent in HaddrInParent. apply HaddrInParent with currentPart. assumption.
      assert(HisChild: isChild s) by (unfold consistency in *; unfold consistency1 in *; intuition).
      unfold isChild in HisChild. apply HisChild.
      + assert(In currentPart (getPartitions multiplexer s0)) by intuition.
        assert(HgetPartsEq: getPartitions multiplexer s = getPartitions multiplexer s0).
        {
          unfold consistency in *; unfold consistency1 in *; unfold consistency2 in *; apply
              getPartitionsEqBuiltWithWriteAccInter with statesList parentsList blockToCutStartAddr
                blockToCutEndAddr currentPart false blockBase bentryBases0; intuition.
        }
        rewrite HgetPartsEq. assumption.
      + unfold pdentryParent. rewrite HlookupCurr. reflexivity.
      + assert(In addr (getAllPaddrAux [blockToShareInCurrPartAddr] s)).
        {
          simpl.  unfold bentryStartAddr in Hstarts0.
          destruct (lookup blockToShareInCurrPartAddr (memory s0) beqAddr) eqn:HlookupBlocks0;
              try(exfalso; congruence). destruct v; try(exfalso; congruence).
          assert(HisBuilt: isBuiltFromWriteAccessibleRec s0 s statesList parentsList currentPart
              blockToCutStartAddr blockToCutEndAddr false) by intuition.
          pose proof (stableBEFieldsIsBuilt statesList s0 parentsList currentPart blockToCutStartAddr
              blockToCutEndAddr false s blockToShareInCurrPartAddr b HlookupBlocks0 HisBuilt) as Hres.
          destruct Hres as [bentrys (HlookupBlocks & _ & _ & _ & _ & _ & HrangeEq)].
          unfold bentryEndAddr in HendBlock. rewrite HlookupBlocks in *. rewrite app_nil_r.
          rewrite <-HrangeEq in *. rewrite <-Hstarts0. rewrite <-HendBlock.
          apply getAllPaddrBlockInclRev in HaddrInRange.
          assert(HleCut: false = StateLib.Paddr.leb cutAddr blockToCutStartAddr) by intuition.
          unfold StateLib.Paddr.leb in HleCut. apply eq_sym in HleCut. apply PeanoNat.Nat.leb_gt in HleCut.
          assert(HleEnd: false = StateLib.Paddr.leb blockToCutEndAddr cutAddr) by intuition.
          unfold StateLib.Paddr.leb in HleEnd. apply eq_sym in HleEnd. apply PeanoNat.Nat.leb_gt in HleEnd.
          destruct HaddrInRange as (Hcut & Hend & Hbounds). apply getAllPaddrBlockIncl; lia.
        }
        apply addrInBlockIsMapped with blockToShareInCurrPartAddr; assumption.
    - assert(HcurrIsChild: In currentPart (getChildren (parent pdentry) s)).
      {
        assert(HisChild: isChild s) by (unfold consistency in *; unfold consistency1 in *; intuition).
        unfold isChild in HisChild. apply HisChild.
        assert(HgetPartsEq: getPartitions multiplexer s = getPartitions multiplexer s0).
        {
          unfold consistency in *; unfold consistency1 in *; unfold consistency2 in *; apply
              getPartitionsEqBuiltWithWriteAccInter with statesList parentsList blockToCutStartAddr
              blockToCutEndAddr currentPart false blockBase bentryBases0; intuition.
        }
        rewrite HgetPartsEq in *. intuition.
        unfold pdentryParent. rewrite HlookupCurr. reflexivity.
      }
      assert(HPFlags0: bentryPFlag blockToShareInCurrPartAddr true s0) by intuition.
      assert(HPFlag: bentryPFlag blockToShareInCurrPartAddr true s).
      {
        unfold bentryPFlag in HPFlags0.
        destruct (lookup blockToShareInCurrPartAddr (memory s0) beqAddr) eqn:HlookupBlocks0;
            try(exfalso; congruence). destruct v; try(exfalso; congruence).
        assert(HisBuilt: isBuiltFromWriteAccessibleRec s0 s statesList parentsList currentPart
            blockToCutStartAddr blockToCutEndAddr false) by intuition.
        pose proof (stableBEFieldsIsBuilt statesList s0 parentsList currentPart blockToCutStartAddr
            blockToCutEndAddr false s blockToShareInCurrPartAddr b HlookupBlocks0 HisBuilt) as Hres.
        destruct Hres as [bentrys (HlookupBlocks & _ & _ & _ & HpresEq & _)].
        unfold bentryPFlag. rewrite HlookupBlocks. rewrite HpresEq. assumption.
      }
      specialize(HblockEquivParent (parent pdentry) currentPart blockToShareInCurrPartAddr blockToCutStartAddr
          blockEndAddr HparentIsPart HcurrIsChild HblockMapped Hstart HendBlock HPFlag).
      destruct HblockEquivParent as [blockParent [startParent [endParent (HblockParentMapped & HstartParent &
          HendParent & HleStart & HleEnd)]]]. exists blockParent. exists endParent.
      specialize(Horigin HcurrNotRoot).
      destruct Horigin as [blockParentBis (HblockParentBisMapped & HstartParentBis & Hincl)].
      assert(HblocksEq: blockParent = blockParentBis).
      {
        destruct (beqAddr blockParent blockParentBis) eqn:HbeqBlocks; try(rewrite DTL.beqAddrTrue; assumption).
        exfalso. rewrite <-beqAddrFalse in HbeqBlocks.
        assert(HnoDup: noDupUsedPaddrList s) by (unfold consistency in *; unfold consistency2 in *; intuition).
        assert(HparentIsPDT: isPDT (parent pdentry) s).
        { unfold isPDT. rewrite HlookupParent. trivial. }
        assert(HstartInParent: In blockToCutStartAddr (getAllPaddrAux [blockParent] s)).
        {
          specialize(HwellFormed blockToShareInCurrPartAddr blockToCutStartAddr blockEndAddr HPFlag Hstart
            HendBlock).
          destruct HwellFormed as (HwellFormed & _).
          simpl. unfold bentryStartAddr in HstartParent. unfold bentryEndAddr in HendParent.
          destruct (lookup blockParent (memory s) beqAddr); try(simpl; congruence).
          destruct v; try(simpl; congruence).
          rewrite app_nil_r. rewrite <-HstartParent. rewrite <-HendParent. apply getAllPaddrBlockIncl; lia.
        }
        pose proof (DisjointPaddrInPart (parent pdentry) blockParent blockParentBis blockToCutStartAddr s HnoDup
          HparentIsPDT HblockParentMapped HblockParentBisMapped HbeqBlocks HstartInParent) as Hcontra.
        assert(HstartInBlock: In blockToCutStartAddr (getAllPaddrAux [blockToShareInCurrPartAddr] s)).
        {
          specialize(HwellFormed blockToShareInCurrPartAddr blockToCutStartAddr blockEndAddr HPFlag Hstart
              HendBlock).
          destruct HwellFormed as (HwellFormed & _).
          simpl. unfold bentryStartAddr in Hstart. unfold bentryEndAddr in HendBlock.
          destruct (lookup blockToShareInCurrPartAddr (memory s) beqAddr); try(simpl; congruence).
          destruct v; try(simpl; congruence).
          rewrite app_nil_r. rewrite <-Hstart. rewrite <-HendBlock. apply getAllPaddrBlockIncl; lia.
        }
        specialize(Hincl blockToCutStartAddr HstartInBlock). congruence.
      }
      subst blockParentBis. split. assumption. split. assumption. split. assumption. split; lia.
  }
  assert(Hs0: pdentryNbFreeSlots currentPart nbFreeSlots s0) by intuition.
  assert(HisBuilt: isBuiltFromWriteAccessibleRec s0 s statesList parentsList currentPart blockToCutStartAddr
         blockToCutEndAddr false) by intuition.
  assert(HleNbFree: false = StateLib.Index.leb nbFreeSlots zero) by intuition. unfold pdentryNbFreeSlots in *.
  destruct (lookup currentPart (memory s0) beqAddr) eqn:HlookupCurrs0; try(exfalso; congruence).
  assert(HbaseIsPDT: isPDT currentPart s0) by intuition. destruct v; try(exfalso; congruence).
  pose proof (stablePDTFieldsIsBuilt statesList s0 parentsList currentPart p blockToCutStartAddr
      blockToCutEndAddr false s currentPart HbaseIsPDT HisBuilt HlookupCurrs0) as HlookupCurrs.
  destruct HlookupCurrs as [pdentryCurrs (HlookupCurrs & _ & _ & HnbEq & _)]. rewrite <-HnbEq in Hs0.
  unfold StateLib.Index.leb in HleNbFree. apply eq_sym in HleNbFree.
  apply Compare_dec.leb_iff_conv in HleNbFree. split.
  {
    split. rewrite HlookupCurrs. assumption. lia.
  } split.
  {
    assert(HnbFreeIsLen: NbFreeSlotsISNbFreeSlotsInList s)
        by (unfold consistency in *; unfold consistency1 in *; intuition).
    assert(HcurrIsPDT: isPDT currentPart s) by (unfold isPDT; rewrite HlookupCurrs; trivial).
    assert(HnbFree: pdentryNbFreeSlots currentPart nbFreeSlots s)
        by (unfold pdentryNbFreeSlots; rewrite HlookupCurrs; assumption).
    specialize(HnbFreeIsLen currentPart nbFreeSlots HcurrIsPDT HnbFree).
    destruct HnbFreeIsLen as [optionfreeslotslist (Hlist & HwellFormedFree & HnbFreeIsLen)].
    subst optionfreeslotslist. unfold getFreeSlotsList in HnbFreeIsLen. rewrite HlookupCurrs in HnbFreeIsLen.
    destruct (beqAddr (firstfreeslot pdentryCurrs) nullAddr) eqn:HbeqFirstFreeNull;
        try(simpl in HnbFreeIsLen; lia). rewrite <-beqAddrFalse in HbeqFirstFreeNull.
    exists (firstfreeslot pdentryCurrs). split. apply lookupPDEntryFirstFreeSlot; intuition. assumption.
  } split; try(apply HpropsCopy).
  assert(HleEnd: false = StateLib.Paddr.leb blockToCutEndAddr cutAddr) by intuition.
  unfold StateLib.Paddr.leb in HleEnd. apply eq_sym in HleEnd. apply PeanoNat.Nat.leb_gt in HleEnd.
  assert(HendBlockBis: bentryEndAddr blockToShareInCurrPartAddr blockToCutEndAddr s).
  {
    assert(HendBlockBiss0: bentryEndAddr blockToShareInCurrPartAddr blockToCutEndAddr s0) by intuition.
    unfold bentryEndAddr in *.
    destruct (lookup blockToShareInCurrPartAddr (memory s0) beqAddr) eqn:HlookupBlocks0;
        try(exfalso; congruence). destruct v; try(exfalso; congruence).
    pose proof (stableBEFieldsIsBuilt statesList s0 parentsList currentPart blockToCutStartAddr blockToCutEndAddr
        false s blockToShareInCurrPartAddr b HlookupBlocks0 HisBuilt) as Hres.
    destruct Hres as [bentrys (HlookupBlocks & _ & _ & _ & _ & _ & HrangeEq)]. rewrite HlookupBlocks.
    rewrite HrangeEq. assumption.
  }
  assert(blockToCutEndAddr = blockEndAddr).
  {
    unfold bentryEndAddr in *.
    destruct (lookup blockToShareInCurrPartAddr (memory s) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). subst blockEndAddr. assumption.
  }
  subst blockToCutEndAddr. split. assumption.
  assert(Hbools: isBlock1TooSmall || isBlock2TooSmall = false) by assumption.
  apply orb_false_iff in Hbools. destruct Hbools.
  assert(Hsub: StateLib.Paddr.subPaddr blockEndAddr cutAddr = Some subblock2Size) by intuition.
  assert(Hmin: minBlockSize = Constants.minBlockSize) by intuition.
  assert(HltSub: isBlock2TooSmall = StateLib.Index.ltb subblock2Size minBlockSize) by intuition.
  subst isBlock2TooSmall. subst minBlockSize.
  unfold StateLib.Paddr.subPaddr in Hsub.
  destruct (Compare_dec.le_dec (blockEndAddr - cutAddr) maxIdx) eqn:HcompEndCut; try(congruence).
  injection Hsub as HsubBlock2. rewrite <-HsubBlock2 in HltSub.
  unfold StateLib.Index.ltb in HltSub. apply eq_sym in HltSub. apply PeanoNat.Nat.ltb_ge in HltSub.
  simpl in HltSub. lia.
}
	intro idNewSubblock.
	(* MALInternal.Paddr.pred *)
	(*eapply bindRev.
{ eapply weaken. apply Paddr.pred.
	intros s Hprops. simpl. split. apply Hprops. destruct Hprops as [s0 Hprops].
  destruct Hprops as (((((((_ & _ & _ & _ & [sInit [pdentry [pdbasepart [blockOriginBis [blockStart [blockEnd
      [blockNext [parentsList [statesList [blockBase [bentryBase [bentryBases0 Hprops]]]]]]]]]]]]) & _) & _) & _)
      & _) & _) & _).
  assert(Hle: false = StateLib.Paddr.leb cutAddr blockToCutStartAddr) by intuition.
  unfold StateLib.Paddr.leb in Hle. apply eq_sym in Hle. apply Compare_dec.leb_iff_conv in Hle. lia.
}
	intro predCutAddr.*) simpl.
	(* MAL.writeBlockEndFromBlockEntryAddr *)
	eapply bindRev.
{	eapply weaken. apply writeBlockEndFromBlockEntryAddr.
	intros s Hprops. simpl. (*destruct Hprops as [Hprops HpredCutAddr].*) destruct Hprops as [s0 Hprops].
  destruct Hprops as (Hprops1 & Hconsist & (Hprops2 & HparentsLists & HkernLists)).
  destruct Hprops2 as [pdentry Hprops]. destruct Hprops as [pdentry0 Hprops].
  destruct Hprops as [pdentry1 Hprops].
  destruct Hprops as [bentry Hprops]. destruct Hprops as [bentry0 Hprops]. destruct Hprops as [bentry1 Hprops].
  destruct Hprops as [bentry2 Hprops]. destruct Hprops as [bentry3 Hprops]. destruct Hprops as [bentry4 Hprops].
  destruct Hprops as [bentry5 Hprops]. destruct Hprops as [bentry6 Hprops]. destruct Hprops as [sceaddr Hprops].
  destruct Hprops as [scentry Hprops]. destruct Hprops as [newBlockEntryAddr Hprops].
  destruct Hprops as [newFirstFreeSlotAddr Hprops]. destruct Hprops as [predCurrentNbFreeSlots Hprops].
  destruct Hprops as [Hs Hprops].
  destruct Hprops1 as ((((((HPI & HKDI & HVS & Hconsists0 & [sInit [pdentryCurr [blockOriginBis
      [blockNext [parentsList [statesList [blockBase [bentryBase [bentryBases0
      Hprops1]]]]]]]]]) & HendAddr) & HsceOrigin) & HRFlag) & HWFlag) & HXFlag).
  assert(HlookupBlock: exists entry, lookup blockToShareInCurrPartAddr (memory sInit) beqAddr = Some (BE entry))
      by intuition.
  destruct HlookupBlock as [bentryShareInit HlookupBlockInit].
  assert(HisBuilt: isBuiltFromWriteAccessibleRec sInit s0 statesList parentsList currentPart blockToCutStartAddr
      blockToCutEndAddr false) by intuition.
  pose proof (stableBEFieldsIsBuilt statesList sInit parentsList currentPart blockToCutStartAddr
      blockToCutEndAddr false s0 blockToShareInCurrPartAddr bentryShareInit HlookupBlockInit HisBuilt) as Hres.
  destruct Hres as [bentryShare (HlookupBlocks0 & HpropsShare)]. exists bentryShare.
  assert(HblockToShareNotNull: blockToShareInCurrPartAddr <> nullAddr).
  {
    assert(Hnull: nullAddrExists s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
    unfold nullAddrExists in Hnull. unfold isPADDR in Hnull.
    intro HcontraEq. rewrite HcontraEq in *. rewrite HlookupBlocks0 in *. congruence.
  }
	assert(HlookupCurrParts0 : lookup currentPart (memory s0) beqAddr = Some (PDT pdentry)) by intuition.
  assert(HbaseIsPDT: isPDT currentPart sInit) by intuition.
  pose proof (stablePDTFieldsIsBuiltRev statesList sInit parentsList currentPart pdentry blockToCutStartAddr
      blockToCutEndAddr false s0 currentPart HbaseIsPDT HisBuilt HlookupCurrParts0) as HlookupCurrPartsInit.
  destruct HlookupCurrPartsInit as [pdentryInit (HlookupCurrPartsInit & HstructEq & HfirstFreeEq & HnbFreeEq &
      HnbPrepEq & HparentEq & HvidtEq)].
  assert(HfreeSlot: isBE (firstfreeslot pdentryInit) sInit /\ isFreeSlot (firstfreeslot pdentry) sInit).
  {
    assert(HFirstFreeSlotPointerIsBEAndFreeSlot : FirstFreeSlotPointerIsBEAndFreeSlot sInit)
				by (unfold consistency in * ; unfold consistency1 in * ; intuition).
		unfold FirstFreeSlotPointerIsBEAndFreeSlot in *.
		specialize(HFirstFreeSlotPointerIsBEAndFreeSlot currentPart pdentryInit HlookupCurrPartsInit).
		assert(HfirstfreeNotNull : firstfreeslot pdentry <> nullAddr).
		{
			assert(HfirstfreecurrParts0 : pdentryFirstFreeSlot currentPart newBlockEntryAddr s0 /\
             beqAddr nullAddr newBlockEntryAddr = false).
      {
        split. intuition. destruct (beqAddr nullAddr newBlockEntryAddr) eqn:HbeqNullNewB; try(reflexivity).
        exfalso. rewrite <-DTL.beqAddrTrue in HbeqNullNewB. subst newBlockEntryAddr.
        assert(Hcontra: lookup nullAddr (memory s0) beqAddr = Some (BE bentry)) by intuition.
        assert(Hnull: nullAddrExists s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
        unfold nullAddrExists in Hnull. unfold isPADDR in Hnull. rewrite Hcontra in Hnull. congruence.
      }
			unfold pdentryFirstFreeSlot in *. rewrite HlookupCurrParts0 in *.
			rewrite <- beqAddrFalse in *.
			destruct HfirstfreecurrParts0 as [HfirstfreeEq HfirstFreeNotNull].
			subst newBlockEntryAddr. congruence.
		}
		rewrite <-HfirstFreeEq in *. specialize (HFirstFreeSlotPointerIsBEAndFreeSlot HfirstfreeNotNull).
    assumption.
  }
  destruct HfreeSlot as (HBEs0 & HfreeSlot).
	assert(HnewBlockToShareEq : newBlockEntryAddr <> blockToShareInCurrPartAddr).
	{
    intro HcontraEq. rewrite <-HfirstFreeEq in *.
		assert(HnewBEq : firstfreeslot pdentryInit = newBlockEntryAddr)
		      by (apply eq_sym; intuition). rewrite HnewBEq in *.
		subst blockToShareInCurrPartAddr.
		assert(HwellFormedsh1newBs0 : wellFormedFstShadowIfBlockEntry sInit)
			  by (unfold consistency in * ; unfold consistency1 in * ; intuition).
		unfold wellFormedFstShadowIfBlockEntry in *.
		assert(HwellFormedSCnewBs0 : wellFormedShadowCutIfBlockEntry sInit)
		    by (unfold consistency in * ; unfold consistency1 in * ; intuition).
		unfold wellFormedShadowCutIfBlockEntry in *.
		specialize (HwellFormedsh1newBs0 newBlockEntryAddr HBEs0).
		specialize (HwellFormedSCnewBs0 newBlockEntryAddr HBEs0).
		unfold isSHE in *. unfold isSCE in *.
		unfold isFreeSlot in *.
		unfold bentryAFlag in *.
		rewrite HlookupBlockInit in *.
		destruct (lookup (CPaddr (newBlockEntryAddr + sh1offset)) (memory sInit) beqAddr) eqn:Hsh1
            ; try(exfalso ; congruence).
		destruct v ; try(exfalso ; congruence).
		destruct HwellFormedSCnewBs0 as [scentryaddr (HSCEs0 & HscentryEq)].
		subst scentryaddr.
		destruct (lookup (CPaddr (newBlockEntryAddr + scoffset))  (memory sInit) beqAddr) eqn:Hsce
            ; try(exfalso ; congruence).
		destruct v ; try(exfalso ; congruence). assert(Hcontra: true = accessible bentryShareInit) by intuition.
    apply eq_sym in Hcontra. assert(accessible bentryShareInit = false) by intuition. congruence.
	}
	assert(HnewFirstFreeBlockToShareEq : newFirstFreeSlotAddr <> blockToShareInCurrPartAddr).
	{
		(* at s0, newFirstFreeSlotAddr is a free slot, which is not the case of
				blockToShareInCurrPartAddr *)
		assert(HFirstFreeSlotPointerIsBEAndFreeSlot : FirstFreeSlotPointerIsBEAndFreeSlot s)
				by (unfold consistency1 in * ; intuition).
		unfold FirstFreeSlotPointerIsBEAndFreeSlot in *.
		assert(HlookupcurrParts : lookup currentPart (memory s) beqAddr = Some (PDT pdentry1)) by intuition.
		specialize(HFirstFreeSlotPointerIsBEAndFreeSlot currentPart pdentry1 HlookupcurrParts).
    intro HcontraEq.
		assert(HfirstfreeNotNull : firstfreeslot pdentry1 <> nullAddr).
		{
			assert(HfirstfreecurrParts : pdentryFirstFreeSlot currentPart newFirstFreeSlotAddr s /\
             beqAddr nullAddr newFirstFreeSlotAddr = false).
      {
        split. unfold pdentryFirstFreeSlot. rewrite HlookupcurrParts. intuition. rewrite <-beqAddrFalse.
        rewrite HcontraEq. apply not_eq_sym. assumption.
      }
			unfold pdentryFirstFreeSlot in *. rewrite HlookupcurrParts in *.
			rewrite <- beqAddrFalse in *.
			destruct HfirstfreecurrParts as [HfirstfreeEq HfirstFreeNotNull].
			subst newFirstFreeSlotAddr. congruence.
		}
		specialize (HFirstFreeSlotPointerIsBEAndFreeSlot HfirstfreeNotNull).
		assert(HnewBEq : firstfreeslot pdentry1 = newFirstFreeSlotAddr)
		      by (apply eq_sym; intuition).
		rewrite HnewBEq in *.
		(* newB is a free slot, so its accessible flag is false
				blockToShareInCurrPartAddr is not a free slot,
				so the equality is a constradiction*)
		subst blockToShareInCurrPartAddr.
		assert(HwellFormedsh1newBs : wellFormedFstShadowIfBlockEntry s)
			  by (unfold consistency1 in * ; intuition).
		unfold wellFormedFstShadowIfBlockEntry in *.
		assert(HwellFormedSCnewBs : wellFormedShadowCutIfBlockEntry s)
		    by (unfold consistency1 in * ; intuition).
		unfold wellFormedShadowCutIfBlockEntry in *.
		assert(HBEs : isBE newFirstFreeSlotAddr s) by intuition.
		specialize (HwellFormedsh1newBs newFirstFreeSlotAddr HBEs).
		specialize (HwellFormedSCnewBs newFirstFreeSlotAddr HBEs).
		unfold isBE in *. unfold isSHE in *. unfold isSCE in *.
		unfold isFreeSlot in HFirstFreeSlotPointerIsBEAndFreeSlot.
		unfold bentryPFlag in *. rewrite HlookupBlockInit in Hprops1.
		destruct (lookup newFirstFreeSlotAddr (memory s) beqAddr) eqn:Hbe ; try(exfalso ; congruence).
		destruct v ; try(exfalso ; congruence).
		destruct (lookup (CPaddr (newFirstFreeSlotAddr + sh1offset)) (memory s) beqAddr) eqn:Hsh1
              ; try(exfalso ; congruence).
		destruct v ; try(exfalso ; congruence).
		destruct HwellFormedSCnewBs as [scentryaddr (HSCEs0 & HscentryEq)].
		subst scentryaddr.
		destruct (lookup (CPaddr (newFirstFreeSlotAddr + scoffset))  (memory s) beqAddr) eqn:Hsce
              ; try(exfalso ; congruence).
		destruct v ; try(exfalso ; congruence). assert(Hcontra: true = present bentryShareInit) by intuition.
    assert(HlookupnewFirstEq: lookup newFirstFreeSlotAddr (memory s) beqAddr
                              = lookup newFirstFreeSlotAddr (memory s0) beqAddr).
    {
      rewrite Hs. simpl. rewrite InternalLemmas.beqAddrTrue.
      destruct (beqAddr sceaddr newFirstFreeSlotAddr) eqn:HbeqSceaddrNewFirstFree.
      {
        rewrite <-beqAddrTrue in HbeqSceaddrNewFirstFree. rewrite HbeqSceaddrNewFirstFree in *.
        unfold isSCE in *. rewrite Hbe in *. intuition.
      }
      rewrite <-beqAddrFalse in HbeqSceaddrNewFirstFree.
      destruct (beqAddr newBlockEntryAddr sceaddr) eqn:HbeqnewBlockSceaddr.
      {
        rewrite <-beqAddrTrue in HbeqnewBlockSceaddr. rewrite HbeqnewBlockSceaddr in *.
        unfold isSCE in *. intuition.
      }
      rewrite <-beqAddrFalse in HbeqnewBlockSceaddr. simpl.
      destruct (beqAddr newBlockEntryAddr newFirstFreeSlotAddr) eqn:HbeqNewBlockNewFirstFree.
      rewrite <-beqAddrTrue in HbeqNewBlockNewFirstFree. congruence.
      destruct (beqAddr currentPart newBlockEntryAddr) eqn: HbeqCurrPartNewBlock.
      rewrite <-beqAddrTrue in HbeqCurrPartNewBlock. intuition. rewrite <-beqAddrFalse in *.
      repeat rewrite removeDupIdentity; try(apply not_eq_sym; assumption). simpl.
      destruct (beqAddr currentPart newFirstFreeSlotAddr) eqn:HbeqCurrPartNewFirstFree.
      rewrite <-beqAddrTrue in HbeqCurrPartNewFirstFree. congruence.
      rewrite InternalLemmas.beqAddrTrue. repeat rewrite removeDupIdentity; intuition.
    }
    rewrite <-HlookupnewFirstEq in HlookupBlocks0. rewrite Hbe in HlookupBlocks0.
    injection HlookupBlocks0 as HentriesEq. subst b. rewrite HlookupnewFirstEq in Hbe.
    pose proof (stableBEFieldsIsBuiltRev statesList sInit parentsList currentPart blockToCutStartAddr
          blockToCutEndAddr false s0 newFirstFreeSlotAddr bentryShare Hbe HisBuilt) as HbentryInit.
    destruct HbentryInit as [bentryShareInitBis (HlookupNewFirstBis & _ & _ & _ & HpresEq & _)].
    rewrite HlookupNewFirstBis in HlookupBlockInit. injection HlookupBlockInit as HentriesEq.
    subst bentryShareInitBis. rewrite HpresEq in Hcontra. assert(present bentryShare = false) by intuition.
    congruence.
	}
  assert(HblockToShareCurrPartEq: blockToShareInCurrPartAddr <> currentPart).
  {
    intro HbeqBlockToShareCurrPart. rewrite HbeqBlockToShareCurrPart in *. unfold isPDT in *.
    rewrite HlookupBlockInit in HlookupCurrPartsInit. congruence.
  }
  assert(blockToShareInCurrPartAddr <> sceaddr).
  {
    intro HcontraEq. rewrite HcontraEq in *. unfold isSCE in *. rewrite HlookupBlocks0 in *. intuition.
  }
  split.
  - rewrite Hs. simpl. rewrite InternalLemmas.beqAddrTrue.
    (* check all possible equalities *)
    destruct (beqAddr sceaddr blockToShareInCurrPartAddr) eqn:HbeqSceBlock.
    { rewrite <-beqAddrTrue in HbeqSceBlock. exfalso. intuition. }
    destruct Hprops as [HnewBlockIdEq (HlookupNew0 & Hprops)].
    destruct (beqAddr newBlockEntryAddr sceaddr) eqn:HbeqnewBlockSce.
    { rewrite <-beqAddrTrue in HbeqnewBlockSce. exfalso. intuition. }
    rewrite <-beqAddrFalse in HbeqnewBlockSce. simpl.
    destruct (beqAddr newBlockEntryAddr blockToShareInCurrPartAddr) eqn:HbeqNewBlockToShare.
    + rewrite <-beqAddrTrue in HbeqNewBlockToShare. congruence.
    + rewrite <-beqAddrFalse in *.
      repeat rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      destruct (beqAddr currentPart newBlockEntryAddr) eqn:HbeqCurrNewBlock.
      {
        rewrite <-beqAddrTrue in HbeqCurrNewBlock. rewrite HbeqCurrNewBlock in *. unfold isPDT in *.
        rewrite HlookupNew0 in *. congruence.
      }
      rewrite <-beqAddrFalse in HbeqCurrNewBlock. simpl.
      destruct (beqAddr currentPart blockToShareInCurrPartAddr) eqn:HbeqCurrBlockToShare.
      {
        rewrite <-beqAddrTrue in HbeqCurrBlockToShare. rewrite HbeqCurrBlockToShare in *. unfold isPDT in *.
        rewrite HlookupBlocks0 in *. congruence.
      }
      rewrite <-beqAddrFalse in HbeqCurrBlockToShare. rewrite InternalLemmas.beqAddrTrue.
      repeat rewrite removeDupIdentity; intuition.
  - instantiate(1:= fun _ s => isBE idNewSubblock s
        (*/\ StateLib.Paddr.pred cutAddr = Some predCutAddr*)
        /\ zero = CIndex 0
        /\ false = StateLib.Index.leb nbFreeSlots zero
        /\ beqAddr nullAddr PDChildAddr = true
        /\ false = StateLib.Paddr.leb cutAddr blockToCutStartAddr
        /\ false = StateLib.Paddr.leb blockToCutEndAddr cutAddr
        /\ StateLib.Paddr.subPaddr cutAddr blockToCutStartAddr = Some subblock1Size
        /\ StateLib.Paddr.subPaddr blockToCutEndAddr cutAddr = Some subblock2Size
        /\ minBlockSize = Constants.minBlockSize
        /\ isBlock1TooSmall = StateLib.Index.ltb subblock1Size minBlockSize
        /\ isBlock2TooSmall = StateLib.Index.ltb subblock2Size minBlockSize
        /\ isCutAddrValid = is32Aligned cutAddr
        /\ exists s0 s1, exists pdentry pdentryInter0 pdentryInter1 newpdentry: PDTable,
           exists bentry bentry0 bentry1 bentry2 bentry3 bentry4 bentry5 bentry6 bentryShare bentry7: BlockEntry,
           exists scentry: SCEntry, exists predCurrentNbFreeSlots: index,
           exists sceaddr newFirstFreeSlotAddr: paddr,
           s =
           {|
             currentPartition := currentPartition s0;
             memory :=
               add blockToShareInCurrPartAddr
               (BE
                  (CBlockEntry (read bentryShare) (write bentryShare) (exec bentryShare)
                    (present bentryShare) (accessible bentryShare) (blockindex bentryShare)
                    (CBlock (startAddr (blockrange bentryShare)) cutAddr)))
                      (memory s1) beqAddr
           |}
           /\ lookup idNewSubblock (memory s0) beqAddr = Some (BE bentry)
           /\ lookup idNewSubblock (memory s) beqAddr = Some (BE bentry6)
           /\ lookup blockToShareInCurrPartAddr (memory s0) beqAddr = Some (BE bentryShare)
           /\ lookup blockToShareInCurrPartAddr (memory s1) beqAddr = Some (BE bentryShare)
           /\ lookup blockToShareInCurrPartAddr (memory s) beqAddr = Some (BE bentry7)
           /\ bentry7 = CBlockEntry (read bentryShare) (write bentryShare) (exec bentryShare)
                        (present bentryShare) (accessible bentryShare) (blockindex bentryShare)
                        (CBlock (startAddr (blockrange bentryShare)) cutAddr)
           /\ bentry6 = CBlockEntry (read bentry5) (write bentry5) blockX (present bentry5)
                        (accessible bentry5) (blockindex bentry5) (blockrange bentry5)
           /\ bentry5 = CBlockEntry (read bentry4) blockW (exec bentry4) (present bentry4)
                        (accessible bentry4) (blockindex bentry4) (blockrange bentry4)
           /\ bentry4 = CBlockEntry blockR (write bentry3) (exec bentry3) (present bentry3)
                        (accessible bentry3) (blockindex bentry3) (blockrange bentry3)
           /\ bentry3 = CBlockEntry (read bentry2) (write bentry2) (exec bentry2) (present bentry2) true
                        (blockindex bentry2) (blockrange bentry2)
           /\ bentry2 = CBlockEntry (read bentry1) (write bentry1) (exec bentry1) true (accessible bentry1)
                        (blockindex bentry1) (blockrange bentry1)
           /\ bentry1 = CBlockEntry (read bentry0) (write bentry0) (exec bentry0) (present bentry0)
                        (accessible bentry0) (blockindex bentry0)
                        (CBlock (startAddr (blockrange bentry0)) blockEndAddr)
           /\ bentry0 = CBlockEntry (read bentry) (write bentry) (exec bentry) (present bentry) 
                        (accessible bentry) (blockindex bentry) (CBlock cutAddr (endAddr (blockrange bentry)))
           /\ beqAddr idNewSubblock blockToShareInCurrPartAddr = false
           /\ sceaddr = CPaddr ((firstfreeslot pdentry) + scoffset)
           /\ lookup sceaddr (memory s0) beqAddr = Some (SCE scentry)
           /\ lookup currentPart (memory s0) beqAddr = Some (PDT pdentry)
           /\ lookup currentPart (memory s) beqAddr = Some (PDT newpdentry)
           /\ newpdentry = pdentryInter1
           /\ pdentryInter1 =
              {|
                structure := structure pdentryInter0;
                firstfreeslot := firstfreeslot pdentryInter0;
                nbfreeslots := predCurrentNbFreeSlots;
                nbprepare := nbprepare pdentryInter0;
                parent := parent pdentryInter0;
                MPU := MPU pdentryInter0;
                vidtAddr := vidtAddr pdentryInter0
              |}
           /\ pdentryInter0 =
              {|
                structure := structure pdentry;
                firstfreeslot := newFirstFreeSlotAddr;
                nbfreeslots := nbfreeslots pdentry;
                nbprepare := nbprepare pdentry;
                parent := parent pdentry;
                MPU := MPU pdentry;
                vidtAddr := vidtAddr pdentry
              |}
           /\ kernelDataIsolation s0 /\ verticalSharing s0 /\ partitionsIsolation s0 /\ consistency s0
           /\ currentPart = currentPartition s0
           /\ isPDT currentPart s0
           /\ consistency1 s1 /\ isPDT currentPart s
           /\ pdentryNbFreeSlots currentPart nbFreeSlots s0
           /\ bentryXFlag blockToShareInCurrPartAddr blockX s0
           /\ bentryWFlag blockToShareInCurrPartAddr blockW s0
           /\ bentryRFlag blockToShareInCurrPartAddr blockR s0
           /\ scentryOrigin (CPaddr (blockToShareInCurrPartAddr + scoffset)) blockOrigin s0
           /\ bentryEndAddr blockToShareInCurrPartAddr blockEndAddr s0
           /\ bentryAFlag blockToShareInCurrPartAddr true s0
           /\ bentryAFlag blockToShareInCurrPartAddr true s
           /\ (exists (sh1entry : Sh1Entry) (sh1entryaddr : paddr),
                lookup sh1entryaddr (memory s0) beqAddr = Some (SHE sh1entry) /\
                sh1entryPDchild sh1entryaddr PDChildAddr s0 /\
                sh1entryAddr blockToShareInCurrPartAddr sh1entryaddr s0)
           /\ beqAddr nullAddr PDChildAddr = true
           /\ bentryStartAddr blockToShareInCurrPartAddr blockToCutStartAddr s0
           /\ bentryEndAddr blockToShareInCurrPartAddr blockToCutEndAddr s0
           /\ bentryPFlag blockToShareInCurrPartAddr true s0
           /\ In blockToShareInCurrPartAddr (getMappedBlocks currentPart s0)
           /\ pdentryFirstFreeSlot currentPart idNewSubblock s0
           /\ bentryEndAddr (firstfreeslot pdentry) newFirstFreeSlotAddr s0
           /\ pdentryNbFreeSlots currentPart predCurrentNbFreeSlots s
           /\ StateLib.Index.pred nbFreeSlots = Some predCurrentNbFreeSlots
           /\ blockindex bentry6 = blockindex bentry5
           /\ blockindex bentry5 = blockindex bentry4
           /\ blockindex bentry4 = blockindex bentry3
           /\ blockindex bentry3 = blockindex bentry2
           /\ blockindex bentry2 = blockindex bentry1
           /\ blockindex bentry1 = blockindex bentry0
           /\ blockindex bentry0 = blockindex bentry
           /\ isBE (firstfreeslot pdentry) s0
           /\ isBE (firstfreeslot pdentry) s
           /\ isSCE sceaddr s0
           /\ isSCE sceaddr s
           /\ sceaddr = CPaddr (idNewSubblock + scoffset)
           /\ firstfreeslot newpdentry = newFirstFreeSlotAddr
           /\ (newFirstFreeSlotAddr = currentPart -> False)
           /\ (currentPart = (firstfreeslot pdentry) -> False)
           /\ (newFirstFreeSlotAddr = (firstfreeslot pdentry) -> False)
           /\ (sceaddr = (firstfreeslot pdentry) -> False)
           /\ (sceaddr = currentPart -> False)
           /\ (sceaddr = newFirstFreeSlotAddr -> False)
           /\ ((firstfreeslot pdentry) = blockToShareInCurrPartAddr -> False)
           /\ (blockToShareInCurrPartAddr = currentPart -> False)
           /\ (forall blockInParentPartitionAddr,
                In blockInParentPartitionAddr (getMappedBlocks (parent pdentry) s0)
                -> bentryStartAddr blockInParentPartitionAddr blockToCutStartAddr s0
                -> bentryEndAddr blockInParentPartitionAddr blockToCutEndAddr s0
                -> bentryAFlag blockInParentPartitionAddr false s0)
           (* intermediate steps *)
           /\ s1 =
              {|
                currentPartition := currentPartition s0;
                memory :=
                    add sceaddr (SCE {| origin := blockOrigin; next := next scentry |})
                       (add idNewSubblock
                          (BE
                             (CBlockEntry (read bentry5) (write bentry5) blockX (present bentry5)
                                (accessible bentry5) (blockindex bentry5) (blockrange bentry5)))
                          (add idNewSubblock
                             (BE
                                (CBlockEntry (read bentry4) blockW (exec bentry4) (present bentry4)
                                   (accessible bentry4) (blockindex bentry4) (blockrange bentry4)))
                             (add idNewSubblock
                                (BE
                                   (CBlockEntry blockR (write bentry3) (exec bentry3) 
                                      (present bentry3) (accessible bentry3) (blockindex bentry3)
                                      (blockrange bentry3)))
                                (add idNewSubblock
                                   (BE
                                      (CBlockEntry (read bentry2) (write bentry2) (exec bentry2)
                                         (present bentry2) true (blockindex bentry2) 
                                         (blockrange bentry2)))
                                   (add idNewSubblock
                                      (BE
                                         (CBlockEntry (read bentry1) (write bentry1) 
                                            (exec bentry1) true (accessible bentry1) 
                                            (blockindex bentry1) (blockrange bentry1)))
                                      (add idNewSubblock
                                         (BE
                                            (CBlockEntry (read bentry0) (write bentry0) 
                                               (exec bentry0) (present bentry0) (accessible bentry0)
                                               (blockindex bentry0)
                                               (CBlock (startAddr (blockrange bentry0)) blockEndAddr)))
                                         (add idNewSubblock
                                            (BE
                                               (CBlockEntry (read bentry) (write bentry) 
                                                  (exec bentry) (present bentry) (accessible bentry)
                                                  (blockindex bentry)
                                                  (CBlock cutAddr (endAddr (blockrange bentry)))))
                                            (add currentPart
                                               (PDT
                                                  {|
                                                    structure := structure pdentryInter0;
                                                    firstfreeslot := firstfreeslot pdentryInter0;
                                                    nbfreeslots := predCurrentNbFreeSlots;
                                                    nbprepare := nbprepare pdentryInter0;
                                                    parent := parent pdentryInter0;
                                                    MPU := MPU pdentryInter0;
                                                    vidtAddr := vidtAddr pdentryInter0
                                                  |})
                                               (add currentPart
                                                  (PDT
                                                     {|
                                                       structure := structure pdentry;
                                                       firstfreeslot := newFirstFreeSlotAddr;
                                                       nbfreeslots := nbfreeslots pdentry;
                                                       nbprepare := nbprepare pdentry;
                                                       parent := parent pdentry;
                                                       MPU := MPU pdentry;
                                                       vidtAddr := vidtAddr pdentry
                                                     |}) (memory s0) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr)
                             beqAddr) beqAddr) beqAddr) beqAddr) beqAddr
              |}
           /\ sh1entryPDflag (CPaddr (blockToShareInCurrPartAddr + sh1offset)) false s1
           /\ sh1entryPDflag (CPaddr (blockToShareInCurrPartAddr + sh1offset)) false s
           /\ exists (optionfreeslotslist : list optionPaddr) (s2 : state) (n0 n1 n2 : nat) (nbleft : index),
                nbleft = CIndex (nbFreeSlots - 1) /\ nbleft < maxIdx
                /\ s1 =
                  {|
                    currentPartition := currentPartition s0;
                    memory :=
                      add sceaddr (SCE {| origin := blockOrigin; next := next scentry |}) 
                        (memory s2) beqAddr
                  |}
                /\ optionfreeslotslist = getFreeSlotsListRec n1 newFirstFreeSlotAddr s2 nbleft
                (*/\ getFreeSlotsListRec n2 newFirstFreeSlotAddr s nbleft = optionfreeslotslist*)
                /\ getFreeSlotsListRec n2 newFirstFreeSlotAddr s1 nbleft = optionfreeslotslist
                /\ optionfreeslotslist = getFreeSlotsListRec n0 newFirstFreeSlotAddr s0 nbleft
                /\ n0 <= n1 /\ nbleft < n0 /\ n1 <= n2 /\ nbleft < n2 /\ n2 <= maxIdx + 1
                /\ (wellFormedFreeSlotsList optionfreeslotslist = False -> False)
                /\ NoDup (filterOptionPaddr optionfreeslotslist)
                /\ (In (firstfreeslot pdentry) (filterOptionPaddr optionfreeslotslist) -> False)
                /\ (exists optionentrieslist : list optionPaddr,
                      optionentrieslist = getKSEntries currentPart s2 /\
                      getKSEntries currentPart s = optionentrieslist /\
                      optionentrieslist = getKSEntries currentPart s0 /\
                      In (firstfreeslot pdentry) (filterOptionPaddr optionentrieslist))
                /\ isPDT multiplexer s
                /\ getPartitions multiplexer s2 = getPartitions multiplexer s0
                /\ getPartitions multiplexer s1 = getPartitions multiplexer s2
                /\ getChildren currentPart s2 = getChildren currentPart s0
                /\ getChildren currentPart s1 = getChildren currentPart s2
                /\ getConfigBlocks currentPart s2 = getConfigBlocks currentPart s0
                /\ getConfigBlocks currentPart s1 = getConfigBlocks currentPart s2
                /\ getConfigPaddr currentPart s2 = getConfigPaddr currentPart s0
                /\ getConfigPaddr currentPart s1 = getConfigPaddr currentPart s2
                /\ (forall block : paddr,
                    In block (getMappedBlocks currentPart s) <->
                    (firstfreeslot pdentry) = block \/ In block (getMappedBlocks currentPart s0))
                /\ ((forall addr : paddr,
                     In addr (getMappedPaddr currentPart s) <-> In addr (getMappedPaddr currentPart s0)) /\
                    length (getMappedPaddr currentPart s) = length (getMappedPaddr currentPart s0))
                /\ (forall block : paddr,
                    In block (getAccessibleMappedBlocks currentPart s) <->
                    (firstfreeslot pdentry) = block \/ In block (getAccessibleMappedBlocks currentPart s0))
                /\ (forall addr : paddr,
                    In addr (getAccessibleMappedPaddr currentPart s) <->
                    In addr (getAllPaddrBlock (startAddr (blockrange bentry6)) (endAddr (blockrange bentry6))
                              ++ getAccessibleMappedPaddr currentPart s0))
                /\ (forall partition : paddr,
                    (partition = currentPart -> False) ->
                    isPDT partition s0 -> getKSEntries partition s = getKSEntries partition s0)
                /\ (forall partition : paddr,
                    (partition = currentPart -> False) ->
                    isPDT partition s0 -> getMappedPaddr partition s = getMappedPaddr partition s0)
                /\ (forall partition : paddr,
                    (partition = currentPart -> False) ->
                    isPDT partition s0 -> getConfigPaddr partition s = getConfigPaddr partition s0)
                /\ (forall partition : paddr,
                    (partition = currentPart -> False) ->
                    isPDT partition s0 -> getPartitions partition s = getPartitions partition s0)
                /\ (forall partition : paddr,
                    (partition = currentPart -> False) ->
                    isPDT partition s0 -> getChildren partition s = getChildren partition s0)
                /\ (forall partition : paddr,
                    (partition = currentPart -> False) ->
                    isPDT partition s0 -> getMappedBlocks partition s = getMappedBlocks partition s0)
                /\ (forall partition : paddr,
                    (partition = currentPart -> False) ->
                    isPDT partition s0 ->
                    getAccessibleMappedBlocks partition s = getAccessibleMappedBlocks partition s0)
                /\ (forall partition : paddr,
                    (partition = currentPart -> False) ->
                    isPDT partition s0 ->
                    getAccessibleMappedPaddr partition s = getAccessibleMappedPaddr partition s0)
                /\ (forall partition : paddr, isPDT partition s = isPDT partition s0)
          ).
    simpl. assert(newBlockEntryAddr = idNewSubblock) by intuition; subst newBlockEntryAddr. split.
    { (* isBE idNewSubblock news *)
      unfold isBE in *. simpl.
      destruct (beqAddr blockToShareInCurrPartAddr idNewSubblock) eqn:HbeqBlockToShareIdNew. trivial.
      rewrite <-beqAddrFalse in HbeqBlockToShareIdNew.
      rewrite removeDupIdentity; intuition.
    }
    destruct Hprops as (_ & HlookupNewBlocks0 & HlookupNewBlocks & Hbentry6 & Hbentry5 & Hbentry4 & Hbentry3 &
        Hbentry2 & Hbentry1 & Hbentry0 & _ & HlookupCurrParts & Hpdentry1 & Hpdentry0 & Hprops).
    destruct Hprops as (HfirstFree & HendNewBlock & HlookupSce & HnbFree & HpredNbFree & Hblkidx6 & Hblkidx5 &
        Hblkidx4 & Hblkidx3 & Hblkidx2 & Hblkidx1 & Hblkidx0 & Hblkidx & Hprops).
    destruct Hprops as (HcurrIsPDTs0 & HcurrIsPDTs & HnewIsBEs0 & HnewIsBEs & HsceIsSCEs0 & HsceIsSCEs & Hsceaddr
        & HnewFirstFree & Hprops).
    destruct Hprops as (HnewSubBlock & HbeqNewFreeCurr & HbeqCurrNewBlock & HbeqNewFreeNewBlock & HbeqSceNewBlock
        & HbeqSceCurr & HbeqSceNewFree & Hoptionfreeslotslist & HinterStates).
    rewrite <-HnewSubBlock in *.
    destruct (beqAddr blockToShareInCurrPartAddr currentPart) eqn:HbeqBlockCurr.
    {
      rewrite <-beqAddrTrue in HbeqBlockCurr. subst currentPart. rewrite HlookupBlocks0 in HlookupCurrParts0.
      congruence.
    }
    assert(HlookupBlocks: lookup blockToShareInCurrPartAddr (memory s) beqAddr = Some (BE bentryShare)).
    {
      rewrite Hs. simpl. rewrite beqAddrFalse in *.
      assert(HbeqSceBlock: beqAddr sceaddr blockToShareInCurrPartAddr = false)
          by (rewrite beqAddrSym; assumption). rewrite HbeqSceBlock. rewrite beqAddrSym.
      rewrite HbeqSceNewBlock. simpl. rewrite HnewBlockToShareEq. rewrite InternalLemmas.beqAddrTrue.
      rewrite HbeqCurrNewBlock. rewrite <-beqAddrFalse in *.
      repeat rewrite removeDupIdentity; try(apply not_eq_sym; assumption). simpl.
      rewrite beqAddrFalse in HbeqBlockCurr. rewrite beqAddrSym in HbeqBlockCurr. rewrite HbeqBlockCurr.
      rewrite InternalLemmas.beqAddrTrue. rewrite <-beqAddrFalse in HbeqBlockCurr.
      repeat rewrite removeDupIdentity; try(apply not_eq_sym; assumption). assumption.
    }
    assert(HnewB: exists l,
                    CBlockEntry (read bentryShare) (write bentryShare) (exec bentryShare) 
                       (present bentryShare) (accessible bentryShare) (blockindex bentryShare)
                       (CBlock (startAddr (blockrange bentryShare)) cutAddr)
                    = {|
                        read := read bentryShare;
                        write := write bentryShare;
                        exec := exec bentryShare;
                        present := present bentryShare;
                        accessible := accessible bentryShare;
                        blockindex := blockindex bentryShare;
                        blockrange := CBlock (startAddr (blockrange bentryShare)) cutAddr;
                        Hidx := ADT.CBlockEntry_obligation_1 (blockindex bentryShare) l
                      |}).
    {
      unfold CBlockEntry. assert(blockindex bentryShare < kernelStructureEntriesNb) by (apply Hidx).
      destruct (Compare_dec.lt_dec (blockindex bentryShare) kernelStructureEntriesNb); try(lia). exists l.
      reflexivity.
    }
    destruct HnewB as [l HnewB].
    assert(Hsh1addr: sh1entryAddr blockToShareInCurrPartAddr (CPaddr (blockToShareInCurrPartAddr + sh1offset)) s).
    { apply lookupSh1EntryAddr with bentryShare. assumption. }
    assert(HPDFlags: sh1entryPDflag (CPaddr (blockToShareInCurrPartAddr + sh1offset)) false s).
    {
      assert(Haccess: AccessibleNoPDFlag sInit)
          by (unfold consistency in Hprops1; unfold consistency1 in Hprops1; intuition).
      assert(HblockIsAcc: bentryAFlag blockToShareInCurrPartAddr true sInit) by intuition.
      assert(HBEBlockToSharesInit: isBE blockToShareInCurrPartAddr sInit).
      { unfold isBE. rewrite HlookupBlockInit. trivial. }
      assert(Hsh1addrsInit: sh1entryAddr blockToShareInCurrPartAddr
                              (CPaddr (blockToShareInCurrPartAddr + sh1offset)) sInit).
      { apply lookupSh1EntryAddr with bentryShareInit. assumption. }
      specialize(Haccess blockToShareInCurrPartAddr (CPaddr (blockToShareInCurrPartAddr + sh1offset))
          HBEBlockToSharesInit Hsh1addrsInit HblockIsAcc). unfold sh1entryPDflag in *.
      assert(Hsh1IsSHE: isSHE (CPaddr (blockToShareInCurrPartAddr + sh1offset)) sInit).
      {
        unfold isSHE.
        destruct (lookup (CPaddr (blockToShareInCurrPartAddr + sh1offset)) (memory sInit) beqAddr);
            try(exfalso; congruence). destruct v; try(exfalso; congruence). trivial.
      }
      assert(HlookupSh1Eq: lookup (CPaddr (blockToShareInCurrPartAddr + sh1offset)) (memory s0) beqAddr
                            = lookup (CPaddr (blockToShareInCurrPartAddr + sh1offset)) (memory sInit) beqAddr).
      {
        apply lookupSHEEqWriteAccess with statesList parentsList blockToCutStartAddr blockToCutEndAddr false
            currentPart; assumption.
      }
      rewrite <-HlookupSh1Eq in Haccess. rewrite Hs. simpl.
      destruct (beqAddr sceaddr (CPaddr (blockToShareInCurrPartAddr + sh1offset))) eqn:HbeqSceSh1.
      {
        rewrite <-beqAddrTrue in HbeqSceSh1. rewrite <-HbeqSceSh1 in *. unfold isSCE in HsceIsSCEs0.
        destruct (lookup sceaddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
      }
      rewrite beqAddrFalse in HbeqSceNewBlock. rewrite beqAddrSym in HbeqSceNewBlock. rewrite HbeqSceNewBlock.
      simpl. destruct (beqAddr idNewSubblock (CPaddr (blockToShareInCurrPartAddr + sh1offset)))
          eqn:HbeqFirstFreeSh1.
      {
        rewrite <-beqAddrTrue in HbeqFirstFreeSh1. rewrite <-HbeqFirstFreeSh1 in *.
        rewrite HlookupNewBlocks0 in Haccess. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite InternalLemmas.beqAddrTrue.
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite beqAddrFalse in HbeqCurrNewBlock. rewrite HbeqCurrNewBlock. simpl.
      destruct (beqAddr currentPart (CPaddr (blockToShareInCurrPartAddr + sh1offset))) eqn:HbeqCurrSh1.
      {
        rewrite <-beqAddrTrue in HbeqCurrSh1. rewrite <-HbeqCurrSh1 in *. rewrite HlookupCurrParts0 in Haccess.
        exfalso; congruence.
      }
      rewrite InternalLemmas.beqAddrTrue. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption). assumption.
    }
    split. intuition. split. intuition. split. intuition. split. intuition. split. intuition.
    split. intuition. split. intuition. split. intuition. split. intuition. split. intuition. split. intuition.
    (* exists (s1 s2 : state) ... *)
    exists s0. exists s. exists pdentry. exists pdentry0. exists pdentry1. exists pdentry1. exists bentry.
    exists bentry0. exists bentry1. exists bentry2. exists bentry3. exists bentry4. exists bentry5.
    exists bentry6. exists bentryShare. exists (CBlockEntry (read bentryShare) (write bentryShare)
        (exec bentryShare) (present bentryShare) (accessible bentryShare) (blockindex bentryShare)
        (CBlock (startAddr (blockrange bentryShare)) cutAddr)). exists scentry. exists predCurrentNbFreeSlots.
    exists sceaddr. exists newFirstFreeSlotAddr.
    assert(HcurrPartEq: currentPartition s = currentPartition s0) by (subst s; simpl; reflexivity).
    split. rewrite HcurrPartEq. reflexivity.
    (*destruct Hprops as (_ & HlookupNewBlocks0 & HlookupNewBlocks & Hbentry6 & Hbentry5 & Hbentry4 & Hbentry3 &
        Hbentry2 & Hbentry1 & Hbentry0 & _ & HlookupCurrParts & Hpdentry1 & Hpdentry0 & Hprops).*)
    split. assumption.
    destruct (beqAddr blockToShareInCurrPartAddr idNewSubblock) eqn:HbeqBlockToShareIdNew.
    { rewrite <-beqAddrTrue in HbeqBlockToShareIdNew. congruence. }
    split.
    { rewrite <-beqAddrFalse in HbeqBlockToShareIdNew. rewrite removeDupIdentity; intuition. }
    split. assumption. split. assumption. split.
    { (* lookup blockToShareInCurrPartAddr *) rewrite InternalLemmas.beqAddrTrue. reflexivity. }
    split. reflexivity.
    split. assumption. split. assumption. split. assumption. split. assumption. split. assumption. split.
    assumption. split. assumption. split. rewrite <-beqAddrFalse. assumption. split.
    { (* sceaddr = CPaddr (firstfreeslot pdentry + scoffset) *)
      subst idNewSubblock. assumption.
    }
    split. assumption. (*destruct (beqAddr blockToShareInCurrPartAddr currentPart) eqn:HbeqBlockCurr.
    {
      rewrite <-beqAddrTrue in HbeqBlockCurr. subst currentPart. rewrite HlookupBlocks0 in HlookupCurrParts0.
      congruence.
    }*)
    split. assumption. split.
    { (* lookup currentPart *) rewrite <-beqAddrFalse in HbeqBlockCurr. rewrite removeDupIdentity; intuition. }
    split. reflexivity. split. assumption. split. assumption. split. assumption. split. assumption. split.
    assumption. split. assumption. split.
    { (* currentPart = currentPartition s0*)
      assert(HcurrPart: currentPart = currentPartition sInit) by intuition. rewrite HcurrPart.
      apply eq_sym. revert HisBuilt. apply currentPartitionEqIsBuilt.
    }
    split. unfold isPDT. rewrite HlookupCurrParts0. trivial. split. assumption. split.
    { (* isPDT currentPart *)
      unfold isPDT. simpl. rewrite HbeqBlockCurr. rewrite <-beqAddrFalse in HbeqBlockCurr.
      rewrite removeDupIdentity; intuition.
    }
    (*destruct Hprops as (HfirstFree & HendNewBlock & HnbFree & HpredNbFree & Hblkidx6 & Hblkidx5 & Hblkidx4 &
        Hblkidx3 & Hblkidx2 & Hblkidx1 & Hblkidx0 & Hblkidx & Hprops).*)
    split.
    { (*pdentryNbFreeSlots currentPart nbFreeSlots s0*)
      unfold pdentryNbFreeSlots in *. rewrite HlookupCurrParts0. rewrite HlookupCurrPartsInit in *.
      assert(HnbFreesInit: nbFreeSlots = nbfreeslots pdentryInit) by intuition. subst nbFreeSlots. assumption.
    }
    split. assumption. split. assumption. split. assumption. split. assumption. split. assumption.
    assert(HAFlags0: bentryAFlag blockToShareInCurrPartAddr true s0).
    {
      assert(HAFlag: bentryAFlag blockToShareInCurrPartAddr true sInit) by intuition.
      assert(HlookupEq: lookup blockToShareInCurrPartAddr (memory s0) beqAddr
                          = lookup blockToShareInCurrPartAddr (memory sInit) beqAddr).
      {
        revert HisBuilt. apply lookupBEEqWriteAccess with currentPart.
        - unfold isPDT. rewrite HlookupCurrPartsInit. trivial.
        - unfold isBE. rewrite HlookupBlockInit. trivial.
        - unfold consistency in *; unfold consistency1 in *; intuition.
        - unfold consistency in *; unfold consistency1 in *; intuition.
        - assert(HparentsList: isParentsList sInit parentsList currentPart) by intuition.
          revert HparentsList. apply basePartNotInParentsLists with pdentryInit; try(assumption);
              unfold consistency in *; unfold consistency1 in *; intuition.
        - intuition.
      }
      unfold bentryAFlag. rewrite HlookupEq. assumption.
    }
    split. assumption. split.
    {
      unfold bentryAFlag in *. simpl. rewrite InternalLemmas.beqAddrTrue. rewrite HnewB. simpl.
      rewrite HlookupBlocks0 in HAFlags0. assumption.
    }
    split.
    {
      assert(Hsh1entryaddr: exists sh1entry sh1entryaddr,
                  lookup sh1entryaddr (memory sInit) beqAddr = Some (SHE sh1entry) /\
                  sh1entryPDchild sh1entryaddr PDChildAddr sInit /\
                  sh1entryAddr blockToShareInCurrPartAddr sh1entryaddr sInit) by intuition.
      destruct Hsh1entryaddr as [sh1entry [sh1entryaddr (HlookupSh1 & HPDchild & Hsh1entryaddr)]].
      assert(HlookupSh1Eq: lookup sh1entryaddr (memory s0) beqAddr
                            = lookup sh1entryaddr (memory sInit) beqAddr).
      {
        apply lookupSHEEqWriteAccess with statesList parentsList blockToCutStartAddr blockToCutEndAddr false
            currentPart; try(assumption). unfold isSHE. rewrite HlookupSh1. trivial.
      }
      exists sh1entry. exists sh1entryaddr. unfold sh1entryPDchild. unfold sh1entryAddr in *.
      rewrite HlookupSh1Eq. rewrite HlookupBlocks0. rewrite HlookupBlockInit in Hsh1entryaddr. intuition.
    }
    split. intuition. destruct HpropsShare as (HreadEq & HwriteEq & HexecEq & HpresentEq & HblkidxEq & HblkrgEq).
    split.
    {
      assert(HstartBlock: bentryStartAddr blockToShareInCurrPartAddr blockToCutStartAddr sInit) by intuition.
      unfold bentryStartAddr in *. rewrite HlookupBlocks0. rewrite HlookupBlockInit in HstartBlock.
      rewrite HblkrgEq. assumption.
    }
    split.
    {
      assert(HendBlock: bentryEndAddr blockToShareInCurrPartAddr blockToCutEndAddr sInit) by intuition.
      unfold bentryEndAddr in *. rewrite HlookupBlocks0. rewrite HlookupBlockInit in HendBlock.
      rewrite HblkrgEq. assumption.
    }
    split.
    {
      assert(HpresentBlock: bentryPFlag blockToShareInCurrPartAddr true sInit) by intuition.
      unfold bentryPFlag in *. rewrite HlookupBlocks0. rewrite HlookupBlockInit in HpresentBlock.
      rewrite HpresentEq. assumption.
    }
    split.
    {
      assert(HblockMapped: In blockToShareInCurrPartAddr (getMappedBlocks currentPart sInit)) by intuition.
      assert(HgetMappedEq: getMappedBlocks currentPart s0 = getMappedBlocks currentPart sInit).
      {
        revert HisBuilt. unfold consistency in *; unfold consistency1 in *; unfold consistency2 in *;
          apply getMappedBlocksEqBuiltWithWriteAcc with blockBase bentryBases0; intuition.
      }
      rewrite HgetMappedEq. assumption.
    }
    split. assumption. split.
    { (* bentryEndAddr (firstfreeslot pdentry) newFirstFreeSlotAddr s0 *)
      subst idNewSubblock. assumption.
    }
    split.
    { (* pdentryNbFreeSlots currentPart *)
      unfold pdentryNbFreeSlots in *. simpl.
      destruct (beqAddr blockToShareInCurrPartAddr currentPart) eqn:HbeqBlockToShareCurrPart.
      rewrite <-beqAddrTrue in HbeqBlockToShareCurrPart. congruence.
      rewrite <-beqAddrFalse in HbeqBlockToShareCurrPart. rewrite removeDupIdentity; intuition.
    }
    split. assumption. split. assumption. split. assumption. split. assumption. split. assumption. split.
    assumption. split. assumption. split. assumption. split.
    { (* isBE (firstfreeslot pdentry) s0 *)
      subst idNewSubblock. unfold isBE. rewrite HlookupNewBlocks0. trivial.
    }
    split.
    { (* isBE (firstfreeslot pdentry) news *)
      unfold isBE in *. simpl. subst idNewSubblock. rewrite HbeqBlockToShareIdNew.
      rewrite <-beqAddrFalse in HbeqBlockToShareIdNew. rewrite removeDupIdentity; intuition.
    }
    split. assumption. split.
    { (* isSCE sceaddr news *)
      unfold isSCE in *. simpl.
      destruct (beqAddr blockToShareInCurrPartAddr sceaddr) eqn:HbeqBlockToShareSceaddr.
      -- rewrite <-beqAddrTrue in HbeqBlockToShareSceaddr. rewrite HbeqBlockToShareSceaddr in *.
         rewrite HlookupBlocks0 in *. congruence.
      -- rewrite <-beqAddrFalse in HbeqBlockToShareSceaddr. rewrite removeDupIdentity; intuition.
    }
    split. assumption. split.
    { rewrite Hpdentry1. rewrite Hpdentry0. simpl. reflexivity. }
    split. intuition. split. subst idNewSubblock. intuition. split. subst idNewSubblock. intuition.
    split. subst idNewSubblock. intuition. split. intuition. split. intuition. split.
    subst idNewSubblock. intuition. split. rewrite <-beqAddrFalse in HbeqBlockCurr. assumption. split.
    {
      intros blockInParentPartitionAddr HblockMappedParent Hstart Hend.
      destruct Hprops1 as (HPIinit & HKDIinit & HVSinit & HparentsList & Hs0 & _ & HcurrIsPDTinit &
        HcurrIsPartinit & HlookupCurrParts0Bis & _ & Hprops0 & Hprops1).
      destruct Hprops0 as (_ & _ & _ & HconsistInit & Hcurr & _ & _ & _ & _ & HblockToShare & HPFlagBlock &
        HblockMapped & HAFlagBlock & _ & _ & HstartBlock & HendBlock & _).
      apply parentsAccSetToFlagIfIsBuiltFromWriteAccessibleRec with currentPart (parent pdentry)
        blockToCutStartAddr blockToCutEndAddr sInit statesList parentsList blockToShareInCurrPartAddr
        bentryShareInit; try(assumption).
      - unfold consistency in HconsistInit; unfold consistency2 in HconsistInit; intuition.
      - unfold consistency in HconsistInit; unfold consistency1 in HconsistInit; intuition.
      - unfold consistency in HconsistInit; unfold consistency1 in HconsistInit; intuition.
      - unfold consistency in HconsistInit; unfold consistency1 in HconsistInit; intuition.
      - unfold consistency in HconsistInit; unfold consistency1 in HconsistInit; intuition.
      - unfold consistency in HconsistInit; unfold consistency1 in HconsistInit; intuition.
      - unfold consistency in HconsistInit; unfold consistency1 in HconsistInit; intuition.
      - unfold consistency in HconsistInit; unfold consistency1 in HconsistInit; intuition.
      - unfold consistency in HconsistInit; unfold consistency1 in HconsistInit; intuition.
      - unfold consistency in HconsistInit; unfold consistency1 in HconsistInit; intuition.
      - unfold consistency in HconsistInit; unfold consistency2 in HconsistInit; intuition.
      - unfold consistency in HconsistInit; unfold consistency1 in HconsistInit; intuition.
      - unfold consistency in HconsistInit; unfold consistency1 in HconsistInit; intuition.
      - assert(HlastPart: exists lastPart pdentryLast,
                               lastPart = last parentsList currentPart /\
                               lookup lastPart (memory s0) beqAddr = Some (PDT pdentryLast) /\
                               (parent pdentryLast = nullAddr \/
                                (forall block : paddr,
                                 In block (getMappedBlocks (parent pdentryLast) s0) ->
                                 ~
                                 (bentryStartAddr block blockToCutStartAddr s0 /\
                                  bentryEndAddr block blockToCutEndAddr s0)))) by intuition.
        destruct HlastPart as [lastPart [pdentryLast (Hlast & HlookupLast & HpropsOrLast)]]. destruct parentsList.
        {
          simpl. simpl in Hlast. subst lastPart. rewrite HlookupCurrParts0 in HlookupLast.
          injection HlookupLast as HpdentriesEq. subst pdentryLast.
          destruct HpropsOrLast as [HcontraNull | HcontraBounds].
          + rewrite HcontraNull in *.
            assert(Hnull: nullAddrExists s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
            unfold nullAddrExists in Hnull. unfold isPADDR in Hnull. unfold getMappedBlocks in HblockMappedParent.
            unfold getKSEntries in HblockMappedParent.
            destruct (lookup nullAddr (memory s0) beqAddr); try(simpl in HblockMappedParent; congruence).
            destruct v; simpl in HblockMappedParent; congruence.
          + specialize(HcontraBounds blockInParentPartitionAddr HblockMappedParent).
            apply Classical_Prop.not_and_or in HcontraBounds.
            destruct HcontraBounds as [Hcontra | Hcontra]; congruence.
        }
        simpl. simpl in HparentsList.
        destruct (lookup p (memory sInit) beqAddr) eqn:HlookupParent; try(exfalso; congruence).
        destruct v; try(exfalso; congruence).
        destruct HparentsList as (_ & [pdentryBis (HlookupCurrPartsInitBis & Hres)] & _).
        rewrite HlookupCurrPartsInitBis in HlookupCurrPartsInit. injection HlookupCurrPartsInit as HpdentriesEq.
        subst pdentryBis. rewrite HparentEq in Hres. left. assumption.
      - unfold checkChild. rewrite HlookupBlockInit.
        assert(HPDFlagsInit: AccessibleNoPDFlag sInit)
          by (unfold consistency in *; unfold consistency1 in *; intuition).
        assert(HblockIsBEsInit: isBE blockToShareInCurrPartAddr sInit)
          by (unfold isBE; rewrite HlookupBlockInit; trivial).
        assert(Hsh1addrsInit: sh1entryAddr blockToShareInCurrPartAddr
                                  (CPaddr (blockToShareInCurrPartAddr + sh1offset)) sInit).
        { apply lookupSh1EntryAddr with bentryShareInit; assumption. }
        specialize(HPDFlagsInit blockToShareInCurrPartAddr (CPaddr (blockToShareInCurrPartAddr + sh1offset))
          HblockIsBEsInit Hsh1addrsInit HAFlagBlock). unfold sh1entryPDflag in HPDFlagsInit.
        destruct (lookup (CPaddr (blockToShareInCurrPartAddr + sh1offset)) (memory sInit) beqAddr);
            try(reflexivity).
        destruct v; try(reflexivity). assumption.
      - assert(HnoDup: noDupUsedPaddrList sInit)
            by (unfold consistency in *; unfold consistency2 in *; intuition).
        assert(HwellFormed: wellFormedBlock sInit)
            by (unfold consistency in *; unfold consistency1 in *; intuition).
        assert(HblockBaseMapped: In blockBase (getMappedBlocks currentPart sInit)) by intuition.
        assert(HstartBase: bentryStartAddr blockBase blockToCutStartAddr sInit) by intuition.
        assert(HPFlagBase: bentryPFlag blockBase true sInit) by intuition.
        pose proof (uniqueBlockMapped blockBase blockToShareInCurrPartAddr blockToCutStartAddr currentPart sInit
            HnoDup HwellFormed HcurrIsPDTinit HblockBaseMapped HblockMapped HstartBase HPFlagBase HstartBlock
            HPFlagBlock) as HeqBlocks. subst blockBase. intuition.
      - pose proof (mappedBlockIsBE blockInParentPartitionAddr (parent pdentry) s0 HblockMappedParent) as Hres.
        destruct Hres as [bentryBlockParent (HlookupBlockParent & Hpresent)]. unfold bentryPFlag.
        rewrite HlookupBlockParent. apply eq_sym. assumption.
           (*/\ (forall blockInParentPartitionAddr,
                In blockInParentPartitionAddr (getMappedBlocks (parent pdentry) s0)
                -> bentryStartAddr blockInParentPartitionAddr blockToCutStartAddr s0
                -> bentryEndAddr blockInParentPartitionAddr blockToCutEndAddr s0
                -> bentryAFlag blockInParentPartitionAddr false s0)*)
    }
    split. assumption. split. assumption. split.
    {
      unfold sh1entryPDflag in *. simpl. destruct (beqAddr blockToShareInCurrPartAddr
          (CPaddr (blockToShareInCurrPartAddr + sh1offset))) eqn:HbeqBlockSh1.
      {
        rewrite <-beqAddrTrue in HbeqBlockSh1. rewrite <-HbeqBlockSh1 in HPDFlags.
        rewrite HlookupBlocks in HPDFlags. congruence.
      }
      rewrite <-beqAddrFalse in HbeqBlockSh1. rewrite removeDupIdentity; intuition.
    }
    (* exists (optionfreeslotslist : list optionPaddr) (s2 : state) ... *)
    (*destruct Hprops as (_ & HbeqNewFreeCurr & HbeqCurrNewBlock & HbeqNewFreeNewBlock & HbeqSceNewBlock &
        HbeqSceCurr & HbeqSceNewFree & Hoptionfreeslotslist & HinterStates).*)
    destruct Hoptionfreeslotslist as [optionfreeslotslist HoptionProps]. exists optionfreeslotslist.
    destruct HoptionProps as [s2' HoptionProps]. exists s2'.
    destruct HoptionProps as [n0 HoptionProps]. exists n0.
    destruct HoptionProps as [n1 HoptionProps]. exists n1.
    destruct HoptionProps as [n2 HoptionProps]. exists n2.
    destruct HoptionProps as [nbleft HoptionProps]. exists nbleft.
    assert(HBEBlockToShare0: isBE blockToShareInCurrPartAddr s0)
        by (unfold isBE; rewrite HlookupBlocks0; intuition).
    assert(HBEBlockToShare: isBE blockToShareInCurrPartAddr s).
    {
      unfold isBE in *. rewrite Hs. simpl. rewrite InternalLemmas.beqAddrTrue.
      destruct (beqAddr sceaddr blockToShareInCurrPartAddr) eqn:HbeqSceaddrBlockToShare.
      { rewrite <-beqAddrTrue in HbeqSceaddrBlockToShare. intuition. }
      destruct (beqAddr idNewSubblock sceaddr) eqn:HbeqIdNewSceaddr.
      { rewrite <-beqAddrTrue in HbeqIdNewSceaddr. exfalso. intuition. }
      simpl. destruct (beqAddr idNewSubblock blockToShareInCurrPartAddr) eqn:HbeqIdNewBlockToShare.
      { rewrite <-beqAddrTrue in HbeqIdNewBlockToShare. intuition. }
      destruct (beqAddr currentPart idNewSubblock) eqn:HbeqCurrPartIdNew.
      { rewrite <-beqAddrTrue in HbeqCurrPartIdNew. intuition. }
      rewrite <-beqAddrFalse in *.
      repeat rewrite removeDupIdentity; try(apply not_eq_sym; assumption). simpl.
      destruct (beqAddr currentPart blockToShareInCurrPartAddr) eqn:HbeqCurrPartBlockToShare.
      { rewrite <-beqAddrTrue in HbeqCurrPartBlockToShare. intuition. }
      rewrite InternalLemmas.beqAddrTrue. repeat rewrite removeDupIdentity; intuition.
    }
    destruct HinterStates as [s1 HinterStates]. destruct HinterStates as [s2 HinterStates].
    destruct HinterStates as [s3 HinterStates]. destruct HinterStates as [s4 HinterStates].
    destruct HinterStates as [s5 HinterStates]. destruct HinterStates as [s6 HinterStates].
    destruct HinterStates as [s7 HinterStates]. destruct HinterStates as [s8 HinterStates].
    destruct HinterStates as [s9 HinterStates]. destruct HinterStates as [s10 HinterStates].
    destruct HinterStates as [Hs1 (Hs2 & (Hs3 & (Hs4 & (Hs5 & (Hs6 & (Hs7 & (Hs8 & (Hs9 & Hs10))))))))].
    assert(Hs10sEq: s10 = s).
    {
      subst s10. subst s9. subst s8. subst s7. subst s6. subst s5. subst s4. subst s3. subst s2. subst s1.
      simpl. rewrite Hs. f_equal.
    }
    rewrite Hs10sEq in *. subst idNewSubblock.
    set(s':= {|
               currentPartition := currentPartition s;
               memory := _
             |}).
    destruct HoptionProps as (Hnbleft & HnbleftBounded & Hss2' & Hoptionfreeslotslist & (Hmult & HgetPartss2' &
        HgetPartss & HgetChildrens2' & HgetChildrens & HgetConfigBs2' & HgetConfigBs & HgetConfigPs2' &
        HgetConfigPs & HgetMappedBEquiv & (HgetMappedPEquiv & HgetMappedPLenEq) & HgetAccMappedBEquiv &
        HgetAccMappedPEquiv & HgetKSEq & HgetMappedPEq & HgetConfigPEq & HgetPartsEq & HgetChildrenEq &
        HgetMappedBEq & HgetAccMappedBEq & HgetAccMappedPEq) & HPDTEq).
    destruct Hoptionfreeslotslist as (HoptionFrees2' & HoptionFrees & HoptionFrees0 & Hn0n1 & Hnbleftn0 &
        Hn1n2 & Hnbleftn2 & Hn2Bounded & HwellFormedList & HnoDupList & HfirstFreeInList & HoptionList).
    split. assumption. split. assumption. split. assumption. split. assumption. split. assumption. split.
    assumption. split. assumption. split. assumption. split. assumption. split. assumption. split. assumption.
    split. assumption. split. assumption. split. assumption. split.
    {
      destruct HoptionList as [optionentrieslist (HgetKSs2' & HgetKSs & HgetKSs0 & HfirstFreeIn)].
      exists optionentrieslist. split. assumption. split. rewrite <-HgetKSs.
      apply getKSEntriesEqBE; intuition. split; assumption.
    }
    split. apply isPDTMultiplexerEqBE; intuition. split. assumption. split. assumption. split. assumption. split.
    assumption. split. assumption. split. assumption. split. assumption. split. assumption. split.
    {
      intro block.
      assert(HgetMappedBCurrEq: getMappedBlocks currentPart s' = getMappedBlocks currentPart s).
      {
        apply getMappedBlocksEqBENoChange with bentryShare. assumption.
        rewrite HnewB. simpl. reflexivity.
      }
      rewrite HgetMappedBCurrEq. specialize(HgetMappedBEquiv block). assumption.
    }
    assert(HgetMappedPCurrEqs: forall addr, In addr (getMappedPaddr currentPart s)
                                            <-> In addr (getMappedPaddr currentPart s0)).
    {
      intro addr. specialize(HgetMappedPEquiv addr).
      destruct HgetMappedPEquiv as (HgetMappedPEquivLeft & HgetMappedPEquivRight). split.
      - intro HaddrMappeds. apply HgetMappedPEquivLeft in HaddrMappeds. apply in_app_or in HaddrMappeds.
        destruct HaddrMappeds as [HedgeCase | HaddrMappeds0]; try(assumption). unfold CBlockEntry in Hbentry6.
        assert(blockindex bentry5 < kernelStructureEntriesNb) by (apply Hidx).
        destruct (Compare_dec.lt_dec (blockindex bentry5) kernelStructureEntriesNb); try(lia).
        unfold CBlockEntry in Hbentry5. assert(blockindex bentry4 < kernelStructureEntriesNb) by (apply Hidx).
        destruct (Compare_dec.lt_dec (blockindex bentry4) kernelStructureEntriesNb); try(lia).
        unfold CBlockEntry in Hbentry4. assert(blockindex bentry3 < kernelStructureEntriesNb) by (apply Hidx).
        destruct (Compare_dec.lt_dec (blockindex bentry3) kernelStructureEntriesNb); try(lia).
        unfold CBlockEntry in Hbentry3. assert(blockindex bentry2 < kernelStructureEntriesNb) by (apply Hidx).
        destruct (Compare_dec.lt_dec (blockindex bentry2) kernelStructureEntriesNb); try(lia).
        unfold CBlockEntry in Hbentry2. assert(blockindex bentry1 < kernelStructureEntriesNb) by (apply Hidx).
        destruct (Compare_dec.lt_dec (blockindex bentry1) kernelStructureEntriesNb); try(lia).
        unfold CBlockEntry in Hbentry1. assert(blockindex bentry0 < kernelStructureEntriesNb) by (apply Hidx).
        destruct (Compare_dec.lt_dec (blockindex bentry0) kernelStructureEntriesNb); try(lia).
        unfold CBlockEntry in Hbentry0. assert(blockindex bentry < kernelStructureEntriesNb) by (apply Hidx).
        destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
        rewrite Hbentry6 in HedgeCase. simpl in HedgeCase. rewrite Hbentry5 in HedgeCase. simpl in HedgeCase.
        rewrite Hbentry4 in HedgeCase. simpl in HedgeCase. rewrite Hbentry3 in HedgeCase. simpl in HedgeCase.
        rewrite Hbentry2 in HedgeCase. simpl in HedgeCase. rewrite Hbentry1 in HedgeCase. simpl in HedgeCase.
        rewrite Hbentry0 in HedgeCase. simpl in HedgeCase. unfold CBlock in HedgeCase.
        assert(endAddr (blockrange bentry) <= maxIdx).
        { rewrite maxIdxEqualMaxAddr. apply Hp. }
        destruct (Compare_dec.le_dec (endAddr (blockrange bentry) - cutAddr) maxIdx); try(lia).
        simpl in HedgeCase.
        assert(HendsEq: blockToCutEndAddr = blockEndAddr).
        {
          assert(HendsInit: bentryEndAddr blockToShareInCurrPartAddr blockToCutEndAddr sInit) by intuition.
          unfold bentryEndAddr in *. rewrite HlookupBlockInit in HendsInit. rewrite HlookupBlocks0 in HendAddr.
          subst blockEndAddr. rewrite HblkrgEq. assumption.
        }
        subst blockToCutEndAddr.
        assert(Hsub: StateLib.Paddr.subPaddr blockEndAddr cutAddr = Some subblock2Size) by intuition.
        unfold StateLib.Paddr.subPaddr in Hsub.
        destruct (Compare_dec.le_dec (blockEndAddr - cutAddr) maxIdx); try(exfalso; congruence).
        simpl in HedgeCase.
        assert(HaddrInBlock: In addr (getAllPaddrAux [blockToShareInCurrPartAddr] s0)).
        {
          simpl. rewrite HlookupBlocks0. rewrite app_nil_r.
          assert(HstartAddr: bentryStartAddr blockToShareInCurrPartAddr blockToCutStartAddr sInit) by intuition.
          unfold bentryStartAddr in HstartAddr. unfold bentryEndAddr in HendAddr.
          rewrite HlookupBlockInit in HstartAddr. rewrite HlookupBlocks0 in HendAddr.
          rewrite <-HblkrgEq in HstartAddr. rewrite <-HstartAddr. rewrite <-HendAddr.
          apply getAllPaddrBlockInclRev in HedgeCase. destruct HedgeCase as (HcutLe & HaddrLt & _).
          assert(HleCut: false = StateLib.Paddr.leb cutAddr blockToCutStartAddr) by intuition.
          unfold StateLib.Paddr.leb in HleCut. apply eq_sym in HleCut. apply PeanoNat.Nat.leb_gt in HleCut.
          apply getAllPaddrBlockIncl; lia.
        }
        assert(HblockMapped: In blockToShareInCurrPartAddr (getMappedBlocks currentPart sInit)) by intuition.
        assert(HgetMappedBCurrEqs0: getMappedBlocks currentPart s0 = getMappedBlocks currentPart sInit).
        {
          revert HisBuilt. unfold consistency in *; unfold consistency1 in *; unfold consistency2 in *;
            apply getMappedBlocksEqBuiltWithWriteAcc with blockBase bentryBases0; intuition.
        }
        rewrite <-HgetMappedBCurrEqs0 in HblockMapped.
        apply addrInBlockIsMapped with blockToShareInCurrPartAddr; assumption.
      - intro HaddrMappeds0. apply HgetMappedPEquivRight. apply in_or_app. right. assumption.
    }
    assert(HgetMappedBCurrEqs0: getMappedBlocks currentPart s0 = getMappedBlocks currentPart sInit).
    {
      revert HisBuilt. unfold consistency in *; unfold consistency1 in *; unfold consistency2 in *;
        apply getMappedBlocksEqBuiltWithWriteAcc with blockBase bentryBases0; intuition.
    }
    assert(HaddrMappedEquiv: forall addr, In addr (getMappedPaddr currentPart s')
                                          <-> In addr (getMappedPaddr currentPart s)).
    {
      intro addr. assert(blockindex bentryShare < kernelStructureEntriesNb) by (apply Hidx).
      apply getMappedPaddrEqBEEndLower with (firstfreeslot pdentry) cutAddr bentryShare bentry6;
          try(assumption);
          try(unfold CBlockEntry;
              destruct (Compare_dec.lt_dec (blockindex bentryShare) kernelStructureEntriesNb); try(lia);
              simpl; try(reflexivity); unfold CBlock).
      + assert(Hstart: bentryStartAddr blockToShareInCurrPartAddr blockToCutStartAddr sInit) by intuition.
        assert(HstartBis: bentryStartAddr blockToShareInCurrPartAddr blockToCutStartAddr sInit) by intuition.
        unfold bentryStartAddr in *. rewrite HlookupBlockInit in *.
        rewrite <-HblkrgEq in Hstart. rewrite <-Hstart.
        assert(Hle: false = StateLib.Paddr.leb cutAddr blockToCutStartAddr) by intuition.
        unfold StateLib.Paddr.leb in Hle. apply eq_sym in Hle. apply PeanoNat.Nat.leb_gt in Hle.
        assert(cutAddr <= maxIdx) by (rewrite maxIdxEqualMaxAddr; apply Hp).
        destruct (Compare_dec.le_dec (cutAddr - blockToCutStartAddr) maxIdx); try(lia). simpl.
        reflexivity.
      + assert(cutAddr <= maxIdx) by (rewrite maxIdxEqualMaxAddr; apply Hp).
        destruct (Compare_dec.le_dec (cutAddr - startAddr (blockrange bentryShare)) maxIdx); try(lia).
        simpl. reflexivity.
      + assert(HendBis: bentryEndAddr blockToShareInCurrPartAddr blockToCutEndAddr sInit) by intuition.
        unfold bentryEndAddr in *. rewrite HlookupBlockInit in HendBis. rewrite HlookupBlocks0 in HendAddr.
        rewrite <-HblkrgEq in HendBis. rewrite <-HendAddr in HendBis. subst blockToCutEndAddr.
        rewrite <-HendAddr. assert(Hle: false = StateLib.Paddr.leb blockEndAddr cutAddr) by intuition.
        unfold StateLib.Paddr.leb in Hle. apply eq_sym in Hle. apply PeanoNat.Nat.leb_gt in Hle. lia.
      + unfold consistency1 in Hconsist. intuition.
      + rewrite HlookupNewBlocks. rewrite app_nil_r. unfold CBlockEntry in Hbentry6.
        assert(blockindex bentry5 < kernelStructureEntriesNb) by (apply Hidx).
        destruct (Compare_dec.lt_dec (blockindex bentry5) kernelStructureEntriesNb); try(lia).
        unfold CBlockEntry in Hbentry5. assert(blockindex bentry4 < kernelStructureEntriesNb) by (apply Hidx).
        destruct (Compare_dec.lt_dec (blockindex bentry4) kernelStructureEntriesNb); try(lia).
        unfold CBlockEntry in Hbentry4. assert(blockindex bentry3 < kernelStructureEntriesNb) by (apply Hidx).
        destruct (Compare_dec.lt_dec (blockindex bentry3) kernelStructureEntriesNb); try(lia).
        unfold CBlockEntry in Hbentry3. assert(blockindex bentry2 < kernelStructureEntriesNb) by (apply Hidx).
        destruct (Compare_dec.lt_dec (blockindex bentry2) kernelStructureEntriesNb); try(lia).
        unfold CBlockEntry in Hbentry2. assert(blockindex bentry1 < kernelStructureEntriesNb) by (apply Hidx).
        destruct (Compare_dec.lt_dec (blockindex bentry1) kernelStructureEntriesNb); try(lia).
        unfold CBlockEntry in Hbentry1. assert(blockindex bentry0 < kernelStructureEntriesNb) by (apply Hidx).
        destruct (Compare_dec.lt_dec (blockindex bentry0) kernelStructureEntriesNb); try(lia).
        unfold CBlockEntry in Hbentry0. assert(blockindex bentry < kernelStructureEntriesNb) by (apply Hidx).
        destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
        rewrite Hbentry6. simpl. rewrite Hbentry5. simpl. rewrite Hbentry4. simpl. rewrite Hbentry3. simpl.
        rewrite Hbentry2. simpl. rewrite Hbentry1. simpl. rewrite Hbentry0. simpl. unfold CBlock.
        assert(endAddr (blockrange bentry) <= maxIdx).
        { rewrite maxIdxEqualMaxAddr. apply Hp. }
        destruct (Compare_dec.le_dec (endAddr (blockrange bentry) - cutAddr) maxIdx); try(lia). simpl.
        assert(HendBis: bentryEndAddr blockToShareInCurrPartAddr blockToCutEndAddr sInit) by intuition.
        unfold bentryEndAddr in *. rewrite HlookupBlockInit in HendBis. rewrite HlookupBlocks0 in HendAddr.
        rewrite <-HblkrgEq in HendBis. rewrite <-HendAddr in HendBis. subst blockToCutEndAddr.
        rewrite <-HendAddr.
        assert(blockEndAddr <= maxIdx).
        { rewrite maxIdxEqualMaxAddr. apply Hp. }
        destruct (Compare_dec.le_dec (blockEndAddr - cutAddr) maxIdx); try(lia). simpl.
        intros addr' Haddr'Mapped. assumption.
      + assert(HblockMapped: In blockToShareInCurrPartAddr (getMappedBlocks currentPart sInit)) by intuition.
        rewrite <-HgetMappedBCurrEqs0 in HblockMapped. apply HgetMappedBEquiv. right. assumption.
      + apply HgetMappedBEquiv. left. reflexivity.
    }
    assert(HgetMappedPEquivs': forall addr, In addr (getMappedPaddr currentPart s')
                                            <-> In addr (getMappedPaddr currentPart s0)).
    {
      intro addr. specialize(HgetMappedPCurrEqs addr).
      destruct HgetMappedPCurrEqs as (HgetMappedPCurrEqsLeft & HgetMappedPCurrEqsRight).
      split.
      - intro HaddrMapped. apply HgetMappedPCurrEqsLeft. apply HaddrMappedEquiv. assumption.
      - intro HaddrMapped. apply HgetMappedPCurrEqsRight in HaddrMapped. apply HaddrMappedEquiv. assumption.
    }
    split.
    {
      split. assumption.
      unfold CBlockEntry in *. assert(blockindex bentryShare < kernelStructureEntriesNb) by (apply Hidx).
      destruct (Compare_dec.lt_dec (blockindex bentryShare) kernelStructureEntriesNb); try(lia).
      unfold CBlock in *. assert(HlebCutMax: cutAddr <= maxAddr) by (apply Hp).
      rewrite <-maxIdxEqualMaxAddr in HlebCutMax.
      destruct (Compare_dec.le_dec (cutAddr - startAddr (blockrange bentryShare)) maxIdx); try(lia).
      set(newBentry := {|
                         read := read bentryShare;
                         write := write bentryShare;
                         exec := exec bentryShare;
                         present := present bentryShare;
                         accessible := accessible bentryShare;
                         blockindex := blockindex bentryShare;
                         blockrange :=
                           {|
                             startAddr := startAddr (blockrange bentryShare);
                             endAddr := cutAddr;
                             Hsize :=
                               ADT.CBlock_obligation_1 (startAddr (blockrange bentryShare)) cutAddr l1
                           |};
                         Hidx := ADT.CBlockEntry_obligation_1 (blockindex bentryShare) l0
                       |}).
      assert(HpresentEqs: present newBentry = present bentryShare) by (simpl; reflexivity).
      assert(HstartEq: startAddr (blockrange newBentry) = startAddr (blockrange bentryShare))
          by (simpl; reflexivity).
      assert(HendIsCut: endAddr (blockrange newBentry) = cutAddr) by (simpl; reflexivity).
      assert(HlebCutEnd: cutAddr <= endAddr (blockrange bentryShare)).
      {
        assert(Hleb: false = StateLib.Paddr.leb blockToCutEndAddr cutAddr) by intuition.
        apply eq_sym in Hleb. unfold StateLib.Paddr.leb in Hleb. apply Compare_dec.leb_iff_conv in Hleb.
        assert(Hend: bentryEndAddr blockToShareInCurrPartAddr blockToCutEndAddr sInit) by intuition.
        unfold bentryEndAddr in Hend. rewrite HlookupBlockInit in Hend; rewrite <-HblkrgEq in Hend.
        subst blockToCutEndAddr. lia.
      }
      assert(HlebStartCut: startAddr (blockrange bentryShare) <= endAddr (blockrange newBentry)).
      {
        simpl. assert(Hleb: false = StateLib.Paddr.leb cutAddr blockToCutStartAddr) by intuition.
        unfold StateLib.Paddr.leb in Hleb. apply eq_sym in Hleb. apply Compare_dec.leb_iff_conv in Hleb.
        assert(Hstart: bentryStartAddr blockToShareInCurrPartAddr blockToCutStartAddr sInit) by intuition.
        unfold bentryStartAddr in Hstart. rewrite HlookupBlockInit in Hstart. rewrite <-HblkrgEq in Hstart.
        subst blockToCutStartAddr. lia.
      }
      assert(HnoDup: noDupMappedBlocksList s) by (unfold consistency1 in *; intuition).
      assert(HblockMappeds: In blockToShareInCurrPartAddr (getMappedBlocks currentPart s)).
      {
        assert(HblockMapped: In blockToShareInCurrPartAddr (getMappedBlocks currentPart sInit)) by intuition.
        rewrite <-HgetMappedBCurrEqs0 in HblockMapped. apply HgetMappedBEquiv. right. assumption.
      }
      pose proof (getMappedPaddrEqBEEndLowerChangeLengthEquality currentPart
          blockToShareInCurrPartAddr newBentry cutAddr bentryShare s HcurrIsPDTs HlookupBlocks HpresentEqs
          HstartEq HendIsCut HlebCutEnd HlebStartCut HnoDup HblockMappeds) as Hss'. unfold newBentry in Hss'.
      fold s' in Hss'. rewrite HgetMappedPLenEq in Hss'.
      assert(blockindex bentry5 < kernelStructureEntriesNb) by (apply Hidx).
      assert(blockindex bentry4 < kernelStructureEntriesNb) by (apply Hidx).
      assert(blockindex bentry3 < kernelStructureEntriesNb) by (apply Hidx).
      assert(blockindex bentry2 < kernelStructureEntriesNb) by (apply Hidx).
      assert(blockindex bentry1 < kernelStructureEntriesNb) by (apply Hidx).
      assert(blockindex bentry0 < kernelStructureEntriesNb) by (apply Hidx).
      assert(blockindex bentry < kernelStructureEntriesNb) by (apply Hidx).
      destruct (Compare_dec.lt_dec (blockindex bentry5) kernelStructureEntriesNb); try(lia).
      destruct (Compare_dec.lt_dec (blockindex bentry4) kernelStructureEntriesNb); try(lia).
      destruct (Compare_dec.lt_dec (blockindex bentry3) kernelStructureEntriesNb); try(lia).
      destruct (Compare_dec.lt_dec (blockindex bentry2) kernelStructureEntriesNb); try(lia).
      destruct (Compare_dec.lt_dec (blockindex bentry1) kernelStructureEntriesNb); try(lia).
      destruct (Compare_dec.lt_dec (blockindex bentry0) kernelStructureEntriesNb); try(lia).
      destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
      rewrite Hbentry6 in Hss'. simpl in Hss'. rewrite Hbentry5 in Hss'. simpl in Hss'.
      rewrite Hbentry4 in Hss'. simpl in Hss'. rewrite Hbentry3 in Hss'. simpl in Hss'.
      rewrite Hbentry2 in Hss'. simpl in Hss'. rewrite Hbentry1 in Hss'. simpl in Hss'.
      assert(blockEndAddr <= maxIdx) by (rewrite maxIdxEqualMaxAddr; apply Hp).
      destruct (Compare_dec.le_dec (blockEndAddr - startAddr (blockrange bentry0)) maxIdx); try(lia).
      simpl in Hss'. rewrite Hbentry0 in Hss'. simpl in Hss'.
      assert(endAddr (blockrange bentry) <= maxIdx) by (rewrite maxIdxEqualMaxAddr; apply Hp).
      destruct (Compare_dec.le_dec (endAddr (blockrange bentry) - cutAddr) maxIdx); try(lia).
      simpl in Hss'. unfold bentryEndAddr in HendAddr. rewrite HlookupBlocks0 in HendAddr.
      rewrite <-HendAddr in Hss'. rewrite length_app in Hss'. rewrite length_app in Hss'.
      rewrite PeanoNat.Nat.add_comm in Hss'. apply PeanoNat.Nat.add_cancel_l in Hss'. assumption.
    }
    split.
    {
      assert(HgetAccMappedBEqs': getAccessibleMappedBlocks currentPart s'
                                              = getAccessibleMappedBlocks currentPart s).
      {
        apply getAccessibleMappedBlocksEqBEAccessiblePresentNoChange with bentryShare; try(assumption);
            unfold CBlockEntry; destruct (Compare_dec.lt_dec (blockindex bentryShare) kernelStructureEntriesNb);
            try(lia); simpl; reflexivity.
      }
      rewrite HgetAccMappedBEqs'. assumption.
    }
    split.
    {
      assert(HaddrAccMappedEquiv: forall addr, In addr (getAccessibleMappedPaddr currentPart s')
                                            <-> In addr (getAllPaddrBlock (startAddr (blockrange bentry6))
                                                                          (endAddr (blockrange bentry6))
                                                          ++ getAccessibleMappedPaddr currentPart s)).
      {
        intro addr. assert(blockindex bentryShare < kernelStructureEntriesNb) by (apply Hidx).
        unfold CBlockEntry in Hbentry6.
        assert(blockindex bentry5 < kernelStructureEntriesNb) by (apply Hidx).
        destruct (Compare_dec.lt_dec (blockindex bentry5) kernelStructureEntriesNb); try(lia).
        unfold CBlockEntry in Hbentry5. assert(blockindex bentry4 < kernelStructureEntriesNb) by (apply Hidx).
        destruct (Compare_dec.lt_dec (blockindex bentry4) kernelStructureEntriesNb); try(lia).
        unfold CBlockEntry in Hbentry4. assert(blockindex bentry3 < kernelStructureEntriesNb) by (apply Hidx).
        destruct (Compare_dec.lt_dec (blockindex bentry3) kernelStructureEntriesNb); try(lia).
        unfold CBlockEntry in Hbentry3. assert(blockindex bentry2 < kernelStructureEntriesNb) by (apply Hidx).
        destruct (Compare_dec.lt_dec (blockindex bentry2) kernelStructureEntriesNb); try(lia).
        unfold CBlockEntry in Hbentry2. assert(blockindex bentry1 < kernelStructureEntriesNb) by (apply Hidx).
        destruct (Compare_dec.lt_dec (blockindex bentry1) kernelStructureEntriesNb); try(lia).
        unfold CBlockEntry in Hbentry1. assert(blockindex bentry0 < kernelStructureEntriesNb) by (apply Hidx).
        destruct (Compare_dec.lt_dec (blockindex bentry0) kernelStructureEntriesNb); try(lia).
        unfold CBlockEntry in Hbentry0. assert(blockindex bentry < kernelStructureEntriesNb) by (apply Hidx).
        destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
        apply getAccessibleMappedPaddrEqBEEndLowerLax with (firstfreeslot pdentry) cutAddr bentryShare;
            try(assumption);
            try(unfold CBlockEntry;
                destruct (Compare_dec.lt_dec (blockindex bentryShare) kernelStructureEntriesNb); try(lia);
                simpl; try(reflexivity); unfold CBlock).
        + rewrite Hbentry6. simpl. rewrite Hbentry5. simpl. rewrite Hbentry4. simpl. rewrite Hbentry3.
          reflexivity.
        + assert(Hstart: bentryStartAddr blockToShareInCurrPartAddr blockToCutStartAddr sInit) by intuition.
          unfold bentryStartAddr in *. rewrite HlookupBlockInit in *. rewrite <-HblkrgEq in Hstart.
          rewrite <-Hstart. assert(Hle: false = StateLib.Paddr.leb cutAddr blockToCutStartAddr) by intuition.
          unfold StateLib.Paddr.leb in Hle. apply eq_sym in Hle. apply PeanoNat.Nat.leb_gt in Hle.
          assert(cutAddr <= maxIdx) by (rewrite maxIdxEqualMaxAddr; apply Hp).
          destruct (Compare_dec.le_dec (cutAddr - blockToCutStartAddr) maxIdx); try(lia). simpl.
          reflexivity.
        + assert(cutAddr <= maxIdx) by (rewrite maxIdxEqualMaxAddr; apply Hp).
          destruct (Compare_dec.le_dec (cutAddr - startAddr (blockrange bentryShare)) maxIdx); try(lia).
          simpl. reflexivity.
        + assert(HendBis: bentryEndAddr blockToShareInCurrPartAddr blockToCutEndAddr sInit) by intuition.
          unfold bentryEndAddr in *. rewrite HlookupBlockInit in HendBis. rewrite HlookupBlocks0 in HendAddr.
          rewrite <-HblkrgEq in HendBis. rewrite <-HendAddr in HendBis. subst blockToCutEndAddr.
          rewrite <-HendAddr. assert(Hle: false = StateLib.Paddr.leb blockEndAddr cutAddr) by intuition.
          unfold StateLib.Paddr.leb in Hle. apply eq_sym in Hle. apply PeanoNat.Nat.leb_gt in Hle. lia.
        + unfold consistency1 in Hconsist. intuition.
        + rewrite HlookupNewBlocks. rewrite app_nil_r.
          rewrite Hbentry6. simpl. rewrite Hbentry5. simpl. rewrite Hbentry4. simpl. rewrite Hbentry3. simpl.
          rewrite Hbentry2. simpl. rewrite Hbentry1. simpl. rewrite Hbentry0. simpl. unfold CBlock.
          assert(endAddr (blockrange bentry) <= maxIdx).
          { rewrite maxIdxEqualMaxAddr. apply Hp. }
          destruct (Compare_dec.le_dec (endAddr (blockrange bentry) - cutAddr) maxIdx); try(lia). simpl.
          assert(HendBis: bentryEndAddr blockToShareInCurrPartAddr blockToCutEndAddr sInit) by intuition.
          unfold bentryEndAddr in *. rewrite HlookupBlockInit in HendBis. rewrite HlookupBlocks0 in HendAddr.
          rewrite <-HblkrgEq in HendBis. rewrite <-HendAddr in HendBis. subst blockToCutEndAddr.
          rewrite <-HendAddr.
          assert(blockEndAddr <= maxIdx).
          { rewrite maxIdxEqualMaxAddr. apply Hp. }
          destruct (Compare_dec.le_dec (blockEndAddr - cutAddr) maxIdx); try(lia). simpl.
          intros addr' Haddr'Mapped. assumption.
        + assert(HblockMapped: In blockToShareInCurrPartAddr (getMappedBlocks currentPart sInit)) by intuition.
          rewrite <-HgetMappedBCurrEqs0 in HblockMapped. apply HgetMappedBEquiv. right. assumption.
        + apply HgetAccMappedBEquiv. left. reflexivity.
      }
      intro addr. specialize(HaddrAccMappedEquiv addr). destruct HaddrAccMappedEquiv as (Hleft & Hright).
      specialize(HgetAccMappedPEquiv addr). destruct HgetAccMappedPEquiv as (HleftP & HrightP). split.
      - intro Hintro. apply Hleft in Hintro. apply in_app_or in Hintro. destruct Hintro as [Hedge | Hintro];
          try(apply in_or_app; left; assumption). apply HleftP. assumption.
      - intro Hintro. apply Hright. apply in_app_or in Hintro. destruct Hintro as [Hedge | Hintro];
          apply in_or_app; try(left; assumption). right. apply HrightP. apply in_or_app. right. assumption.
    }
    split.
    {
      intros part HpartNotCurr HpartIsPDT. specialize(HgetKSEq part HpartNotCurr HpartIsPDT). rewrite <-HgetKSEq.
      apply getKSEntriesEqBE. assumption.
    }
    split.
    {
      intros part HpartNotCurr HpartIsPDT. specialize(HgetMappedPEq part HpartNotCurr HpartIsPDT).
      rewrite <-HgetMappedPEq. apply getMappedPaddrEqBENotInPart. assumption.
      assert(HblockInCurr: In blockToShareInCurrPartAddr (getMappedBlocks currentPart sInit)) by intuition.
      assert(Hdisjoint: DisjointKSEntries s) by (unfold consistency1 in *; intuition).
      assert(HpartIsPDTs: isPDT part s).
      {
        unfold isPDT in *. rewrite Hs. simpl. destruct (beqAddr sceaddr part) eqn:HbeqPartSce.
        {
          rewrite <-DTL.beqAddrTrue in HbeqPartSce. unfold isSCE in HsceIsSCEs0. subst part.
          destruct (lookup sceaddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
        }
        rewrite <-beqAddrFalse in HbeqPartSce. rewrite beqAddrFalse in HbeqSceNewBlock.
        rewrite beqAddrSym in HbeqSceNewBlock. rewrite HbeqSceNewBlock. simpl.
        destruct (beqAddr (firstfreeslot pdentry) part) eqn:HbeqFirstFreePart.
        {
          rewrite <-DTL.beqAddrTrue in HbeqFirstFreePart. unfold isBE in HnewIsBEs0. subst part.
          destruct (lookup (firstfreeslot pdentry) (memory s0) beqAddr); try(congruence). destruct v; congruence.
        }
        rewrite removeDupIdentity; try(apply not_eq_sym; assumption). rewrite InternalLemmas.beqAddrTrue.
        rewrite beqAddrFalse in HbeqCurrNewBlock. rewrite HbeqCurrNewBlock. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity; try(apply not_eq_sym; assumption). simpl.
        assert(HpartNotCurrBis: currentPart <> part) by intuition. rewrite beqAddrFalse in HpartNotCurrBis.
        rewrite HpartNotCurrBis. rewrite InternalLemmas.beqAddrTrue.
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity; try(apply not_eq_sym; assumption). assumption.
      }
      specialize(Hdisjoint part currentPart HpartIsPDTs HcurrIsPDTs HpartNotCurr).
      destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
      unfold getMappedBlocks in HblockInCurr. apply InFilterPresentInList in HblockInCurr. intro Hcontra.
      specialize(Hdisjoint blockToShareInCurrPartAddr Hcontra).
      assert(HgetKSCurrEq: getKSEntries currentPart s = getKSEntries currentPart sInit).
      {
        destruct HoptionList as [optionlist (_ & Hlists & Hlists0 & _)]. subst optionlist.
        assert(HgetKSCurrEq: getKSEntries currentPart s0 = getKSEntries currentPart sInit).
        {
          unfold consistency in Hprops1. unfold consistency1 in Hprops1. unfold consistency2 in Hprops1.
          apply getKSEntriesEqBuiltWithWriteAcc with statesList parentsList blockToCutStartAddr blockToCutEndAddr
              currentPart false blockBase bentryBases0; intuition.
        }
        rewrite <-HgetKSCurrEq. assumption.
      }
      rewrite <-HgetKSCurrEq in HblockInCurr. congruence.
    }
    split.
    {
      intros part HpartNotCurr HpartIsPDT. specialize(HgetConfigPEq part HpartNotCurr HpartIsPDT).
      rewrite <-HgetConfigPEq. apply getConfigPaddrEqBE. unfold isPDT in *. rewrite Hs. simpl.
      destruct (beqAddr sceaddr part) eqn:HbeqPartSce.
      {
        rewrite <-DTL.beqAddrTrue in HbeqPartSce. unfold isSCE in HsceIsSCEs0. subst part.
        destruct (lookup sceaddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
      }
      rewrite <-beqAddrFalse in HbeqPartSce. rewrite beqAddrFalse in HbeqSceNewBlock.
      rewrite beqAddrSym in HbeqSceNewBlock. rewrite HbeqSceNewBlock. simpl.
      destruct (beqAddr (firstfreeslot pdentry) part) eqn:HbeqFirstFreePart.
      {
        rewrite <-DTL.beqAddrTrue in HbeqFirstFreePart. unfold isBE in HnewIsBEs0. subst part.
        destruct (lookup (firstfreeslot pdentry) (memory s0) beqAddr); try(congruence). destruct v; congruence.
      }
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption). rewrite InternalLemmas.beqAddrTrue.
      rewrite beqAddrFalse in HbeqCurrNewBlock. rewrite HbeqCurrNewBlock. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption). simpl.
      assert(HpartNotCurrBis: currentPart <> part) by intuition. rewrite beqAddrFalse in HpartNotCurrBis.
      rewrite HpartNotCurrBis. rewrite InternalLemmas.beqAddrTrue.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption). assumption.
      assumption.
    }
    split.
    {
      intros part HpartNotCurr HpartIsPDT. specialize(HgetPartsEq part HpartNotCurr HpartIsPDT).
      rewrite <-HgetPartsEq. apply getPartitionsAuxEqBEPDflagFalse with bentryShare
          (CPaddr (blockToShareInCurrPartAddr + sh1offset)); try(assumption).
      - unfold isPDT in *. rewrite Hs. simpl.
        destruct (beqAddr sceaddr part) eqn:HbeqPartSce.
        {
          rewrite <-DTL.beqAddrTrue in HbeqPartSce. unfold isSCE in HsceIsSCEs0. subst part.
          destruct (lookup sceaddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
        }
        rewrite <-beqAddrFalse in HbeqPartSce. rewrite beqAddrFalse in HbeqSceNewBlock.
        rewrite beqAddrSym in HbeqSceNewBlock. rewrite HbeqSceNewBlock. simpl.
        destruct (beqAddr (firstfreeslot pdentry) part) eqn:HbeqFirstFreePart.
        {
          rewrite <-DTL.beqAddrTrue in HbeqFirstFreePart. unfold isBE in HnewIsBEs0. subst part.
          destruct (lookup (firstfreeslot pdentry) (memory s0) beqAddr); try(congruence). destruct v; congruence.
        }
        rewrite removeDupIdentity; try(apply not_eq_sym; assumption). rewrite InternalLemmas.beqAddrTrue.
        rewrite beqAddrFalse in HbeqCurrNewBlock. rewrite HbeqCurrNewBlock. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity; try(apply not_eq_sym; assumption). simpl.
        assert(HpartNotCurrBis: currentPart <> part) by intuition. rewrite beqAddrFalse in HpartNotCurrBis.
        rewrite HpartNotCurrBis. rewrite InternalLemmas.beqAddrTrue.
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity; try(apply not_eq_sym; assumption). assumption.
      - unfold consistency1 in Hconsist. intuition.
    }
    split.
    {
      intros part HpartNotCurr HpartIsPDT. specialize(HgetChildrenEq part HpartNotCurr HpartIsPDT).
      rewrite <-HgetChildrenEq. apply getChildrenEqBEPDflagFalse with bentryShare
          (CPaddr (blockToShareInCurrPartAddr + sh1offset)); try(assumption). unfold isPDT in *. rewrite Hs.
      simpl. destruct (beqAddr sceaddr part) eqn:HbeqPartSce.
      {
        rewrite <-DTL.beqAddrTrue in HbeqPartSce. unfold isSCE in HsceIsSCEs0. subst part.
        destruct (lookup sceaddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
      }
      rewrite <-beqAddrFalse in HbeqPartSce. rewrite beqAddrFalse in HbeqSceNewBlock.
      rewrite beqAddrSym in HbeqSceNewBlock. rewrite HbeqSceNewBlock. simpl.
      destruct (beqAddr (firstfreeslot pdentry) part) eqn:HbeqFirstFreePart.
      {
        rewrite <-DTL.beqAddrTrue in HbeqFirstFreePart. unfold isBE in HnewIsBEs0. subst part.
        destruct (lookup (firstfreeslot pdentry) (memory s0) beqAddr); try(congruence). destruct v; congruence.
      }
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption). rewrite InternalLemmas.beqAddrTrue.
      rewrite beqAddrFalse in HbeqCurrNewBlock. rewrite HbeqCurrNewBlock. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption). simpl.
      assert(HpartNotCurrBis: currentPart <> part) by intuition. rewrite beqAddrFalse in HpartNotCurrBis.
      rewrite HpartNotCurrBis. rewrite InternalLemmas.beqAddrTrue.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption). assumption.
    }
    split.
    {
      intros part HpartNotCurr HpartIsPDT. specialize(HgetMappedBEq part HpartNotCurr HpartIsPDT).
      rewrite <-HgetMappedBEq. apply getMappedBlocksEqBENoChange with bentryShare; try(assumption).
      rewrite HnewB. simpl. reflexivity.
    }
    split.
    {
      intros part HpartNotCurr HpartIsPDT. specialize(HgetAccMappedBEq part HpartNotCurr HpartIsPDT).
      rewrite <-HgetAccMappedBEq. apply getAccessibleMappedBlocksEqBEAccessiblePresentNoChange with bentryShare;
          try(assumption); rewrite HnewB; simpl; reflexivity.
    }
    split.
    {
      intros part HpartNotCurr HpartIsPDT. specialize(HgetAccMappedPEq part HpartNotCurr HpartIsPDT).
      rewrite <-HgetAccMappedPEq. apply getAccessibleMappedPaddrEqBENotInPart; try(assumption).
      - unfold isPDT in *. rewrite Hs. simpl. destruct (beqAddr sceaddr part) eqn:HbeqPartSce.
        {
          rewrite <-DTL.beqAddrTrue in HbeqPartSce. unfold isSCE in HsceIsSCEs0. subst part.
          destruct (lookup sceaddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
        }
        rewrite <-beqAddrFalse in HbeqPartSce. rewrite beqAddrFalse in HbeqSceNewBlock.
        rewrite beqAddrSym in HbeqSceNewBlock. rewrite HbeqSceNewBlock. simpl.
        destruct (beqAddr (firstfreeslot pdentry) part) eqn:HbeqFirstFreePart.
        {
          rewrite <-DTL.beqAddrTrue in HbeqFirstFreePart. unfold isBE in HnewIsBEs0. subst part.
          destruct (lookup (firstfreeslot pdentry) (memory s0) beqAddr); try(congruence). destruct v; congruence.
        }
        rewrite removeDupIdentity; try(apply not_eq_sym; assumption). rewrite InternalLemmas.beqAddrTrue.
        rewrite beqAddrFalse in HbeqCurrNewBlock. rewrite HbeqCurrNewBlock. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity; try(apply not_eq_sym; assumption). simpl.
        assert(HpartNotCurrBis: currentPart <> part) by intuition. rewrite beqAddrFalse in HpartNotCurrBis.
        rewrite HpartNotCurrBis. rewrite InternalLemmas.beqAddrTrue.
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity; try(apply not_eq_sym; assumption). assumption.
      - assert(HblockInCurr: In blockToShareInCurrPartAddr (getMappedBlocks currentPart sInit)) by intuition.
        rewrite <-HgetMappedBCurrEqs0 in HblockInCurr.
        assert(HblockInCurrs: In blockToShareInCurrPartAddr (getMappedBlocks currentPart s)).
        {
          apply HgetMappedBEquiv. right. assumption.
        }
        unfold getMappedBlocks in HblockInCurrs. apply InFilterPresentInList in HblockInCurrs.
        assert(Hdisjoint: DisjointKSEntries s) by (unfold consistency1 in Hconsist; intuition).
        assert(HpartIsPDTs: isPDT part s).
        {
          unfold isPDT in *. rewrite Hs. simpl. destruct (beqAddr sceaddr part) eqn:HbeqPartSce.
          {
            rewrite <-DTL.beqAddrTrue in HbeqPartSce. unfold isSCE in HsceIsSCEs0. subst part.
            destruct (lookup sceaddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
          }
          rewrite <-beqAddrFalse in HbeqPartSce. rewrite beqAddrFalse in HbeqSceNewBlock.
          rewrite beqAddrSym in HbeqSceNewBlock. rewrite HbeqSceNewBlock. simpl.
          destruct (beqAddr (firstfreeslot pdentry) part) eqn:HbeqFirstFreePart.
          {
            rewrite <-DTL.beqAddrTrue in HbeqFirstFreePart. unfold isBE in HnewIsBEs0. subst part.
            destruct (lookup (firstfreeslot pdentry) (memory s0) beqAddr); try(congruence).
            destruct v; congruence.
          }
          rewrite removeDupIdentity; try(apply not_eq_sym; assumption). rewrite InternalLemmas.beqAddrTrue.
          rewrite beqAddrFalse in HbeqCurrNewBlock. rewrite HbeqCurrNewBlock. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
          rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
          rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
          rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
          rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
          rewrite removeDupIdentity; try(apply not_eq_sym; assumption). simpl.
          assert(HpartNotCurrBis: currentPart <> part) by intuition. rewrite beqAddrFalse in HpartNotCurrBis.
          rewrite HpartNotCurrBis. rewrite InternalLemmas.beqAddrTrue.
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
          rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
          rewrite removeDupIdentity; try(apply not_eq_sym; assumption). assumption.
        }
        specialize(Hdisjoint part currentPart HpartIsPDTs HcurrIsPDTs HpartNotCurr).
        destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
        unfold getMappedBlocks in HblockInCurr. apply InFilterPresentInList in HblockInCurr. intro Hcontra.
        specialize(Hdisjoint blockToShareInCurrPartAddr Hcontra). congruence.
    }
    intro part. rewrite <-HPDTEq. unfold isPDT. simpl.
    destruct (beqAddr blockToShareInCurrPartAddr part) eqn:HbeqBlockPart.
    + rewrite <-beqAddrTrue in HbeqBlockPart. subst part. rewrite HlookupBlocks. reflexivity.
    + rewrite <-beqAddrFalse in HbeqBlockPart. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      reflexivity.
}
  intro.
  eapply bindRev.
{ eapply weaken. eapply getKernelStructureEntriesNb.
  intros s Hprops. simpl. apply Hprops.
}
  intro kernelentriesnb.
  eapply bindRev.
{
  eapply weaken. eapply Invariants.Index.succ. simpl. intros s Hprops. split.
  - eapply Hprops.
  - assert (HleqIdx: CIndex (kernelentriesnb + 1) <= maxIdx) by apply IdxLtMaxIdx.
    unfold CIndex in HleqIdx.
    destruct (Compare_dec.le_dec (kernelentriesnb + 1) maxIdx).
    -- exact l.
    -- destruct Hprops as [Hprops Hkern]. subst kernelentriesnb.
       unfold CIndex in *.
       assert(kernelStructureEntriesNb < maxIdx-1) by apply KSEntriesNbLessThanMaxIdx.
       destruct (Compare_dec.le_dec kernelStructureEntriesNb maxIdx) ; simpl in * ; try lia.
       assert (HBigEnough: maxIdx > kernelStructureEntriesNb) by apply maxIdxBiggerThanNbOfKernels.
       unfold kernelStructureEntriesNb in HBigEnough. simpl in HBigEnough. lia.
}
  intro defaultidx. eapply bindRev.
{ (** MAL.findBlockIdxInPhysicalMPU **)
  eapply weaken. apply Invariants.findBlockIdxInPhysicalMPU.
  intros s Hprops. simpl. split. eapply Hprops. destruct Hprops as (((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & [s0 [s1 [pdentry [pdentryInter0 [pdentryInter1 [newpdentry [bentry [bentry0 [bentry1 [bentry2 [bentry3
    [bentry4 [bentry5 [bentry6 [bentryShare [bentry7 [scentry [predCurrentNbFreeSlots [sceaddr
    [newFirstFreeSlotAddr (Hs & Hprops)]]]]]]]]]]]]]]]]]]]]) & _) & _). intuition.
  assert(Hcons1: MPUsizeIsBelowMax s1) by (unfold consistency1 in *; intuition).
  intros partition MPUlist HMPU.
  assert(HMPUs1: pdentryMPU partition MPUlist s1).
  {
    unfold pdentryMPU in *. rewrite Hs in HMPU. simpl in HMPU.
    destruct (beqAddr blockToShareInCurrPartAddr partition) eqn:HbeqBlockPart; try(exfalso; congruence).
    rewrite <-beqAddrFalse in HbeqBlockPart. rewrite removeDupIdentity in HMPU; intuition.
  }
  specialize(Hcons1 partition MPUlist HMPUs1). assumption.
}
  intro blockMPURegionNb. eapply bindRev.
{ (** Internal.enableBlockInMPU **)
  eapply weaken. apply enableBlockInMPUconsist1.
  intros s Hprops. simpl.
  assert(Hconsists: consistency1 s).
  {
    destruct Hprops as ((((_ & _ & _ & _ & HlebCutStart & HlebEndCut & HsubCutEnd & HsubEndCut & Hmin & Hblock1 &
      Hblock2 & _ & [s0 [s1 [pdentry [pdentryInter0
      [pdentryInter1 [newpdentry [bentry [bentry0 [bentry1 [bentry2 [bentry3 [bentry4 [bentry5 [bentry6
      [bentryShare [bentry7 [scentry [predCurrentNbFreeSlots [sceaddr [newFirstFreeSlotAddr
      (Hs & Hprops)]]]]]]]]]]]]]]]]]]]]) & _) & _) & _).
    assert(HlookupBlocks0: lookup blockToShareInCurrPartAddr (memory s0) beqAddr = Some (BE bentryShare))
        by intuition.
    destruct (beqAddr blockToShareInCurrPartAddr nullAddr) eqn:HbeqBlockNull.
    {
      assert(Hnull: nullAddrExists s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
      unfold nullAddrExists in Hnull. unfold isPADDR in Hnull. rewrite <-DTL.beqAddrTrue in HbeqBlockNull.
      subst blockToShareInCurrPartAddr. rewrite HlookupBlocks0 in Hnull. exfalso; congruence.
    }
    destruct (beqAddr sceaddr blockToShareInCurrPartAddr) eqn:HbeqSceBlock.
    {
      assert(Hsce: isSCE sceaddr s0) by intuition. rewrite <-DTL.beqAddrTrue in HbeqSceBlock.
      subst sceaddr. unfold isSCE in Hsce. rewrite HlookupBlocks0 in Hsce. exfalso; congruence.
    }
    destruct (beqAddr idNewSubblock sceaddr) eqn:HbeqSubblockSce.
    {
      assert(HlookupSubblocks0: lookup idNewSubblock (memory s0) beqAddr = Some (BE bentry)) by intuition.
      assert(Hsce: isSCE sceaddr s0) by intuition. rewrite <-DTL.beqAddrTrue in HbeqSubblockSce.
      subst sceaddr. unfold isSCE in Hsce. rewrite HlookupSubblocks0 in Hsce. exfalso; congruence.
    }
    destruct (beqAddr currentPart idNewSubblock) eqn:HbeqCurrSubblock.
    {
      assert(HlookupCurrs0: lookup currentPart (memory s0) beqAddr = Some (PDT pdentry)) by intuition.
      assert(HlookupSubblocks0: lookup idNewSubblock (memory s0) beqAddr = Some (BE bentry)) by intuition.
      rewrite <-beqAddrTrue in HbeqCurrSubblock. subst currentPart. exfalso; congruence.
    }
    destruct (beqAddr currentPart blockToShareInCurrPartAddr) eqn:HbeqCurrBlock.
    {
      assert(HlookupCurrs0: lookup currentPart (memory s0) beqAddr = Some (PDT pdentry)) by intuition.
      rewrite <-beqAddrTrue in HbeqCurrBlock. subst currentPart. exfalso; congruence.
    }
    assert(HnewB: exists l,
                    CBlockEntry (read bentryShare) (write bentryShare) (exec bentryShare) 
                       (present bentryShare) (accessible bentryShare) (blockindex bentryShare)
                       (CBlock (startAddr (blockrange bentryShare)) cutAddr)
                    = {|
                        read := read bentryShare;
                        write := write bentryShare;
                        exec := exec bentryShare;
                        present := present bentryShare;
                        accessible := accessible bentryShare;
                        blockindex := blockindex bentryShare;
                        blockrange := CBlock (startAddr (blockrange bentryShare)) cutAddr;
                        Hidx := ADT.CBlockEntry_obligation_1 (blockindex bentryShare) l
                      |}).
    {
      unfold CBlockEntry. assert(blockindex bentryShare < kernelStructureEntriesNb) by (apply Hidx).
      destruct (Compare_dec.lt_dec (blockindex bentryShare) kernelStructureEntriesNb); try(lia). exists l.
      reflexivity.
    }
    destruct HnewB as [l HnewB].

    assert(Hs1:
        s1 =
        {|
          currentPartition := currentPartition s0;
          memory :=
            add sceaddr (SCE {| origin := blockOrigin; next := next scentry |})
              (add idNewSubblock
                 (BE
                    (CBlockEntry (read bentry5) (write bentry5) blockX (present bentry5)
                       (accessible bentry5) (blockindex bentry5) (blockrange bentry5)))
                 (add idNewSubblock
                    (BE
                       (CBlockEntry (read bentry4) blockW (exec bentry4) (present bentry4)
                          (accessible bentry4) (blockindex bentry4) (blockrange bentry4)))
                    (add idNewSubblock
                       (BE
                          (CBlockEntry blockR (write bentry3) (exec bentry3) 
                             (present bentry3) (accessible bentry3) (blockindex bentry3)
                             (blockrange bentry3)))
                       (add idNewSubblock
                          (BE
                             (CBlockEntry (read bentry2) (write bentry2) (exec bentry2)
                                (present bentry2) true (blockindex bentry2) 
                                (blockrange bentry2)))
                          (add idNewSubblock
                             (BE
                                (CBlockEntry (read bentry1) (write bentry1) 
                                   (exec bentry1) true (accessible bentry1) 
                                   (blockindex bentry1) (blockrange bentry1)))
                             (add idNewSubblock
                                (BE
                                   (CBlockEntry (read bentry0) (write bentry0) 
                                      (exec bentry0) (present bentry0) (accessible bentry0)
                                      (blockindex bentry0)
                                      (CBlock (startAddr (blockrange bentry0)) blockEndAddr)))
                                (add idNewSubblock
                                   (BE
                                      (CBlockEntry (read bentry) (write bentry) 
                                         (exec bentry) (present bentry) (accessible bentry)
                                         (blockindex bentry)
                                         (CBlock cutAddr (endAddr (blockrange bentry)))))
                                   (add currentPart
                                      (PDT
                                         {|
                                           structure := structure pdentryInter0;
                                           firstfreeslot := firstfreeslot pdentryInter0;
                                           nbfreeslots := predCurrentNbFreeSlots;
                                           nbprepare := nbprepare pdentryInter0;
                                           parent := parent pdentryInter0;
                                           MPU := MPU pdentryInter0;
                                           vidtAddr := vidtAddr pdentryInter0
                                         |})
                                      (add currentPart
                                         (PDT
                                            {|
                                              structure := structure pdentry;
                                              firstfreeslot := newFirstFreeSlotAddr;
                                              nbfreeslots := nbfreeslots pdentry;
                                              nbprepare := nbprepare pdentry;
                                              parent := parent pdentry;
                                              MPU := MPU pdentry;
                                              vidtAddr := vidtAddr pdentry
                                            |}) (memory s0) beqAddr) beqAddr) beqAddr) beqAddr)
                             beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr
        |}) by intuition.

    assert(HblockIsBEs1: isBE blockToShareInCurrPartAddr s1).
    {
      unfold isBE. rewrite Hs1. simpl. rewrite HbeqSceBlock. rewrite HbeqSubblockSce. simpl.
      destruct (beqAddr idNewSubblock blockToShareInCurrPartAddr) eqn:HbeqSubblockBlock; try(trivial).
      rewrite InternalLemmas.beqAddrTrue. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite beqAddrFalse in HbeqCurrSubblock. rewrite HbeqCurrSubblock. simpl.
      rewrite beqAddrFalse in HbeqCurrBlock. rewrite HbeqCurrBlock. rewrite InternalLemmas.beqAddrTrue.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption). rewrite HlookupBlocks0. trivial.
    }

    assert(HPDFlagBlock: sh1entryPDflag (CPaddr (blockToShareInCurrPartAddr + sh1offset)) false s) by intuition.
    assert(HPDFlagBlocks1: sh1entryPDflag (CPaddr (blockToShareInCurrPartAddr + sh1offset)) false s1)
          by intuition.

    assert(HlookupBlocks: lookup blockToShareInCurrPartAddr (memory s) beqAddr = Some (BE bentry7)) by intuition.

    assert(HlookupBlocks1: lookup blockToShareInCurrPartAddr (memory s1) beqAddr = Some(BE bentryShare)).
    {
      rewrite Hs1. simpl. rewrite HbeqSceBlock. rewrite HbeqSubblockSce. simpl.
      assert(HbeqSubblockBlock: beqAddr idNewSubblock blockToShareInCurrPartAddr = false) by intuition.
      rewrite HbeqSubblockBlock. rewrite InternalLemmas.beqAddrTrue. rewrite HbeqCurrSubblock.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption). simpl. rewrite beqAddrFalse in HbeqCurrBlock.
      rewrite HbeqCurrBlock. rewrite InternalLemmas.beqAddrTrue. rewrite <-beqAddrFalse in HbeqCurrBlock.
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption). assumption.
    }

    assert(HgetCurrEqs0: currentPartition s1 = currentPartition s0).
    { rewrite Hs1. simpl. reflexivity. }

    assert(HgetCurrEq: currentPartition s = currentPartition s1).
    { rewrite Hs. simpl. rewrite HgetCurrEqs0. reflexivity. }

    assert(HgetPartsEq: getPartitions multiplexer s = getPartitions multiplexer s1).
    {
      rewrite Hs. rewrite <-HgetCurrEqs0.
      apply getPartitionsEqBEPDflagFalse with bentryShare (CPaddr (blockToShareInCurrPartAddr + sh1offset));
          try(assumption). unfold consistency1 in *; intuition. unfold consistency1 in *; intuition.
      apply lookupSh1EntryAddr with bentryShare. assumption.
    }

    assert(nullAddrExists s).
    { (* BEGIN nullAddrExists s *)
      assert(Hcons0: nullAddrExists s1) by (unfold consistency1 in *; intuition).
      unfold nullAddrExists in *. unfold isPADDR. rewrite Hs. simpl. rewrite HbeqBlockNull.
      rewrite <-beqAddrFalse in HbeqBlockNull. rewrite removeDupIdentity; intuition.
      (* END nullAddrExists *)
    }

    assert(wellFormedFstShadowIfBlockEntry s).
    { (* BEGIN wellFormedFstShadowIfBlockEntry s *)
      assert(Hcons0: wellFormedFstShadowIfBlockEntry s1) by (unfold consistency1 in *; intuition).
      intros addr HaddrIsBE.
      assert(HaddrIsBEs1: isBE addr s1).
      {
        unfold isBE in HaddrIsBE. rewrite Hs in HaddrIsBE. simpl in HaddrIsBE.
        destruct (beqAddr blockToShareInCurrPartAddr addr) eqn:HbeqBlockAddr.
        - rewrite <-DTL.beqAddrTrue in HbeqBlockAddr. subst addr. assumption.
        - rewrite <-beqAddrFalse in HbeqBlockAddr. rewrite removeDupIdentity in HaddrIsBE; intuition.
      }
      specialize(Hcons0 addr HaddrIsBEs1). unfold isSHE in *. rewrite Hs. simpl.
      destruct (beqAddr blockToShareInCurrPartAddr (CPaddr (addr + sh1offset))) eqn:HbeqBlockSh1.
      {
        rewrite <-beqAddrTrue in HbeqBlockSh1. rewrite <-HbeqBlockSh1 in Hcons0. unfold isBE in HblockIsBEs1.
        destruct (lookup blockToShareInCurrPartAddr (memory s1) beqAddr); try(congruence).
        destruct v; congruence.
      }
      rewrite <-beqAddrFalse in HbeqBlockSh1. rewrite removeDupIdentity; intuition.
      (* END wellFormedFstShadowIfBlockEntry *)
    }

    assert(PDTIfPDFlag s).
    { (* BEGIN PDTIfPDFlag s *)
      assert(Hcons0: PDTIfPDFlag s1) by (unfold consistency1 in *; intuition).
      intros idPDchild sh1entryaddr HcheckChild.
      assert(HcheckChilds1: true = checkChild idPDchild s1 sh1entryaddr
                            /\ sh1entryAddr idPDchild sh1entryaddr s1).
      {
        unfold checkChild in *. unfold sh1entryAddr in *. rewrite Hs in HcheckChild. simpl in HcheckChild.
        destruct HcheckChild as (HcheckChild & Hsh1).
        destruct (beqAddr blockToShareInCurrPartAddr idPDchild) eqn:HbeqBlockIdChild.
        {
          rewrite <-beqAddrTrue in HbeqBlockIdChild. subst idPDchild.
          destruct (beqAddr blockToShareInCurrPartAddr sh1entryaddr) eqn:HbeqBlockSh1; try(exfalso; congruence).
          unfold isBE in HblockIsBEs1.
          destruct (lookup blockToShareInCurrPartAddr (memory s1) beqAddr); try(exfalso; congruence).
          destruct v; try(exfalso; congruence). rewrite <-beqAddrFalse in HbeqBlockSh1.
          rewrite removeDupIdentity in HcheckChild; intuition.
        }
        rewrite <-beqAddrFalse in HbeqBlockIdChild.
        rewrite removeDupIdentity in HcheckChild; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in Hsh1; try(apply not_eq_sym; assumption).
        destruct (lookup idPDchild (memory s1) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence).
        destruct (beqAddr blockToShareInCurrPartAddr sh1entryaddr) eqn:HbeqBlockSh1; try(exfalso; congruence).
        rewrite <-beqAddrFalse in HbeqBlockSh1. rewrite removeDupIdentity in HcheckChild; intuition.
      }
      specialize(Hcons0 idPDchild sh1entryaddr HcheckChilds1).
      destruct Hcons0 as (HAFlag & HPFlag & Hstart). unfold bentryAFlag in *. unfold bentryPFlag in *.
      unfold bentryStartAddr in *. unfold entryPDT in *. rewrite Hs. simpl.
      destruct (beqAddr blockToShareInCurrPartAddr idPDchild) eqn:HbeqBlockChild.
      {
        rewrite HnewB. simpl. rewrite <-beqAddrTrue in HbeqBlockChild. subst idPDchild. exfalso.
        unfold sh1entryPDflag in HPDFlagBlock. destruct HcheckChild as (HcheckChild & Hsh1).
        unfold checkChild in HcheckChild. unfold sh1entryAddr in Hsh1.
        rewrite HlookupBlocks in *. subst sh1entryaddr.
        destruct (lookup (CPaddr (blockToShareInCurrPartAddr + sh1offset)) (memory s) beqAddr); try(congruence).
        destruct v; congruence.
      }
      rewrite <-beqAddrFalse in HbeqBlockChild. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      destruct (lookup idPDchild (memory s1) beqAddr); try(exfalso; congruence).
      destruct v; try(exfalso; congruence). split. assumption. split. assumption.
      destruct Hstart as [startaddr (Hstart & HstartIsStart)]. exists startaddr. split. assumption.
      destruct (beqAddr blockToShareInCurrPartAddr (startAddr (blockrange b))) eqn:HbeqBlockStart.
      {
        rewrite <-beqAddrTrue in HbeqBlockStart. rewrite <-HbeqBlockStart in *. unfold isBE in HblockIsBEs1.
        destruct (lookup blockToShareInCurrPartAddr (memory s1) beqAddr); try(congruence). destruct v; congruence.
      }
      rewrite <-beqAddrFalse in HbeqBlockStart. rewrite removeDupIdentity; intuition.
      (* END PDTIfPDFlag *)
    }

    assert(AccessibleNoPDFlag s).
    { (* BEGIN AccessibleNoPDFlag s *)
      assert(Hcons0: AccessibleNoPDFlag s1) by (unfold consistency1 in *; intuition).
      intros block sh1entryaddr HtmpblockIsBE Hsh1 HAFlag.
      assert(HtmpblockIsBEs1: isBE block s1).
      {
        unfold isBE in *. rewrite Hs in HtmpblockIsBE. simpl in HtmpblockIsBE.
        destruct (beqAddr blockToShareInCurrPartAddr block) eqn:HbeqBlockBlock.
        - rewrite <-beqAddrTrue in HbeqBlockBlock. subst block. assumption.
        - rewrite <-beqAddrFalse in HbeqBlockBlock. rewrite removeDupIdentity in HtmpblockIsBE; intuition.
      }
      assert(Hsh1s1: sh1entryAddr block sh1entryaddr s1).
      {
        unfold sh1entryAddr in *. rewrite Hs in Hsh1. simpl in Hsh1.
        destruct (beqAddr blockToShareInCurrPartAddr block) eqn:HbeqBlockBlock.
        - rewrite <-beqAddrTrue in HbeqBlockBlock. subst block. unfold isBE in HblockIsBEs1.
          destruct (lookup blockToShareInCurrPartAddr (memory s1) beqAddr); try(congruence).
          destruct v; congruence.
        - rewrite <-beqAddrFalse in HbeqBlockBlock. rewrite removeDupIdentity in Hsh1; intuition.
      }
      assert(HAFlags1: bentryAFlag block true s1).
      {
        unfold bentryAFlag in *. rewrite Hs in HAFlag. simpl in HAFlag.
        destruct (beqAddr blockToShareInCurrPartAddr block) eqn:HbeqBlockBlock.
        - rewrite <-beqAddrTrue in HbeqBlockBlock. subst block. rewrite HlookupBlocks1.
          rewrite HnewB in HAFlag. simpl in HAFlag. assumption.
        - rewrite <-beqAddrFalse in HbeqBlockBlock. rewrite removeDupIdentity in HAFlag; intuition.
      }
      specialize(Hcons0 block sh1entryaddr HtmpblockIsBEs1 Hsh1s1 HAFlags1). unfold sh1entryPDflag in *.
      rewrite Hs. simpl. destruct (beqAddr blockToShareInCurrPartAddr sh1entryaddr) eqn:HbeqBlockSh1.
      {
        rewrite <-beqAddrTrue in HbeqBlockSh1. subst sh1entryaddr. rewrite HlookupBlocks1 in Hcons0.
        congruence.
      }
      rewrite <-beqAddrFalse in HbeqBlockSh1. rewrite removeDupIdentity; intuition.
      (* END AccessibleNoPDFlag *)
    }

    assert(FirstFreeSlotPointerIsBEAndFreeSlot s).
    { (* BEGIN FirstFreeSlotPointerIsBEAndFreeSlot s *)
      assert(Hcons0: FirstFreeSlotPointerIsBEAndFreeSlot s1) by (unfold consistency1 in *; intuition).
      intros pdentryaddr pdentrytmp HlookupPdaddr HbeqFirstNull.
      assert(HlookupPdaddrs1: lookup pdentryaddr (memory s1) beqAddr = Some (PDT pdentrytmp)).
      {
        rewrite Hs in HlookupPdaddr. simpl in HlookupPdaddr.
        destruct (beqAddr blockToShareInCurrPartAddr pdentryaddr) eqn:HbeqBlockPdaddr; try(exfalso; congruence).
        rewrite <-beqAddrFalse in HbeqBlockPdaddr. rewrite removeDupIdentity in HlookupPdaddr; intuition.
      }
      specialize(Hcons0 pdentryaddr pdentrytmp HlookupPdaddrs1 HbeqFirstNull). unfold isBE in *.
      unfold isFreeSlot in *. destruct Hcons0 as (HfirstIsBE & HfirstIsFree).
      destruct (beqAddr blockToShareInCurrPartAddr (firstfreeslot pdentrytmp)) eqn:HbeqBlockFirst.
      - rewrite <-beqAddrTrue in HbeqBlockFirst. rewrite <-HbeqBlockFirst in *. rewrite HlookupBlocks.
        rewrite HlookupBlocks1 in HfirstIsFree. rewrite Hs. simpl.
        destruct (beqAddr blockToShareInCurrPartAddr (CPaddr (blockToShareInCurrPartAddr + sh1offset)))
            eqn:HbeqBlockBlockSh1.
        {
          rewrite <-beqAddrTrue in HbeqBlockBlockSh1. rewrite <-HbeqBlockBlockSh1 in *.
          rewrite HlookupBlocks1 in HfirstIsFree. exfalso; congruence.
        }
        rewrite <-beqAddrFalse in HbeqBlockBlockSh1. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
        destruct (lookup (CPaddr (blockToShareInCurrPartAddr + sh1offset)) (memory s1) beqAddr);
            try(exfalso; congruence). destruct v; try(exfalso; congruence).
        destruct (beqAddr blockToShareInCurrPartAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)))
            eqn:HbeqBlockBlockSce.
        {
          rewrite <-beqAddrTrue in HbeqBlockBlockSce. rewrite <-HbeqBlockBlockSce in *.
          rewrite HlookupBlocks1 in HfirstIsFree. exfalso; congruence.
        }
        rewrite <-beqAddrFalse in HbeqBlockBlockSce. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
        assert(Hbentry7: bentry7 = CBlockEntry (read bentryShare) (write bentryShare) (exec bentryShare)
                    (present bentryShare) (accessible bentryShare) (blockindex bentryShare)
                    (CBlock (startAddr (blockrange bentryShare)) cutAddr)) by intuition.
        rewrite HnewB in Hbentry7. rewrite Hbentry7. simpl. unfold CBlock.
        assert(cutAddr <= maxAddr) by (apply Hp). rewrite <-maxIdxEqualMaxAddr in *.
        destruct (Compare_dec.le_dec (cutAddr - startAddr (blockrange bentryShare)) maxIdx); try(lia). simpl.
        intuition.
      - rewrite Hs. simpl. rewrite HbeqBlockFirst. rewrite <-beqAddrFalse in HbeqBlockFirst.
        rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
        destruct (beqAddr blockToShareInCurrPartAddr (CPaddr (firstfreeslot pdentrytmp + sh1offset)))
            eqn:HbeqBlockSh1.
        {
          rewrite <-beqAddrTrue in HbeqBlockSh1. rewrite <-HbeqBlockSh1 in *.
          rewrite HlookupBlocks1 in HfirstIsFree. intuition.
        }
        rewrite <-beqAddrFalse in HbeqBlockSh1. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
        destruct (lookup (firstfreeslot pdentrytmp) (memory s1) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence).
        destruct (lookup (CPaddr (firstfreeslot pdentrytmp + sh1offset)) (memory s1) beqAddr);
            try(exfalso; congruence). destruct v; try(exfalso; congruence).
        destruct (beqAddr blockToShareInCurrPartAddr (CPaddr (firstfreeslot pdentrytmp + scoffset)))
            eqn:HbeqBlockSce.
        {
          rewrite <-beqAddrTrue in HbeqBlockSce. rewrite <-HbeqBlockSce in *.
          rewrite HlookupBlocks1 in HfirstIsFree. exfalso; congruence.
        }
        rewrite <-beqAddrFalse in HbeqBlockSce. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
        intuition.
      (* END FirstFreeSlotPointerIsBEAndFreeSlot *)
    }

    assert(multiplexerIsPDT s).
    { (* BEGIN multiplexerIsPDT s *)
      assert(Hcons0: multiplexerIsPDT s1) by (unfold consistency1 in *; intuition).
      unfold multiplexerIsPDT in *. unfold isPDT in *. rewrite Hs. simpl.
      destruct (beqAddr blockToShareInCurrPartAddr multiplexer) eqn:HbeqBlockMult.
      {
        rewrite <-beqAddrTrue in HbeqBlockMult. subst blockToShareInCurrPartAddr.
        rewrite HlookupBlocks1 in Hcons0. congruence.
      }
      rewrite <-beqAddrFalse in HbeqBlockMult. rewrite removeDupIdentity; intuition.
      (* END multiplexerIsPDT *)
    }

    assert(currentPartitionInPartitionsList s).
    { (* BEGIN currentPartitionInPartitionsList s *)
      assert(Hcons0: currentPartitionInPartitionsList s1) by (unfold consistency1 in *; intuition).
      unfold currentPartitionInPartitionsList in *. rewrite HgetPartsEq. rewrite HgetCurrEq. assumption.
      (* END currentPartitionInPartitionsList *)
    }

    assert(wellFormedShadowCutIfBlockEntry s).
    { (* BEGIN wellFormedShadowCutIfBlockEntry s *)
      assert(Hcons0: wellFormedShadowCutIfBlockEntry s1) by (unfold consistency1 in *; intuition).
      intros addr HaddrIsBE.
      assert(HaddrIsBEs1: isBE addr s1).
      {
        unfold isBE in *. rewrite Hs in HaddrIsBE. simpl in HaddrIsBE.
        destruct (beqAddr blockToShareInCurrPartAddr addr) eqn:HbeqBlockBlock.
        - rewrite <-beqAddrTrue in HbeqBlockBlock. subst addr. assumption.
        - rewrite <-beqAddrFalse in HbeqBlockBlock. rewrite removeDupIdentity in HaddrIsBE; intuition.
      }
      specialize(Hcons0 addr HaddrIsBEs1). destruct Hcons0 as [scentryaddr (HsceIsSCE & Hsce)].
      exists scentryaddr. split; try(assumption). unfold isSCE in *. rewrite Hs. simpl.
      destruct (beqAddr blockToShareInCurrPartAddr scentryaddr) eqn:HbeqBlockSce.
      {
        rewrite <-beqAddrTrue in HbeqBlockSce. rewrite <-HbeqBlockSce in *. rewrite HlookupBlocks1 in HsceIsSCE.
        congruence.
      }
      rewrite <-beqAddrFalse in HbeqBlockSce. rewrite removeDupIdentity; intuition.
      (* END wellFormedShadowCutIfBlockEntry *)
    }

    assert(BlocksRangeFromKernelStartIsBE s).
    { (* BEGIN BlocksRangeFromKernelStartIsBE s *)
      assert(Hcons0: BlocksRangeFromKernelStartIsBE s1) by (unfold consistency1 in *; intuition).
      intros kernelentryaddr blockidx HkernIsKS HidxBounded.
      assert(HkernIsKSs1: isKS kernelentryaddr s1).
      {
        unfold isKS in *. rewrite Hs in HkernIsKS. simpl in HkernIsKS.
        destruct (beqAddr blockToShareInCurrPartAddr kernelentryaddr) eqn:HbeqBlockKern.
        - rewrite <-beqAddrTrue in HbeqBlockKern. subst kernelentryaddr. rewrite HnewB in HkernIsKS.
          simpl in HkernIsKS. rewrite HlookupBlocks1. assumption.
        - rewrite <-beqAddrFalse in HbeqBlockKern. rewrite removeDupIdentity in HkernIsKS; intuition.
      }
      specialize(Hcons0 kernelentryaddr blockidx HkernIsKSs1 HidxBounded). unfold isBE in *.
      rewrite Hs. simpl. destruct (beqAddr blockToShareInCurrPartAddr (CPaddr (kernelentryaddr + blockidx)))
          eqn:HbeqBlocKernIdx; try(trivial).
      rewrite <-beqAddrFalse in HbeqBlocKernIdx. rewrite removeDupIdentity; intuition.
      (* END BlocksRangeFromKernelStartIsBE *)
    }

    assert(KernelStructureStartFromBlockEntryAddrIsKS s).
    { (* BEGIN KernelStructureStartFromBlockEntryAddrIsKS s *)
      assert(Hcons0: KernelStructureStartFromBlockEntryAddrIsKS s1) by (unfold consistency1 in *; intuition).
      intros block blockidx HblocktmpIsBE HblockIdx.
      assert(HblocktmpIsBEs1: isBE block s1).
      {
        unfold isBE in *. rewrite Hs in HblocktmpIsBE. simpl in HblocktmpIsBE.
        destruct (beqAddr blockToShareInCurrPartAddr block) eqn:HbeqBlockBlock.
        - rewrite <-beqAddrTrue in HbeqBlockBlock. subst block. assumption.
        - rewrite <-beqAddrFalse in HbeqBlockBlock. rewrite removeDupIdentity in HblocktmpIsBE; intuition.
      }
      assert(HblockIdxs1: bentryBlockIndex block blockidx s1).
      {
        unfold bentryBlockIndex in *. rewrite Hs in HblockIdx. simpl in HblockIdx.
        destruct (beqAddr blockToShareInCurrPartAddr block) eqn:HbeqBlockBlock.
        - rewrite <-beqAddrTrue in HbeqBlockBlock. subst block. rewrite HnewB in HblockIdx. simpl in HblockIdx.
          rewrite HlookupBlocks1. assumption.
        - rewrite <-beqAddrFalse in HbeqBlockBlock. rewrite removeDupIdentity in HblockIdx; intuition.
      }
      specialize(Hcons0 block blockidx HblocktmpIsBEs1 HblockIdxs1). unfold isKS in *. rewrite Hs. simpl.
      destruct (beqAddr blockToShareInCurrPartAddr (CPaddr (block - blockidx))) eqn:HbeqBlockBlockMIdx.
      - rewrite <-beqAddrTrue in HbeqBlockBlockMIdx. rewrite <-HbeqBlockBlockMIdx in Hcons0.
        rewrite HlookupBlocks1 in Hcons0. rewrite HnewB. simpl. assumption.
      - rewrite <-beqAddrFalse in HbeqBlockBlockMIdx. rewrite removeDupIdentity; intuition.
      (* END KernelStructureStartFromBlockEntryAddrIsKS *)
    }

    assert(sh1InChildLocationIsBE s).
    { (* BEGIN sh1InChildLocationIsBE s *)
      assert(Hcons0: sh1InChildLocationIsBE s1) by (unfold consistency1 in *; intuition).
      intros sh1entryaddr sh1entry HlookupSh1 HchildLoc.
      assert(HlookupSh1s1: lookup sh1entryaddr (memory s1) beqAddr = Some (SHE sh1entry)).
      {
        rewrite Hs in HlookupSh1. simpl in HlookupSh1.
        destruct (beqAddr blockToShareInCurrPartAddr sh1entryaddr) eqn:HbeqBlockSh1; try(exfalso; congruence).
        rewrite <-beqAddrFalse in HbeqBlockSh1. rewrite removeDupIdentity in HlookupSh1; intuition.
      }
      specialize(Hcons0 sh1entryaddr sh1entry HlookupSh1s1 HchildLoc). unfold isBE in *. rewrite Hs. simpl.
      destruct (beqAddr blockToShareInCurrPartAddr (inChildLocation sh1entry)) eqn:HbeqBlockChildLoc; trivial.
      rewrite <-beqAddrFalse in HbeqBlockChildLoc. rewrite removeDupIdentity; intuition.
      (* END sh1InChildLocationIsBE *)
    }

    assert(StructurePointerIsKS s).
    { (* BEGIN StructurePointerIsKS s *)
      assert(Hcons0: StructurePointerIsKS s1) by (unfold consistency1 in *; intuition).
      intros entryaddr entry HlookupEntry Hstruct.
      assert(HlookupEntrys1: lookup entryaddr (memory s1) beqAddr = Some (PDT entry)).
      {
        rewrite Hs in HlookupEntry. simpl in HlookupEntry.
        destruct (beqAddr blockToShareInCurrPartAddr entryaddr) eqn:HbeqBlockEntry; try(exfalso; congruence).
        rewrite <-beqAddrFalse in HbeqBlockEntry. rewrite removeDupIdentity in HlookupEntry; intuition.
      }
      specialize(Hcons0 entryaddr entry HlookupEntrys1 Hstruct). unfold isKS in *. rewrite Hs. simpl.
      destruct (beqAddr blockToShareInCurrPartAddr (structure entry)) eqn:HbeqBlockStruct.
      - rewrite <-beqAddrTrue in HbeqBlockStruct. rewrite <-HbeqBlockStruct in Hcons0. rewrite HnewB. simpl.
        rewrite HlookupBlocks1 in Hcons0. assumption.
      - rewrite <-beqAddrFalse in HbeqBlockStruct. rewrite removeDupIdentity; intuition.
      (* END StructurePointerIsKS *)
    }

    assert(NextKSIsKS s).
    { (* BEGIN NextKSIsKS s *)
      assert(Hcons0: NextKSIsKS s1) by (unfold consistency1 in *; intuition).
      intros addr nextKSaddr nextKS HaddrIsKS HnextAddr HnextEntry HbeqNextNull.
      assert(HaddrIsKSs1: isKS addr s1).
      {
        unfold isKS in *. rewrite Hs in HaddrIsKS. simpl in HaddrIsKS.
        destruct (beqAddr blockToShareInCurrPartAddr addr) eqn:HbeqBlockAddr.
        - rewrite <-beqAddrTrue in HbeqBlockAddr. subst addr. rewrite HlookupBlocks1. rewrite HnewB in HaddrIsKS.
          simpl in HaddrIsKS. assumption.
        - rewrite <-beqAddrFalse in HbeqBlockAddr. rewrite removeDupIdentity in HaddrIsKS; intuition.
      }
      assert(HnextAddrs1: nextKSAddr addr nextKSaddr s1).
      {
        unfold nextKSAddr in *. rewrite Hs in HnextAddr. simpl in HnextAddr.
        destruct (beqAddr blockToShareInCurrPartAddr addr) eqn:HbeqBlockAddr.
        - rewrite <-beqAddrTrue in HbeqBlockAddr. subst addr. rewrite HlookupBlocks1. assumption.
        - rewrite <-beqAddrFalse in HbeqBlockAddr. rewrite removeDupIdentity in HnextAddr; intuition.
      }
      assert(HnextEntrys1: nextKSentry nextKSaddr nextKS s1).
      {
        unfold nextKSentry in *. rewrite Hs in HnextEntry. simpl in HnextEntry.
        destruct (beqAddr blockToShareInCurrPartAddr nextKSaddr) eqn:HbeqBlockNextAddr; try(exfalso; congruence).
        rewrite <-beqAddrFalse in HbeqBlockNextAddr. rewrite removeDupIdentity in HnextEntry; intuition.
      }
      specialize(Hcons0 addr nextKSaddr nextKS HaddrIsKSs1 HnextAddrs1 HnextEntrys1 HbeqNextNull).
      unfold isKS in *. rewrite Hs. simpl.
      destruct (beqAddr blockToShareInCurrPartAddr nextKS) eqn:HbeqBlockNext.
      - rewrite <-beqAddrTrue in HbeqBlockNext. subst nextKS. rewrite HlookupBlocks1 in Hcons0. rewrite HnewB.
        simpl. assumption.
      - rewrite <-beqAddrFalse in HbeqBlockNext. rewrite removeDupIdentity; intuition.
      (* END NextKSIsKS *)
    }

    assert(NextKSOffsetIsPADDR s).
    { (* BEGIN NextKSOffsetIsPADDR s *)
      assert(Hcons0: NextKSOffsetIsPADDR s1) by (unfold consistency1 in *; intuition).
      intros addr nextksaddr HaddrIsKS Hnext.
      assert(HaddrIsKSs1: isKS addr s1).
      {
        unfold isKS in *. rewrite Hs in HaddrIsKS. simpl in HaddrIsKS.
        destruct (beqAddr blockToShareInCurrPartAddr addr) eqn:HbeqBlockAddr.
        - rewrite <-beqAddrTrue in HbeqBlockAddr. subst addr. rewrite HlookupBlocks1. rewrite HnewB in HaddrIsKS.
          simpl in HaddrIsKS. assumption.
        - rewrite <-beqAddrFalse in HbeqBlockAddr. rewrite removeDupIdentity in HaddrIsKS; intuition.
      }
      assert(Hnexts1: nextKSAddr addr nextksaddr s1).
      {
        unfold nextKSAddr in *. rewrite Hs in Hnext. simpl in Hnext.
        destruct (beqAddr blockToShareInCurrPartAddr addr) eqn:HbeqBlockAddr.
        - rewrite <-beqAddrTrue in HbeqBlockAddr. subst addr. rewrite HlookupBlocks1. assumption.
        - rewrite <-beqAddrFalse in HbeqBlockAddr. rewrite removeDupIdentity in Hnext; intuition.
      }
      specialize(Hcons0 addr nextksaddr HaddrIsKSs1 Hnexts1). destruct Hcons0 as (HnextIsPADDR & HbeqNextNull).
      split; try(assumption). unfold isPADDR in *. rewrite Hs. simpl.
      destruct (beqAddr blockToShareInCurrPartAddr nextksaddr) eqn:HbeqBlockNext.
      {
        rewrite <-beqAddrTrue in HbeqBlockNext. subst nextksaddr. rewrite HlookupBlocks1 in HnextIsPADDR.
        congruence.
      }
      rewrite <-beqAddrFalse in HbeqBlockNext. rewrite removeDupIdentity; intuition.
      (* END NextKSOffsetIsPADDR *)
    }

    assert(NoDupInFreeSlotsList s).
    { (* BEGIN NoDupInFreeSlotsList s *)
      assert(Hcons0: NoDupInFreeSlotsList s1) by (unfold consistency1 in *; intuition).
      intros pd pdentrytmp HlookupPd.
      assert(HlookupPds1: lookup pd (memory s1) beqAddr = Some (PDT pdentrytmp)).
      {
        rewrite Hs in HlookupPd. simpl in HlookupPd.
        destruct (beqAddr blockToShareInCurrPartAddr pd) eqn:HbeqBlockPd; try(exfalso; congruence).
        rewrite <-beqAddrFalse in HbeqBlockPd. rewrite removeDupIdentity in HlookupPd; intuition.
      }
      specialize(Hcons0 pd pdentrytmp HlookupPds1). destruct Hcons0 as [freeList (Hlist & HwellFormed & HnoDup)].
      assert(HgetFreeListEq: getFreeSlotsList pd s = getFreeSlotsList pd s1).
      {
        unfold getFreeSlotsList in *. rewrite HlookupPd. rewrite HlookupPds1 in *.
        destruct (beqAddr (firstfreeslot pdentrytmp) nullAddr) eqn:HbeqFirstFreeNull; try(reflexivity).
        subst freeList. rewrite Hs. rewrite <-HgetCurrEqs0. apply getFreeSlotsListRecEqBE; try(assumption).
        - assert(HfirstFreeIsFree: FirstFreeSlotPointerIsBEAndFreeSlot s) by intuition.
          rewrite <-beqAddrFalse in HbeqFirstFreeNull.
          specialize(HfirstFreeIsFree pd pdentrytmp HlookupPd HbeqFirstFreeNull).
          destruct HfirstFreeIsFree as (_ & HfirstFreeIsFree). unfold isFreeSlot in HfirstFreeIsFree.
          intro Hcontra. rewrite Hcontra in *. rewrite HlookupBlocks in HfirstFreeIsFree.
          destruct (lookup (CPaddr (blockToShareInCurrPartAddr + sh1offset)) (memory s) beqAddr);
              try(congruence). destruct v; try(congruence).
          destruct (lookup (CPaddr (blockToShareInCurrPartAddr + scoffset)) (memory s) beqAddr);
              try(congruence). destruct v; try(congruence).
          assert(HPFlag: bentryPFlag blockToShareInCurrPartAddr true s0) by intuition.
          unfold bentryPFlag in HPFlag. rewrite HlookupBlocks0 in HPFlag.
          destruct HfirstFreeIsFree as (_ & _ & _ & _ & Hpresent & _).
          assert(Hbentry7: bentry7 = CBlockEntry (read bentryShare) (write bentryShare) (exec bentryShare)
                                        (present bentryShare) (accessible bentryShare) (blockindex bentryShare)
                                        (CBlock (startAddr (blockrange bentryShare)) cutAddr)) by intuition.
          rewrite Hbentry7 in Hpresent. rewrite HnewB in Hpresent. simpl in Hpresent. congruence.
        - reflexivity.
        - intro Hcontra.
          assert(Hcontra2: In blockToShareInCurrPartAddr (filterOptionPaddr (getFreeSlotsList pd s1))).
          {
            unfold getFreeSlotsList. rewrite HlookupPds1. rewrite HbeqFirstFreeNull. assumption.
          }
          assert(HblockIsFree: isFreeSlot blockToShareInCurrPartAddr s1).
          {
            assert(HfreeSlotsList: freeSlotsListIsFreeSlot s1) by (unfold consistency1 in *; intuition).
            specialize(HfreeSlotsList pd blockToShareInCurrPartAddr (getFreeSlotsList pd s1)
                (filterOptionPaddr (getFreeSlotsList pd s1))). apply HfreeSlotsList.
            - unfold isPDT. rewrite HlookupPds1. trivial.
            - split; try(reflexivity). unfold getFreeSlotsList. rewrite HlookupPds1. rewrite HbeqFirstFreeNull.
              assumption.
            - split; try(reflexivity). assumption.
            - rewrite <-beqAddrFalse in HbeqBlockNull. assumption.
          }
          unfold isFreeSlot in HblockIsFree. rewrite HlookupBlocks1 in HblockIsFree.
          destruct (lookup (CPaddr (blockToShareInCurrPartAddr + sh1offset)) (memory s1) beqAddr);
              try(congruence). destruct v; try(congruence).
          destruct (lookup (CPaddr (blockToShareInCurrPartAddr + scoffset)) (memory s1) beqAddr);
              try(congruence). destruct v; try(congruence).
          assert(HPFlag: bentryPFlag blockToShareInCurrPartAddr true s0) by intuition.
          unfold bentryPFlag in HPFlag. rewrite HlookupBlocks0 in HPFlag.
          destruct HblockIsFree as (_ & _ & _ & _ & Hpresent & _). congruence.
      }
      rewrite HgetFreeListEq. exists freeList. intuition.
      (* END NoDupInFreeSlotsList *)
    }

    assert(freeSlotsListIsFreeSlot s).
    { (* BEGIN freeSlotsListIsFreeSlot s *)
      assert(Hcons0: freeSlotsListIsFreeSlot s1) by (unfold consistency1 in *; intuition).
      intros pd freeslotaddr optionFreeList freeList HpdIsPDT HfreeList HaddrInFreeList HaddrNotNull.
      assert(HlookupPdEq: lookup pd (memory s) beqAddr = lookup pd (memory s1) beqAddr).
      {
        unfold isPDT in HpdIsPDT. rewrite Hs in HpdIsPDT. simpl in HpdIsPDT. rewrite Hs. simpl.
        destruct (beqAddr blockToShareInCurrPartAddr pd) eqn:HbeqBlockPd; try(exfalso; congruence).
        rewrite <-beqAddrFalse in HbeqBlockPd. rewrite removeDupIdentity; intuition.
      }
      assert(HpdIsPDTs1: isPDT pd s1).
      { unfold isPDT. rewrite <-HlookupPdEq. assumption. }
      assert(HfreeLists1: optionFreeList = getFreeSlotsList pd s1
                          /\ wellFormedFreeSlotsList optionFreeList <> False).
      {
        destruct HfreeList as (HfreeList & HwellFormed). split; try(assumption).
        assert(HgetFreeListEq: getFreeSlotsList pd s = getFreeSlotsList pd s1).
        {
          unfold getFreeSlotsList in *. rewrite HlookupPdEq in *.
          destruct (lookup pd (memory s1) beqAddr) eqn:HlookupPd; try(reflexivity). destruct v; try(reflexivity).
          destruct (beqAddr (firstfreeslot p) nullAddr) eqn:HbeqFirstFreeNull; try(reflexivity).
          subst optionFreeList. rewrite Hs. rewrite <-HgetCurrEqs0.
          assert(HnoDups1: NoDupInFreeSlotsList s1) by (unfold consistency1 in *; intuition).
          specialize(HnoDups1 pd p HlookupPd).
          destruct HnoDups1 as [optionListProp (HoptionList & Hwell & HnoDup)].
          unfold getFreeSlotsList in HoptionList. rewrite HlookupPd in HoptionList.
          rewrite HbeqFirstFreeNull in HoptionList. subst optionListProp.
          apply getFreeSlotsListRecEqBE; try(assumption).
          - assert(HfirstFreeIsFree: FirstFreeSlotPointerIsBEAndFreeSlot s) by intuition.
            rewrite <-beqAddrFalse in HbeqFirstFreeNull.
            specialize(HfirstFreeIsFree pd p HlookupPdEq HbeqFirstFreeNull).
            destruct HfirstFreeIsFree as (_ & HfirstFreeIsFree). unfold isFreeSlot in HfirstFreeIsFree.
            intro Hcontra. rewrite Hcontra in *. rewrite HlookupBlocks in HfirstFreeIsFree.
            destruct (lookup (CPaddr (blockToShareInCurrPartAddr + sh1offset)) (memory s) beqAddr);
                try(congruence). destruct v; try(congruence).
            destruct (lookup (CPaddr (blockToShareInCurrPartAddr + scoffset)) (memory s) beqAddr);
                try(congruence). destruct v; try(congruence).
            assert(HPFlag: bentryPFlag blockToShareInCurrPartAddr true s0) by intuition.
            unfold bentryPFlag in HPFlag. rewrite HlookupBlocks0 in HPFlag.
            destruct HfirstFreeIsFree as (_ & _ & _ & _ & Hpresent & _).
            assert(Hbentry7: bentry7 = CBlockEntry (read bentryShare) (write bentryShare) (exec bentryShare)
                                          (present bentryShare) (accessible bentryShare) (blockindex bentryShare)
                                          (CBlock (startAddr (blockrange bentryShare)) cutAddr)) by intuition.
            rewrite Hbentry7 in Hpresent. rewrite HnewB in Hpresent. simpl in Hpresent. congruence.
          - reflexivity.
          - intro Hcontra.
            assert(Hcontra2: In blockToShareInCurrPartAddr (filterOptionPaddr (getFreeSlotsList pd s1))).
            {
              unfold getFreeSlotsList. rewrite HlookupPd. rewrite HbeqFirstFreeNull. assumption.
            }
            assert(HblockIsFree: isFreeSlot blockToShareInCurrPartAddr s1).
            {
              assert(HfreeSlotsList: freeSlotsListIsFreeSlot s1) by (unfold consistency1 in *; intuition).
              specialize(HfreeSlotsList pd blockToShareInCurrPartAddr (getFreeSlotsList pd s1)
                  (filterOptionPaddr (getFreeSlotsList pd s1))). apply HfreeSlotsList.
              - unfold isPDT. rewrite HlookupPd. trivial.
              - split; try(reflexivity). unfold getFreeSlotsList. rewrite HlookupPd. rewrite HbeqFirstFreeNull.
                assumption.
              - split; try(reflexivity). assumption.
              - rewrite <-beqAddrFalse in HbeqBlockNull. assumption.
            }
            unfold isFreeSlot in HblockIsFree. rewrite HlookupBlocks1 in HblockIsFree.
            destruct (lookup (CPaddr (blockToShareInCurrPartAddr + sh1offset)) (memory s1) beqAddr);
                try(congruence). destruct v; try(congruence).
            destruct (lookup (CPaddr (blockToShareInCurrPartAddr + scoffset)) (memory s1) beqAddr);
                try(congruence). destruct v; try(congruence).
            assert(HPFlag: bentryPFlag blockToShareInCurrPartAddr true s0) by intuition.
            unfold bentryPFlag in HPFlag. rewrite HlookupBlocks0 in HPFlag.
            destruct HblockIsFree as (_ & _ & _ & _ & Hpresent & _). congruence.
        }
        rewrite <-HgetFreeListEq. assumption.
      }
      specialize(Hcons0 pd freeslotaddr optionFreeList freeList HpdIsPDTs1 HfreeLists1 HaddrInFreeList
          HaddrNotNull). unfold isFreeSlot in *. rewrite Hs. simpl.
      destruct (beqAddr blockToShareInCurrPartAddr freeslotaddr) eqn:HbeqBlockFree.
      {
        exfalso. rewrite <-beqAddrTrue in HbeqBlockFree. subst freeslotaddr. rewrite HlookupBlocks1 in Hcons0.
        destruct (lookup (CPaddr (blockToShareInCurrPartAddr + sh1offset)) (memory s1) beqAddr);
            try(congruence). destruct v; try(congruence).
        destruct (lookup (CPaddr (blockToShareInCurrPartAddr + scoffset)) (memory s1) beqAddr);
            try(congruence). destruct v; try(congruence).
        assert(HPFlag: bentryPFlag blockToShareInCurrPartAddr true s0) by intuition.
        unfold bentryPFlag in HPFlag. rewrite HlookupBlocks0 in HPFlag.
        destruct Hcons0 as (_ & _ & _ & _ & Hpresent & _). congruence.
      }
      rewrite <-beqAddrFalse in HbeqBlockFree. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      destruct (lookup freeslotaddr (memory s1) beqAddr); try(congruence). destruct v; try(congruence).
      destruct (beqAddr blockToShareInCurrPartAddr (CPaddr (freeslotaddr + sh1offset))) eqn:HbeqBlockSh1.
      {
        rewrite <-beqAddrTrue in HbeqBlockSh1. rewrite <-HbeqBlockSh1 in Hcons0. rewrite HlookupBlocks1 in Hcons0.
        congruence.
      }
      rewrite <-beqAddrFalse in HbeqBlockSh1. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      destruct (lookup (CPaddr (freeslotaddr + sh1offset)) (memory s1) beqAddr); try(congruence).
      destruct v; try(congruence).
      destruct (beqAddr blockToShareInCurrPartAddr (CPaddr (freeslotaddr + scoffset))) eqn:HbeqBlockSce.
      {
        rewrite <-beqAddrTrue in HbeqBlockSce. rewrite <-HbeqBlockSce in Hcons0. rewrite HlookupBlocks1 in Hcons0.
        congruence.
      }
      rewrite <-beqAddrFalse in HbeqBlockSce. rewrite removeDupIdentity; intuition.
      (* END freeSlotsListIsFreeSlot *)
    }

    assert(DisjointFreeSlotsLists s).
    { (* BEGIN DisjointFreeSlotsLists s *)
      assert(Hcons0: DisjointFreeSlotsLists s1) by (unfold consistency1 in *; intuition).
      intros pd1 pd2 Hpd1IsPDT Hpd2IsPDT HbeqPd1Pd2.
      assert(HlookupPd1Eq: lookup pd1 (memory s) beqAddr = lookup pd1 (memory s1) beqAddr).
      {
        unfold isPDT in Hpd1IsPDT. rewrite Hs in Hpd1IsPDT. simpl in Hpd1IsPDT. rewrite Hs. simpl.
        destruct (beqAddr blockToShareInCurrPartAddr pd1) eqn:HbeqBlockPd1; try(exfalso; congruence).
        rewrite <-beqAddrFalse in HbeqBlockPd1. rewrite removeDupIdentity; intuition.
      }
      assert(Hpd1IsPDTs1: isPDT pd1 s1).
      { unfold isPDT. rewrite <-HlookupPd1Eq. assumption. }
      assert(HlookupPd2Eq: lookup pd2 (memory s) beqAddr = lookup pd2 (memory s1) beqAddr).
      {
        unfold isPDT in Hpd2IsPDT. rewrite Hs in Hpd2IsPDT. simpl in Hpd2IsPDT. rewrite Hs. simpl.
        destruct (beqAddr blockToShareInCurrPartAddr pd2) eqn:HbeqBlockPd2; try(exfalso; congruence).
        rewrite <-beqAddrFalse in HbeqBlockPd2. rewrite removeDupIdentity; intuition.
      }
      assert(Hpd2IsPDTs1: isPDT pd2 s1).
      { unfold isPDT. rewrite <-HlookupPd2Eq. assumption. }
      specialize(Hcons0 pd1 pd2 Hpd1IsPDTs1 Hpd2IsPDTs1 HbeqPd1Pd2).
      destruct Hcons0 as [list1 [list2 (Hlist1 & Hwell1 & Hlist2 & Hwell2 & Hdisjoint)]]. exists list1.
      exists list2. subst list1. subst list2.
      assert(HgetFreeListEq1: getFreeSlotsList pd1 s = getFreeSlotsList pd1 s1).
      {
        unfold getFreeSlotsList in *. rewrite HlookupPd1Eq in *.
        destruct (lookup pd1 (memory s1) beqAddr) eqn:HlookupPd1; try(reflexivity). destruct v; try(reflexivity).
        destruct (beqAddr (firstfreeslot p) nullAddr) eqn:HbeqFirstFreeNull; try(reflexivity).
        rewrite Hs. rewrite <-HgetCurrEqs0.
        assert(HnoDups1: NoDupInFreeSlotsList s1) by (unfold consistency1 in *; intuition).
        specialize(HnoDups1 pd1 p HlookupPd1).
        destruct HnoDups1 as [optionListProp (HoptionList & Hwell & HnoDup)].
        unfold getFreeSlotsList in HoptionList. rewrite HlookupPd1 in HoptionList.
        rewrite HbeqFirstFreeNull in HoptionList. subst optionListProp.
        apply getFreeSlotsListRecEqBE; try(assumption).
        - assert(HfirstFreeIsFree: FirstFreeSlotPointerIsBEAndFreeSlot s) by intuition.
          rewrite <-beqAddrFalse in HbeqFirstFreeNull.
          specialize(HfirstFreeIsFree pd1 p HlookupPd1Eq HbeqFirstFreeNull).
          destruct HfirstFreeIsFree as (_ & HfirstFreeIsFree). unfold isFreeSlot in HfirstFreeIsFree.
          intro Hcontra. rewrite Hcontra in *. rewrite HlookupBlocks in HfirstFreeIsFree.
          destruct (lookup (CPaddr (blockToShareInCurrPartAddr + sh1offset)) (memory s) beqAddr);
              try(congruence). destruct v; try(congruence).
          destruct (lookup (CPaddr (blockToShareInCurrPartAddr + scoffset)) (memory s) beqAddr);
              try(congruence). destruct v; try(congruence).
          assert(HPFlag: bentryPFlag blockToShareInCurrPartAddr true s0) by intuition.
          unfold bentryPFlag in HPFlag. rewrite HlookupBlocks0 in HPFlag.
          destruct HfirstFreeIsFree as (_ & _ & _ & _ & Hpresent & _).
          assert(Hbentry7: bentry7 = CBlockEntry (read bentryShare) (write bentryShare) (exec bentryShare)
                                        (present bentryShare) (accessible bentryShare) (blockindex bentryShare)
                                        (CBlock (startAddr (blockrange bentryShare)) cutAddr)) by intuition.
          rewrite Hbentry7 in Hpresent. rewrite HnewB in Hpresent. simpl in Hpresent. congruence.
        - reflexivity.
        - intro Hcontra.
          assert(Hcontra2: In blockToShareInCurrPartAddr (filterOptionPaddr (getFreeSlotsList pd1 s1))).
          {
            unfold getFreeSlotsList. rewrite HlookupPd1. rewrite HbeqFirstFreeNull. assumption.
          }
          assert(HblockIsFree: isFreeSlot blockToShareInCurrPartAddr s1).
          {
            assert(HfreeSlotsList: freeSlotsListIsFreeSlot s1) by (unfold consistency1 in *; intuition).
            specialize(HfreeSlotsList pd1 blockToShareInCurrPartAddr (getFreeSlotsList pd1 s1)
                (filterOptionPaddr (getFreeSlotsList pd1 s1))). apply HfreeSlotsList.
            - unfold isPDT. rewrite HlookupPd1. trivial.
            - split; try(reflexivity). unfold getFreeSlotsList. rewrite HlookupPd1. rewrite HbeqFirstFreeNull.
              assumption.
            - split; try(reflexivity). assumption.
            - rewrite <-beqAddrFalse in HbeqBlockNull. assumption.
          }
          unfold isFreeSlot in HblockIsFree. rewrite HlookupBlocks1 in HblockIsFree.
          destruct (lookup (CPaddr (blockToShareInCurrPartAddr + sh1offset)) (memory s1) beqAddr);
              try(congruence). destruct v; try(congruence).
          destruct (lookup (CPaddr (blockToShareInCurrPartAddr + scoffset)) (memory s1) beqAddr);
              try(congruence). destruct v; try(congruence).
          assert(HPFlag: bentryPFlag blockToShareInCurrPartAddr true s0) by intuition.
          unfold bentryPFlag in HPFlag. rewrite HlookupBlocks0 in HPFlag.
          destruct HblockIsFree as (_ & _ & _ & _ & Hpresent & _). congruence.
      }
      assert(HgetFreeListEq2: getFreeSlotsList pd2 s = getFreeSlotsList pd2 s1).
      {
        unfold getFreeSlotsList in *. rewrite HlookupPd2Eq in *.
        destruct (lookup pd2 (memory s1) beqAddr) eqn:HlookupPd2; try(reflexivity). destruct v; try(reflexivity).
        destruct (beqAddr (firstfreeslot p) nullAddr) eqn:HbeqFirstFreeNull; try(reflexivity).
        rewrite Hs. rewrite <-HgetCurrEqs0.
        assert(HnoDups1: NoDupInFreeSlotsList s1) by (unfold consistency1 in *; intuition).
        specialize(HnoDups1 pd2 p HlookupPd2).
        destruct HnoDups1 as [optionListProp (HoptionList & Hwell & HnoDup)].
        unfold getFreeSlotsList in HoptionList. rewrite HlookupPd2 in HoptionList.
        rewrite HbeqFirstFreeNull in HoptionList. subst optionListProp.
        apply getFreeSlotsListRecEqBE; try(assumption).
        - assert(HfirstFreeIsFree: FirstFreeSlotPointerIsBEAndFreeSlot s) by intuition.
          rewrite <-beqAddrFalse in HbeqFirstFreeNull.
          specialize(HfirstFreeIsFree pd2 p HlookupPd2Eq HbeqFirstFreeNull).
          destruct HfirstFreeIsFree as (_ & HfirstFreeIsFree). unfold isFreeSlot in HfirstFreeIsFree.
          intro Hcontra. rewrite Hcontra in *. rewrite HlookupBlocks in HfirstFreeIsFree.
          destruct (lookup (CPaddr (blockToShareInCurrPartAddr + sh1offset)) (memory s) beqAddr);
              try(congruence). destruct v; try(congruence).
          destruct (lookup (CPaddr (blockToShareInCurrPartAddr + scoffset)) (memory s) beqAddr);
              try(congruence). destruct v; try(congruence).
          assert(HPFlag: bentryPFlag blockToShareInCurrPartAddr true s0) by intuition.
          unfold bentryPFlag in HPFlag. rewrite HlookupBlocks0 in HPFlag.
          destruct HfirstFreeIsFree as (_ & _ & _ & _ & Hpresent & _).
          assert(Hbentry7: bentry7 = CBlockEntry (read bentryShare) (write bentryShare) (exec bentryShare)
                                        (present bentryShare) (accessible bentryShare) (blockindex bentryShare)
                                        (CBlock (startAddr (blockrange bentryShare)) cutAddr)) by intuition.
          rewrite Hbentry7 in Hpresent. rewrite HnewB in Hpresent. simpl in Hpresent. congruence.
        - reflexivity.
        - intro Hcontra.
          assert(Hcontra2: In blockToShareInCurrPartAddr (filterOptionPaddr (getFreeSlotsList pd2 s1))).
          {
            unfold getFreeSlotsList. rewrite HlookupPd2. rewrite HbeqFirstFreeNull. assumption.
          }
          assert(HblockIsFree: isFreeSlot blockToShareInCurrPartAddr s1).
          {
            assert(HfreeSlotsList: freeSlotsListIsFreeSlot s1) by (unfold consistency1 in *; intuition).
            specialize(HfreeSlotsList pd2 blockToShareInCurrPartAddr (getFreeSlotsList pd2 s1)
                (filterOptionPaddr (getFreeSlotsList pd2 s1))). apply HfreeSlotsList.
            - unfold isPDT. rewrite HlookupPd2. trivial.
            - split; try(reflexivity). unfold getFreeSlotsList. rewrite HlookupPd2. rewrite HbeqFirstFreeNull.
              assumption.
            - split; try(reflexivity). assumption.
            - rewrite <-beqAddrFalse in HbeqBlockNull. assumption.
          }
          unfold isFreeSlot in HblockIsFree. rewrite HlookupBlocks1 in HblockIsFree.
          destruct (lookup (CPaddr (blockToShareInCurrPartAddr + sh1offset)) (memory s1) beqAddr);
              try(congruence). destruct v; try(congruence).
          destruct (lookup (CPaddr (blockToShareInCurrPartAddr + scoffset)) (memory s1) beqAddr);
              try(congruence). destruct v; try(congruence).
          assert(HPFlag: bentryPFlag blockToShareInCurrPartAddr true s0) by intuition.
          unfold bentryPFlag in HPFlag. rewrite HlookupBlocks0 in HPFlag.
          destruct HblockIsFree as (_ & _ & _ & _ & Hpresent & _). congruence.
      }
      intuition.
      (* END DisjointFreeSlotsLists *)
    }

    assert(inclFreeSlotsBlockEntries s).
    { (* BEGIN inclFreeSlotsBlockEntries s *)
      assert(Hcons0: inclFreeSlotsBlockEntries s1) by (unfold consistency1 in *; intuition).
      intros pd HpdIsPDT.
      assert(HpdLookupEq: lookup pd (memory s) beqAddr = lookup pd (memory s1) beqAddr).
      {
        unfold isPDT in HpdIsPDT. rewrite Hs in HpdIsPDT. simpl in HpdIsPDT. rewrite Hs. simpl.
        destruct (beqAddr blockToShareInCurrPartAddr pd) eqn:HbeqBlockPd; try(exfalso; congruence).
        rewrite <-beqAddrFalse in HbeqBlockPd. rewrite removeDupIdentity; intuition.
      }
      assert(HpdIsPDTs1: isPDT pd s1).
      { unfold isPDT. rewrite <-HpdLookupEq. assumption. }
      specialize(Hcons0 pd HpdIsPDTs1).
      assert(HgetKSEq: getKSEntries pd s = getKSEntries pd s1).
      {
        rewrite Hs. rewrite <-HgetCurrEqs0. apply getKSEntriesEqBE. assumption.
      }
      rewrite HgetKSEq.
      assert(HgetFreeEq: getFreeSlotsList pd s = getFreeSlotsList pd s1).
      {
        unfold getFreeSlotsList in *. rewrite HpdLookupEq.
        destruct (lookup pd (memory s1) beqAddr) eqn:HlookupPd; try(reflexivity). destruct v; try(reflexivity).
        destruct (beqAddr (firstfreeslot p) nullAddr) eqn:HbeqFirstFreeNull; try(reflexivity).
        rewrite Hs. rewrite <-HgetCurrEqs0.
        assert(HnoDups1: NoDupInFreeSlotsList s1) by (unfold consistency1 in *; intuition).
        specialize(HnoDups1 pd p HlookupPd).
        destruct HnoDups1 as [optionListProp (HoptionList & Hwell & HnoDup)].
        unfold getFreeSlotsList in HoptionList. rewrite HlookupPd in HoptionList.
        rewrite HbeqFirstFreeNull in HoptionList. subst optionListProp.
        apply getFreeSlotsListRecEqBE; try(assumption).
        - assert(HfirstFreeIsFree: FirstFreeSlotPointerIsBEAndFreeSlot s) by intuition.
          rewrite <-beqAddrFalse in HbeqFirstFreeNull.
          specialize(HfirstFreeIsFree pd p HpdLookupEq HbeqFirstFreeNull).
          destruct HfirstFreeIsFree as (_ & HfirstFreeIsFree). unfold isFreeSlot in HfirstFreeIsFree.
          intro Hcontra. rewrite Hcontra in *. rewrite HlookupBlocks in HfirstFreeIsFree.
          destruct (lookup (CPaddr (blockToShareInCurrPartAddr + sh1offset)) (memory s) beqAddr);
              try(congruence). destruct v; try(congruence).
          destruct (lookup (CPaddr (blockToShareInCurrPartAddr + scoffset)) (memory s) beqAddr);
              try(congruence). destruct v; try(congruence).
          assert(HPFlag: bentryPFlag blockToShareInCurrPartAddr true s0) by intuition.
          unfold bentryPFlag in HPFlag. rewrite HlookupBlocks0 in HPFlag.
          destruct HfirstFreeIsFree as (_ & _ & _ & _ & Hpresent & _).
          assert(Hbentry7: bentry7 = CBlockEntry (read bentryShare) (write bentryShare) (exec bentryShare)
                                        (present bentryShare) (accessible bentryShare) (blockindex bentryShare)
                                        (CBlock (startAddr (blockrange bentryShare)) cutAddr)) by intuition.
          rewrite Hbentry7 in Hpresent. rewrite HnewB in Hpresent. simpl in Hpresent. congruence.
        - reflexivity.
        - intro Hcontra.
          assert(Hcontra2: In blockToShareInCurrPartAddr (filterOptionPaddr (getFreeSlotsList pd s1))).
          {
            unfold getFreeSlotsList. rewrite HlookupPd. rewrite HbeqFirstFreeNull. assumption.
          }
          assert(HblockIsFree: isFreeSlot blockToShareInCurrPartAddr s1).
          {
            assert(HfreeSlotsList: freeSlotsListIsFreeSlot s1) by (unfold consistency1 in *; intuition).
            specialize(HfreeSlotsList pd blockToShareInCurrPartAddr (getFreeSlotsList pd s1)
                (filterOptionPaddr (getFreeSlotsList pd s1))). apply HfreeSlotsList.
            - unfold isPDT. rewrite HlookupPd. trivial.
            - split; try(reflexivity). unfold getFreeSlotsList. rewrite HlookupPd. rewrite HbeqFirstFreeNull.
              assumption.
            - split; try(reflexivity). assumption.
            - rewrite <-beqAddrFalse in HbeqBlockNull. assumption.
          }
          unfold isFreeSlot in HblockIsFree. rewrite HlookupBlocks1 in HblockIsFree.
          destruct (lookup (CPaddr (blockToShareInCurrPartAddr + sh1offset)) (memory s1) beqAddr);
              try(congruence). destruct v; try(congruence).
          destruct (lookup (CPaddr (blockToShareInCurrPartAddr + scoffset)) (memory s1) beqAddr);
              try(congruence). destruct v; try(congruence).
          assert(HPFlag: bentryPFlag blockToShareInCurrPartAddr true s0) by intuition.
          unfold bentryPFlag in HPFlag. rewrite HlookupBlocks0 in HPFlag.
          destruct HblockIsFree as (_ & _ & _ & _ & Hpresent & _). congruence.
      }
      rewrite HgetFreeEq. assumption.
      (* END inclFreeSlotsBlockEntries *)
    }

    assert(DisjointKSEntries s).
    { (* BEGIN DisjointKSEntries s *)
      assert(Hcons0: DisjointKSEntries s1) by (unfold consistency1 in *; intuition).
      intros pd1 pd2 Hpd1IsPDT Hpd2IsPDT HbeqPd1Pd2.
      assert(HlookupPd1Eq: lookup pd1 (memory s) beqAddr = lookup pd1 (memory s1) beqAddr).
      {
        unfold isPDT in Hpd1IsPDT. rewrite Hs in Hpd1IsPDT. simpl in Hpd1IsPDT. rewrite Hs. simpl.
        destruct (beqAddr blockToShareInCurrPartAddr pd1) eqn:HbeqBlockPd1; try(exfalso; congruence).
        rewrite <-beqAddrFalse in HbeqBlockPd1. rewrite removeDupIdentity; intuition.
      }
      assert(Hpd1IsPDTs1: isPDT pd1 s1).
      { unfold isPDT. rewrite <-HlookupPd1Eq. assumption. }
      assert(HlookupPd2Eq: lookup pd2 (memory s) beqAddr = lookup pd2 (memory s1) beqAddr).
      {
        unfold isPDT in Hpd2IsPDT. rewrite Hs in Hpd2IsPDT. simpl in Hpd2IsPDT. rewrite Hs. simpl.
        destruct (beqAddr blockToShareInCurrPartAddr pd2) eqn:HbeqBlockPd2; try(exfalso; congruence).
        rewrite <-beqAddrFalse in HbeqBlockPd2. rewrite removeDupIdentity; intuition.
      }
      assert(Hpd2IsPDTs1: isPDT pd2 s1).
      { unfold isPDT. rewrite <-HlookupPd2Eq. assumption. }
      specialize(Hcons0 pd1 pd2 Hpd1IsPDTs1 Hpd2IsPDTs1 HbeqPd1Pd2).
      destruct Hcons0 as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. exists list1. exists list2.
      subst list1. subst list2.
      assert(HgetKSEq1: getKSEntries pd1 s = getKSEntries pd1 s1).
      {
        rewrite Hs. rewrite <-HgetCurrEqs0. apply getKSEntriesEqBE. assumption.
      }
      assert(HgetKSEq2: getKSEntries pd2 s = getKSEntries pd2 s1).
      {
        rewrite Hs. rewrite <-HgetCurrEqs0. apply getKSEntriesEqBE. assumption.
      }
      rewrite HgetKSEq1. rewrite HgetKSEq2. intuition.
      (* END DisjointKSEntries *)
    }

    assert(noDupPartitionTree s).
    { (* BEGIN noDupPartitionTree s *)
      assert(Hcons0: noDupPartitionTree s1) by (unfold consistency1 in *; intuition).
      unfold noDupPartitionTree in *. rewrite HgetPartsEq. assumption.
      (* END noDupPartitionTree *)
    }

    assert(isParent s).
    { (* BEGIN isParent s *)
      assert(Hcons0: isParent s1) by (unfold consistency1 in *; intuition).
      intros partition pdparent HparentIsPart HpartIsChild. rewrite HgetPartsEq in HparentIsPart.
      assert(HgetChildrenEq: getChildren pdparent s = getChildren pdparent s1).
      {
        rewrite Hs. rewrite <-HgetCurrEqs0. apply getChildrenEqBEPDflagFalse with bentryShare
            (CPaddr (blockToShareInCurrPartAddr + sh1offset)); try(assumption).
        - apply partitionsArePDT. unfold consistency1 in *; intuition. unfold consistency1 in *; intuition.
          assumption.
        - apply lookupSh1EntryAddr with bentryShare. assumption.
      }
      rewrite HgetChildrenEq in HpartIsChild. specialize(Hcons0 partition pdparent HparentIsPart HpartIsChild).
      unfold pdentryParent in *. rewrite Hs. simpl.
      destruct (beqAddr blockToShareInCurrPartAddr partition) eqn:HbeqBlockPart.
      {
        rewrite <-beqAddrTrue in HbeqBlockPart. subst partition. rewrite HlookupBlocks1 in Hcons0. congruence.
      }
      rewrite <-beqAddrFalse in HbeqBlockPart. rewrite removeDupIdentity; intuition.
      (* END isParent *)
    }

    assert(isChild s).
    { (* BEGIN isChild s *)
      assert(Hcons0: isChild s1) by (unfold consistency1 in *; intuition).
      intros partition pdparent HpartIsPart HparentIsParent. rewrite HgetPartsEq in HpartIsPart.
      assert(HparentIsParents1: pdentryParent partition pdparent s1).
      {
        unfold pdentryParent in *. rewrite Hs in HparentIsParent. simpl in HparentIsParent.
        destruct (beqAddr blockToShareInCurrPartAddr partition) eqn:HbeqBlockPart; try(exfalso; congruence).
        rewrite <-beqAddrFalse in HbeqBlockPart. rewrite removeDupIdentity in HparentIsParent; intuition.
      }
      specialize(Hcons0 partition pdparent HpartIsPart HparentIsParents1).
      assert(HgetChildrenEq: getChildren pdparent s = getChildren pdparent s1).
      {
        rewrite Hs. rewrite <-HgetCurrEqs0. apply getChildrenEqBEPDflagFalse with bentryShare
            (CPaddr (blockToShareInCurrPartAddr + sh1offset)); try(assumption).
        - unfold isPDT. unfold pdentryParent in HparentIsParents1.
          destruct (lookup partition (memory s1) beqAddr) eqn:HlookupParts1; try(exfalso; congruence).
          destruct v; try(exfalso; congruence).
          assert(HparentOfPart: parentOfPartitionIsPartition s1) by (unfold consistency1 in *; intuition).
          specialize(HparentOfPart partition p HlookupParts1).
          destruct HparentOfPart as (HparentIsPart & HparentOfRoot & _).
          destruct (beqAddr partition constantRootPartM) eqn:HbeqPartRoot.
          {
            rewrite <-beqAddrTrue in HbeqPartRoot. specialize(HparentOfRoot HbeqPartRoot).
            rewrite HparentOfRoot in HparentIsParents1. rewrite HparentIsParents1 in Hcons0.
            assert(Hnull: nullAddrExists s1) by (unfold consistency1 in *; intuition).
            unfold getChildren in Hcons0. unfold nullAddrExists in Hnull. unfold isPADDR in Hnull.
            destruct (lookup nullAddr (memory s1) beqAddr); try(exfalso; congruence).
            destruct v; try(exfalso; congruence). simpl in Hcons0. exfalso; congruence.
          }
          rewrite <-beqAddrFalse in HbeqPartRoot. specialize(HparentIsPart HbeqPartRoot).
          destruct HparentIsPart as ([pdentryP HlookupParent] & _).
          rewrite <-HparentIsParents1 in HlookupParent. rewrite HlookupParent. trivial.
        - apply lookupSh1EntryAddr with bentryShare. assumption.
      }
      rewrite HgetChildrenEq. assumption.
      (* END isChild *)
    }

    assert(noDupKSEntriesList s).
    { (* BEGIN noDupKSEntriesList s *)
      assert(Hcons0: noDupKSEntriesList s1) by (unfold consistency1 in *; intuition).
      intros partition HpartIsPDT.
      assert(HpartIsPDTs1: isPDT partition s1).
      {
        unfold isPDT in *. rewrite Hs in HpartIsPDT. simpl in HpartIsPDT.
        destruct (beqAddr blockToShareInCurrPartAddr partition) eqn:HbeqBlockPart; try(exfalso; congruence).
        rewrite <-beqAddrFalse in HbeqBlockPart. rewrite removeDupIdentity in HpartIsPDT; intuition.
      }
      specialize(Hcons0 partition HpartIsPDTs1).
      assert(HgetKSEq: getKSEntries partition s = getKSEntries partition s1).
      {
        rewrite Hs. rewrite <-HgetCurrEqs0. apply getKSEntriesEqBE. assumption.
      }
      rewrite HgetKSEq. assumption.
      (* END noDupKSEntriesList *)
    }

    assert(noDupMappedBlocksList s).
    { (* BEGIN noDupMappedBlocksList s *)
      assert(Hcons0: noDupMappedBlocksList s1) by (unfold consistency1 in *; intuition).
      intros partition HpartIsPDT.
      assert(HpartIsPDTs1: isPDT partition s1).
      {
        unfold isPDT in *. rewrite Hs in HpartIsPDT. simpl in HpartIsPDT.
        destruct (beqAddr blockToShareInCurrPartAddr partition) eqn:HbeqBlockPart; try(exfalso; congruence).
        rewrite <-beqAddrFalse in HbeqBlockPart. rewrite removeDupIdentity in HpartIsPDT; intuition.
      }
      specialize(Hcons0 partition HpartIsPDTs1).
      assert(HgetMappedBlocksEq: getMappedBlocks partition s = getMappedBlocks partition s1).
      {
        rewrite Hs. rewrite <-HgetCurrEqs0. apply getMappedBlocksEqBENoChange with bentryShare.
        assumption. rewrite HnewB. simpl. reflexivity.
      }
      rewrite HgetMappedBlocksEq. assumption.
      (* END noDupMappedBlocksList *)
    }

    assert(wellFormedBlock s).
    { (* BEGIN wellFormedBlock s *)
      assert(Hcons0: wellFormedBlock s1) by (unfold consistency1 in *; intuition).
      intros block startaddr endaddr HPFlag Hstart Hend.
      destruct (beqAddr blockToShareInCurrPartAddr block) eqn:HbeqBlockBlock.
      - rewrite <-beqAddrTrue in HbeqBlockBlock. subst block.
        assert(Hbentry7: bentry7 =
                            CBlockEntry (read bentryShare) (write bentryShare) (exec bentryShare) 
                              (present bentryShare) (accessible bentryShare) (blockindex bentryShare)
                              (CBlock (startAddr (blockrange bentryShare)) cutAddr)) by intuition.
        assert(Hends: endaddr = cutAddr).
        {
          unfold bentryEndAddr in Hend. rewrite HlookupBlocks in Hend.
          rewrite Hbentry7 in Hend. rewrite HnewB in Hend. simpl in Hend. unfold CBlock in Hend.
          assert(Hcut: cutAddr <= maxAddr) by (apply Hp). rewrite <-maxIdxEqualMaxAddr in Hcut.
          destruct (Compare_dec.le_dec (cutAddr - startAddr (blockrange bentryShare)) maxIdx); try(lia).
          simpl in Hend. assumption.
        }
        assert(HPFlags1: bentryPFlag blockToShareInCurrPartAddr true s1).
        {
          unfold bentryPFlag in *. rewrite HlookupBlocks1. rewrite HlookupBlocks in HPFlag.
          rewrite Hbentry7 in HPFlag. rewrite HnewB in HPFlag. simpl in HPFlag. assumption.
        }
        assert(HstartEq: startaddr = blockToCutStartAddr).
        {
          assert(Hstarts0: bentryStartAddr blockToShareInCurrPartAddr blockToCutStartAddr s0) by intuition.
          unfold bentryStartAddr in *. rewrite HlookupBlocks in Hstart. rewrite HlookupBlocks0 in Hstarts0.
          rewrite Hbentry7 in Hstart. rewrite HnewB in Hstart. simpl in Hstart. unfold CBlock in Hstart.
          assert(Hcut: cutAddr <= maxAddr) by (apply Hp). rewrite <-maxIdxEqualMaxAddr in Hcut.
          destruct (Compare_dec.le_dec (cutAddr - startAddr (blockrange bentryShare)) maxIdx); try(lia).
          simpl in Hstart. rewrite <-Hstarts0 in Hstart. assumption.
        }
        subst endaddr. subst startaddr. split.
        + unfold StateLib.Paddr.leb in HlebCutStart. apply eq_sym in HlebCutStart.
          apply Compare_dec.leb_iff_conv in HlebCutStart. assumption.
        + unfold StateLib.Paddr.subPaddr in HsubCutEnd.
          destruct (Compare_dec.le_dec (cutAddr - blockToCutStartAddr) maxIdx); try(exfalso; congruence).
          injection HsubCutEnd as HsubCutEnd. apply orb_false_elim in H5. destruct H5 as (Hsmall1 & Hsmall2).
          subst isBlock1TooSmall. unfold StateLib.Index.ltb in Hblock1. rewrite <-HsubCutEnd in Hblock1.
          simpl in Hblock1. apply eq_sym in Hblock1. apply PeanoNat.Nat.ltb_ge in Hblock1.
          rewrite Hmin in Hblock1. assumption.
      - unfold bentryPFlag in HPFlag. unfold bentryStartAddr in Hstart. unfold bentryEndAddr in Hend.
        rewrite Hs in *. simpl in *. rewrite HbeqBlockBlock in *. rewrite <-beqAddrFalse in HbeqBlockBlock.
        rewrite removeDupIdentity in HPFlag; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in Hstart; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in Hend; try(apply not_eq_sym; assumption).
        specialize(Hcons0 block startaddr endaddr HPFlag Hstart Hend). assumption.
      (* END wellFormedBlock *)
    }

    assert(parentOfPartitionIsPartition s).
    { (* BEGIN parentOfPartitionIsPartition s *)
      assert(Hcons0: parentOfPartitionIsPartition s1) by (unfold consistency1 in *; intuition).
      intros partition pdentryPart HlookupPart.
      assert(HlookupParts1: lookup partition (memory s1) beqAddr = Some (PDT pdentryPart)).
      {
        rewrite Hs in HlookupPart. simpl in HlookupPart.
        destruct (beqAddr blockToShareInCurrPartAddr partition) eqn:HbeqBlockPart; try(exfalso; congruence).
        rewrite <-beqAddrFalse in HbeqBlockPart. rewrite removeDupIdentity in HlookupPart; intuition.
      }
      specialize(Hcons0 partition pdentryPart HlookupParts1).
      destruct Hcons0 as (HparentIsPart & HparentOfRoot & HbeqParentPart).
      split.
      - intro HbeqPartRoot. specialize(HparentIsPart HbeqPartRoot).
        destruct HparentIsPart as ([parentEntry HlookupParent] & HparentIsPart). rewrite HgetPartsEq.
        split; try(assumption). exists parentEntry. rewrite Hs. simpl.
        destruct (beqAddr blockToShareInCurrPartAddr (parent pdentryPart)) eqn:HbeqBlockParent.
        {
          rewrite <-beqAddrTrue in HbeqBlockParent. rewrite <-HbeqBlockParent in *. exfalso; congruence.
        }
        rewrite <-beqAddrFalse in HbeqBlockParent. rewrite removeDupIdentity; intuition.
      - split; assumption.
      (* END parentOfPartitionIsPartition *)
    }

    assert(NbFreeSlotsISNbFreeSlotsInList s).
    { (* BEGIN NbFreeSlotsISNbFreeSlotsInList s *)
      assert(Hcons0: NbFreeSlotsISNbFreeSlotsInList s1) by (unfold consistency1 in *; intuition).
      intros pd nbfreeslots HpdIsPDT HnbFree.
      assert(HlookupEq: lookup pd (memory s) beqAddr = lookup pd (memory s1) beqAddr).
      {
        rewrite Hs. simpl. unfold isPDT in HpdIsPDT. rewrite Hs in HpdIsPDT. simpl in HpdIsPDT.
        destruct (beqAddr blockToShareInCurrPartAddr pd) eqn:HbeqBlockPd; try(exfalso; congruence).
        rewrite <-beqAddrFalse in HbeqBlockPd. rewrite removeDupIdentity; intuition.
      }
      unfold isPDT in HpdIsPDT. unfold pdentryNbFreeSlots in HnbFree. rewrite HlookupEq in *.
      specialize(Hcons0 pd nbfreeslots HpdIsPDT HnbFree).
      destruct Hcons0 as [slotsList (Hlist & HwellFormed & Hnbfreeslots)]. exists slotsList.
      split; try(split; assumption). subst slotsList. apply eq_sym. unfold getFreeSlotsList in *.
      rewrite HlookupEq. destruct (lookup pd (memory s1) beqAddr) eqn:HlookupPds1; try(reflexivity).
      destruct v; try(reflexivity). destruct (beqAddr (firstfreeslot p) nullAddr) eqn:HbeqFirstNull;
            try(reflexivity). rewrite Hs. rewrite <-HgetCurrEqs0. apply getFreeSlotsListRecEqBE; try(assumption).
      - assert(HPFlag: bentryPFlag blockToShareInCurrPartAddr true s0) by intuition.
        assert(HfirstFree: FirstFreeSlotPointerIsBEAndFreeSlot s1) by (unfold consistency1 in *; intuition).
        rewrite <-beqAddrFalse in HbeqFirstNull. specialize(HfirstFree pd p HlookupPds1 HbeqFirstNull).
        destruct HfirstFree as (_ & HfirstFree). intro Hcontra. rewrite Hcontra in *.
        unfold isFreeSlot in HfirstFree. rewrite HlookupBlocks1 in HfirstFree.
        destruct (lookup (CPaddr (blockToShareInCurrPartAddr + sh1offset)) (memory s1) beqAddr); try(congruence).
        destruct v; try(congruence).
        destruct (lookup (CPaddr (blockToShareInCurrPartAddr + scoffset)) (memory s1) beqAddr); try(congruence).
        destruct v; try(congruence). destruct HfirstFree as (_ & _ & _ & _ & Hpresent & _).
        unfold bentryPFlag in HPFlag. rewrite HlookupBlocks0 in HPFlag. congruence.
      - reflexivity.
      - assert(HnoDup: NoDupInFreeSlotsList s1) by (unfold consistency1 in *; intuition).
        specialize(HnoDup pd p HlookupPds1). destruct HnoDup as [slotsList (HslotsList & _ & HnoDup)].
        subst slotsList. unfold getFreeSlotsList in HnoDup. rewrite HlookupPds1 in HnoDup.
        rewrite HbeqFirstNull in HnoDup. assumption.
      - assert(HPFlag: bentryPFlag blockToShareInCurrPartAddr true s0) by intuition. unfold bentryPFlag in HPFlag.
        rewrite HlookupBlocks0 in HPFlag.
        assert(HfreeSlot: freeSlotsListIsFreeSlot s1) by (unfold consistency1 in *; intuition).
        assert(HPDT: isPDT pd s1) by (unfold isPDT; rewrite HlookupPds1; trivial).
        assert(HwellFormedBis: getFreeSlotsList pd s1 = getFreeSlotsList pd s1
                                /\ wellFormedFreeSlotsList (getFreeSlotsList pd s1) <> False).
        {
          split. reflexivity. unfold getFreeSlotsList. rewrite HlookupPds1. rewrite HbeqFirstNull.
          assumption.
        }
        intro Hcontra.
        assert(Heq: filterOptionPaddr (getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s1 (ADT.nbfreeslots p))
                      = filterOptionPaddr (getFreeSlotsList pd s1)
                    /\ In blockToShareInCurrPartAddr
                        (filterOptionPaddr (getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s1
                          (ADT.nbfreeslots p)))).
        {
          unfold getFreeSlotsList. rewrite HlookupPds1. rewrite HbeqFirstNull. split. reflexivity. assumption.
        }
        rewrite <-beqAddrFalse in HbeqBlockNull.
        specialize(HfreeSlot pd blockToShareInCurrPartAddr (getFreeSlotsList pd s1)
            (filterOptionPaddr (getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s1 (ADT.nbfreeslots p))) HPDT
            HwellFormedBis Heq HbeqBlockNull). unfold isFreeSlot in HfreeSlot.
        rewrite HlookupBlocks1 in HfreeSlot.
        destruct (lookup (CPaddr (blockToShareInCurrPartAddr + sh1offset)) (memory s1) beqAddr); try(congruence).
        destruct v; try(congruence).
        destruct (lookup (CPaddr (blockToShareInCurrPartAddr + scoffset)) (memory s1) beqAddr); try(congruence).
        destruct v; try(congruence). destruct HfreeSlot as (_ & _ & _ & _ & Hpresent & _). congruence.
      (* END NbFreeSlotsISNbFreeSlotsInList *)
    }

    assert(maxNbPrepareIsMaxNbKernels s).
    { (* BEGIN maxNbPrepareIsMaxNbKernels s *)
      assert(Hcons0: maxNbPrepareIsMaxNbKernels s1) by (unfold consistency1 in *; intuition).
      intros partition kernList HkernList.
      assert(HkernLists1: isListOfKernels kernList partition s1).
      {
        revert HkernList. rewrite Hs. rewrite <-HgetCurrEqs0. apply isListOfKernelsEqBE.
      }
      specialize(Hcons0 partition kernList HkernLists1). assumption.
      (* END maxNbPrepareIsMaxNbKernels *)
    }

    rewrite <-HgetCurrEqs0 in Hs.

    assert(blockInChildHasAtLeastEquivalentBlockInParent s).
    { (* BEGIN blockInChildHasAtLeastEquivalentBlockInParent s *)
      assert(Hcons0: blockInChildHasAtLeastEquivalentBlockInParent s1) by (unfold consistency1 in *; intuition).
      intros pdparent child block startChild endChild HparentIsPart HchildIsChild HblockMappedChild HstartChild
          HendChild HPFlag. rewrite HgetPartsEq in HparentIsPart.
      assert(HgetChildrenEq: getChildren pdparent s = getChildren pdparent s1).
      {
        rewrite Hs. apply getChildrenEqBEPDflagFalse with bentryShare
          (CPaddr (blockToShareInCurrPartAddr + sh1offset)); try(assumption). apply partitionsArePDT.
        unfold consistency1 in *; intuition. unfold consistency1 in *; intuition. assumption.
        apply lookupSh1EntryAddr with bentryShare. assumption.
      }
      assert(HgetMappedChildEq: getMappedBlocks child s = getMappedBlocks child s1).
      {
        rewrite Hs. apply getMappedBlocksEqBENoChange with bentryShare. assumption. rewrite HnewB. simpl.
        reflexivity.
      }
      assert(HgetMappedParentEq: getMappedBlocks pdparent s = getMappedBlocks pdparent s1).
      {
        rewrite Hs. apply getMappedBlocksEqBENoChange with bentryShare. assumption. rewrite HnewB. simpl.
        reflexivity.
      }
      rewrite HgetChildrenEq in HchildIsChild. rewrite HgetMappedChildEq in HblockMappedChild.
      rewrite HgetMappedParentEq.
      destruct (beqAddr blockToShareInCurrPartAddr block) eqn:HbeqBlockBlock.
      - rewrite <-beqAddrTrue in HbeqBlockBlock. subst block.
        assert(HendChilds1: bentryEndAddr blockToShareInCurrPartAddr blockToCutEndAddr s1).
        {
          assert(Hends0: bentryEndAddr blockToShareInCurrPartAddr blockToCutEndAddr s0) by intuition.
          unfold bentryEndAddr in *. rewrite HlookupBlocks1. rewrite HlookupBlocks0 in Hends0. assumption.
        }
        assert(Hbentry7: bentry7 =
                          CBlockEntry (read bentryShare) (write bentryShare) (exec bentryShare)
                            (present bentryShare) (accessible bentryShare) (blockindex bentryShare)
                            (CBlock (startAddr (blockrange bentryShare)) cutAddr)) by intuition.
        assert(HstartChilds1: bentryStartAddr blockToShareInCurrPartAddr startChild s1).
        {
          unfold bentryStartAddr in *. rewrite HlookupBlocks in HstartChild. rewrite HlookupBlocks1.
          rewrite Hbentry7 in HstartChild. rewrite HnewB in HstartChild. simpl in HstartChild.
          unfold CBlock in HstartChild. assert(Hcut: cutAddr <= maxAddr) by (apply Hp).
          rewrite <-maxIdxEqualMaxAddr in Hcut.
          destruct (Compare_dec.le_dec (cutAddr - startAddr (blockrange bentryShare)) maxIdx); try(lia).
          simpl in HstartChild. assumption.
        }
        assert(HPFlags1: bentryPFlag blockToShareInCurrPartAddr true s1).
        {
          unfold bentryPFlag in *. rewrite Hs in HPFlag. simpl in HPFlag. rewrite HlookupBlocks1.
          rewrite InternalLemmas.beqAddrTrue in HPFlag. rewrite HnewB in HPFlag. simpl in HPFlag. assumption.
        }
        specialize(Hcons0 pdparent child blockToShareInCurrPartAddr startChild blockToCutEndAddr HparentIsPart
          HchildIsChild HblockMappedChild HstartChilds1 HendChilds1 HPFlags1).
        destruct Hcons0 as [blockParent [startParent [endParent (HblockParentMapped & HstartParent & HendParent &
            Hstart & Hend)]]]. exists blockParent. exists startParent. exists endParent. split. assumption.
        destruct (beqAddr blockToShareInCurrPartAddr blockParent) eqn:HbeqBlockBlockParent.
        {
          rewrite <-beqAddrTrue in HbeqBlockBlockParent. subst blockParent.
          assert(HbeqParentChild: pdparent <> child).
          {
            apply childparentNotEq with s1; try(assumption). unfold consistency1 in *; intuition.
          }
          assert(Hdisjoint: DisjointKSEntries s1) by (unfold consistency1 in *; intuition).
          assert(HparentIsPDT: isPDT pdparent s1).
          {
            apply partitionsArePDT. unfold consistency1 in *; intuition.
            unfold consistency1 in *; intuition. assumption.
          }
          assert(HchildIsPDT: isPDT child s1).
          {
            apply childrenArePDT with pdparent. unfold consistency1 in *; intuition. assumption.
          }
          specialize(Hdisjoint pdparent child HparentIsPDT HchildIsPDT HbeqParentChild).
          destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
          unfold getMappedBlocks in *. apply InFilterPresentInList in HblockParentMapped.
          apply InFilterPresentInList in HblockMappedChild.
          specialize(Hdisjoint blockToShareInCurrPartAddr HblockParentMapped). exfalso; congruence.
        }
        split.
        + unfold bentryStartAddr. rewrite Hs. simpl. rewrite HbeqBlockBlockParent.
          rewrite <-beqAddrFalse in HbeqBlockBlockParent. rewrite removeDupIdentity; intuition.
        + split; try(split; try(assumption)).
          * unfold bentryEndAddr. rewrite Hs. simpl. rewrite HbeqBlockBlockParent.
            rewrite <-beqAddrFalse in HbeqBlockBlockParent. rewrite removeDupIdentity; intuition.
          * unfold bentryEndAddr in HendChild. rewrite Hs in HendChild. simpl in HendChild.
            rewrite InternalLemmas.beqAddrTrue in HendChild. rewrite HnewB in HendChild. simpl in HendChild.
            unfold CBlock in HendChild. assert(Hcut: cutAddr <= maxAddr) by (apply Hp).
            rewrite <-maxIdxEqualMaxAddr in Hcut.
            destruct (Compare_dec.le_dec (cutAddr - startAddr (blockrange bentryShare)) maxIdx); try(lia).
            simpl in HendChild. subst endChild. unfold StateLib.Paddr.leb in HlebEndCut.
            apply eq_sym in HlebEndCut. apply Compare_dec.leb_iff_conv in HlebEndCut. lia.
      - assert(HstartChilds1: bentryStartAddr block startChild s1).
        {
          unfold bentryStartAddr in *. rewrite Hs in HstartChild. simpl in HstartChild.
          rewrite HbeqBlockBlock in HstartChild. rewrite <-beqAddrFalse in HbeqBlockBlock.
          rewrite removeDupIdentity in HstartChild; intuition.
        }
        assert(HendChilds1: bentryEndAddr block endChild s1).
        {
          unfold bentryEndAddr in *. rewrite Hs in HendChild. simpl in HendChild.
          rewrite HbeqBlockBlock in HendChild. rewrite <-beqAddrFalse in HbeqBlockBlock.
          rewrite removeDupIdentity in HendChild; intuition.
        }
        assert(HPFlags1: bentryPFlag block true s1).
        {
          unfold bentryPFlag in *. rewrite Hs in HPFlag. simpl in HPFlag.
          rewrite HbeqBlockBlock in HPFlag. rewrite <-beqAddrFalse in HbeqBlockBlock.
          rewrite removeDupIdentity in HPFlag; intuition.
        }
        specialize(Hcons0 pdparent child block startChild endChild HparentIsPart HchildIsChild HblockMappedChild
            HstartChilds1 HendChilds1 HPFlags1).
        destruct Hcons0 as [blockParent [startParent [endParent (HblockParentMapped & HstartParent & HendParent &
            Hstart & Hend)]]]. exists blockParent.
        destruct (beqAddr blockToShareInCurrPartAddr blockParent) eqn:HbeqBlockBlockParent.
        + rewrite <-beqAddrTrue in HbeqBlockBlockParent. subst blockParent. exfalso.
          assert(currentPart = pdparent).
          {
            destruct (beqAddr currentPart pdparent) eqn:HbeqCurrParent;
                try(rewrite <- beqAddrTrue in HbeqCurrParent; assumption). exfalso.
            rewrite <-beqAddrFalse in HbeqCurrParent.
            assert(HpropsBis: exists optionfreeslotslist s2 n0 n1 n2 nbleft,
                     nbleft = CIndex (nbFreeSlots - 1) /\
                     nbleft < maxIdx /\
                     s1 =
                     {|
                       currentPartition := currentPartition s0;
                       memory :=
                         add sceaddr (SCE {| origin := blockOrigin; next := next scentry |}) (memory s2) beqAddr
                     |} /\
                     optionfreeslotslist = getFreeSlotsListRec n1 newFirstFreeSlotAddr s2 nbleft /\
                     getFreeSlotsListRec n2 newFirstFreeSlotAddr s1 nbleft = optionfreeslotslist /\
                     optionfreeslotslist = getFreeSlotsListRec n0 newFirstFreeSlotAddr s0 nbleft /\
                     n0 <= n1 /\
                     nbleft < n0 /\
                     n1 <= n2 /\
                     nbleft < n2 /\
                     n2 <= maxIdx + 1 /\
                     (wellFormedFreeSlotsList optionfreeslotslist = False -> False) /\
                     NoDup (filterOptionPaddr optionfreeslotslist) /\
                     (In (firstfreeslot pdentry) (filterOptionPaddr optionfreeslotslist) -> False) /\
                     (exists optionentrieslist : list optionPaddr,
                        optionentrieslist = getKSEntries currentPart s2 /\
                        getKSEntries currentPart s = optionentrieslist /\
                        optionentrieslist = getKSEntries currentPart s0 /\
                        In (firstfreeslot pdentry) (filterOptionPaddr optionentrieslist)) /\
                     isPDT multiplexer s /\
                     getPartitions multiplexer s2 = getPartitions multiplexer s0 /\
                     getPartitions multiplexer s1 = getPartitions multiplexer s2 /\
                     getChildren currentPart s2 = getChildren currentPart s0 /\
                     getChildren currentPart s1 = getChildren currentPart s2 /\
                     getConfigBlocks currentPart s2 = getConfigBlocks currentPart s0 /\
                     getConfigBlocks currentPart s1 = getConfigBlocks currentPart s2 /\
                     getConfigPaddr currentPart s2 = getConfigPaddr currentPart s0 /\
                     getConfigPaddr currentPart s1 = getConfigPaddr currentPart s2 /\
                     (forall block : paddr,
                      In block (getMappedBlocks currentPart s) <->
                      firstfreeslot pdentry = block \/ In block (getMappedBlocks currentPart s0)) /\
                     ((forall addr : paddr,
                       In addr (getMappedPaddr currentPart s) <-> In addr (getMappedPaddr currentPart s0)) /\
                      length (getMappedPaddr currentPart s) = length (getMappedPaddr currentPart s0)) /\
                     (forall block : paddr,
                      In block (getAccessibleMappedBlocks currentPart s) <->
                      firstfreeslot pdentry = block \/ In block (getAccessibleMappedBlocks currentPart s0)) /\
                     (forall addr : paddr,
                      In addr (getAccessibleMappedPaddr currentPart s) <->
                      In addr
                        (getAllPaddrBlock (startAddr (blockrange bentry6)) (endAddr (blockrange bentry6)) ++
                         getAccessibleMappedPaddr currentPart s0)) /\
                     (forall partition : paddr,
                      (partition = currentPart -> False) ->
                      isPDT partition s0 -> getKSEntries partition s = getKSEntries partition s0) /\
                     (forall partition : paddr,
                      (partition = currentPart -> False) ->
                      isPDT partition s0 -> getMappedPaddr partition s = getMappedPaddr partition s0) /\
                     (forall partition : paddr,
                      (partition = currentPart -> False) ->
                      isPDT partition s0 -> getConfigPaddr partition s = getConfigPaddr partition s0) /\
                     (forall partition : paddr,
                      (partition = currentPart -> False) ->
                      isPDT partition s0 -> getPartitions partition s = getPartitions partition s0) /\
                     (forall partition : paddr,
                      (partition = currentPart -> False) ->
                      isPDT partition s0 -> getChildren partition s = getChildren partition s0) /\
                     (forall partition : paddr,
                      (partition = currentPart -> False) ->
                      isPDT partition s0 -> getMappedBlocks partition s = getMappedBlocks partition s0) /\
                     (forall partition : paddr,
                      (partition = currentPart -> False) ->
                      isPDT partition s0 ->
                      getAccessibleMappedBlocks partition s = getAccessibleMappedBlocks partition s0) /\
                     (forall partition : paddr,
                      (partition = currentPart -> False) ->
                      isPDT partition s0 ->
                      getAccessibleMappedPaddr partition s = getAccessibleMappedPaddr partition s0) /\
                     (forall partition : paddr, isPDT partition s = isPDT partition s0)) by intuition.
            destruct HpropsBis as [optionfreeslotslist [s2 [n0 [n1 [n2 [nbleft HpropsBis]]]]]].
            assert(HgetKSEq: exists optionentrieslist : list optionPaddr,
                               optionentrieslist = getKSEntries currentPart s2 /\
                               getKSEntries currentPart s = optionentrieslist /\
                               optionentrieslist = getKSEntries currentPart s0 /\
                               In (firstfreeslot pdentry) (filterOptionPaddr optionentrieslist)) by intuition.
            clear HpropsBis. destruct HgetKSEq as [kslist (_ & HgetKSs & HgetKSs0 & _)]. subst kslist.
            assert(HblockParentMappedBis: In blockToShareInCurrPartAddr (getMappedBlocks currentPart s0))
                by intuition. rewrite <-HgetMappedParentEq in HblockParentMapped.
            unfold getMappedBlocks in HblockParentMapped. unfold getMappedBlocks in HblockParentMappedBis.
            apply InFilterPresentInList in HblockParentMapped.
            apply InFilterPresentInList in HblockParentMappedBis. rewrite <-HgetKSs0 in *.
            assert(Hdisjoint: DisjointKSEntries s) by assumption.
            assert(HcurrIsPDT: isPDT currentPart s).
            {
              assert(Hlookup: lookup currentPart (memory s) beqAddr = Some (PDT newpdentry)) by intuition.
              unfold isPDT. rewrite Hlookup. trivial.
            }
            assert(HparentIsPDT: isPDT pdparent s).
            {
              apply partitionsArePDT; try(assumption). rewrite HgetPartsEq. assumption.
            }
            specialize(Hdisjoint currentPart pdparent HcurrIsPDT HparentIsPDT HbeqCurrParent).
            destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
            specialize(Hdisjoint blockToShareInCurrPartAddr HblockParentMappedBis). congruence.
          }
          subst pdparent. assert(HPDChildNull: beqAddr nullAddr PDChildAddr = true) by intuition.
          assert(HPDChild: exists sh1entry sh1entryaddr,
                              lookup sh1entryaddr (memory s0) beqAddr = Some (SHE sh1entry)
                              /\ sh1entryPDchild sh1entryaddr PDChildAddr s0
                              /\ sh1entryAddr blockToShareInCurrPartAddr sh1entryaddr s0) by intuition.
          assert(HchildBlockProps: childsBlocksPropsInParent s0)
            by (unfold consistency in *; unfold consistency2 in *; intuition).
          assert(HpropsBis: exists optionfreeslotslist s2 n0 n1 n2 nbleft,
                   nbleft = CIndex (nbFreeSlots - 1) /\
                   nbleft < maxIdx /\
                   s1 =
                   {|
                     currentPartition := currentPartition s0;
                     memory :=
                       add sceaddr (SCE {| origin := blockOrigin; next := next scentry |}) (memory s2) beqAddr
                   |} /\
                   optionfreeslotslist = getFreeSlotsListRec n1 newFirstFreeSlotAddr s2 nbleft /\
                   getFreeSlotsListRec n2 newFirstFreeSlotAddr s1 nbleft = optionfreeslotslist /\
                   optionfreeslotslist = getFreeSlotsListRec n0 newFirstFreeSlotAddr s0 nbleft /\
                   n0 <= n1 /\
                   nbleft < n0 /\
                   n1 <= n2 /\
                   nbleft < n2 /\
                   n2 <= maxIdx + 1 /\
                   (wellFormedFreeSlotsList optionfreeslotslist = False -> False) /\
                   NoDup (filterOptionPaddr optionfreeslotslist) /\
                   (In (firstfreeslot pdentry) (filterOptionPaddr optionfreeslotslist) -> False) /\
                   (exists optionentrieslist : list optionPaddr,
                      optionentrieslist = getKSEntries currentPart s2 /\
                      getKSEntries currentPart s = optionentrieslist /\
                      optionentrieslist = getKSEntries currentPart s0 /\
                      In (firstfreeslot pdentry) (filterOptionPaddr optionentrieslist)) /\
                   isPDT multiplexer s /\
                   getPartitions multiplexer s2 = getPartitions multiplexer s0 /\
                   getPartitions multiplexer s1 = getPartitions multiplexer s2 /\
                   getChildren currentPart s2 = getChildren currentPart s0 /\
                   getChildren currentPart s1 = getChildren currentPart s2 /\
                   getConfigBlocks currentPart s2 = getConfigBlocks currentPart s0 /\
                   getConfigBlocks currentPart s1 = getConfigBlocks currentPart s2 /\
                   getConfigPaddr currentPart s2 = getConfigPaddr currentPart s0 /\
                   getConfigPaddr currentPart s1 = getConfigPaddr currentPart s2 /\
                   (forall block : paddr,
                    In block (getMappedBlocks currentPart s) <->
                    firstfreeslot pdentry = block \/ In block (getMappedBlocks currentPart s0)) /\
                   ((forall addr : paddr,
                     In addr (getMappedPaddr currentPart s) <-> In addr (getMappedPaddr currentPart s0)) /\
                    length (getMappedPaddr currentPart s) = length (getMappedPaddr currentPart s0)) /\
                   (forall block : paddr,
                    In block (getAccessibleMappedBlocks currentPart s) <->
                    firstfreeslot pdentry = block \/ In block (getAccessibleMappedBlocks currentPart s0)) /\
                   (forall addr : paddr,
                    In addr (getAccessibleMappedPaddr currentPart s) <->
                    In addr
                      (getAllPaddrBlock (startAddr (blockrange bentry6)) (endAddr (blockrange bentry6)) ++
                       getAccessibleMappedPaddr currentPart s0)) /\
                   (forall partition : paddr,
                    (partition = currentPart -> False) ->
                    isPDT partition s0 -> getKSEntries partition s = getKSEntries partition s0) /\
                   (forall partition : paddr,
                    (partition = currentPart -> False) ->
                    isPDT partition s0 -> getMappedPaddr partition s = getMappedPaddr partition s0) /\
                   (forall partition : paddr,
                    (partition = currentPart -> False) ->
                    isPDT partition s0 -> getConfigPaddr partition s = getConfigPaddr partition s0) /\
                   (forall partition : paddr,
                    (partition = currentPart -> False) ->
                    isPDT partition s0 -> getPartitions partition s = getPartitions partition s0) /\
                   (forall partition : paddr,
                    (partition = currentPart -> False) ->
                    isPDT partition s0 -> getChildren partition s = getChildren partition s0) /\
                   (forall partition : paddr,
                    (partition = currentPart -> False) ->
                    isPDT partition s0 -> getMappedBlocks partition s = getMappedBlocks partition s0) /\
                   (forall partition : paddr,
                    (partition = currentPart -> False) ->
                    isPDT partition s0 ->
                    getAccessibleMappedBlocks partition s = getAccessibleMappedBlocks partition s0) /\
                   (forall partition : paddr,
                    (partition = currentPart -> False) ->
                    isPDT partition s0 ->
                    getAccessibleMappedPaddr partition s = getAccessibleMappedPaddr partition s0) /\
                   (forall partition : paddr, isPDT partition s = isPDT partition s0)) by intuition.
          destruct HpropsBis as [optionfreeslotslist [s2 [n0 [n1 [n2 [nbleft (Hnbleft & Hlnbleft & Hs1Bis & _ &
              Hlists1 & Hlists0 & Hlebn0n1 & Hltnbleftn0 & Hlebn1n2 & Hltnbleftn2 & Hlebn2 & HwellFormed & HnoDup
              & HfirstFreeChanged & HgetKSEq & _ & HgetPartsEqs2s0 & HgetPartsEqs1s2 & HpropsBis)]]]]]].
          rewrite HgetPartsEqs2s0 in HgetPartsEqs1s2. rewrite HgetPartsEqs1s2 in HparentIsPart.
          assert(HgetChildrenEqs0: getChildren currentPart s = getChildren currentPart s0).
          {
            rewrite HgetChildrenEq.
            assert(Heq1: getChildren currentPart s1 = getChildren currentPart s2) by intuition.
            assert(Heq2: getChildren currentPart s2 = getChildren currentPart s0) by intuition.
            rewrite Heq1. rewrite Heq2. reflexivity.
          }
          rewrite <-HgetChildrenEq in HchildIsChild. rewrite HgetChildrenEqs0 in HchildIsChild.
          assert(HgetMappedChilds0: (firstfreeslot pdentry = block /\ child = currentPart)
                                    \/ In block (getMappedBlocks child s0)).
          {
            destruct (beqAddr child currentPart) eqn:HbeqChildCurr.
            - rewrite <-beqAddrTrue in HbeqChildCurr. subst child.
              assert(Hres: forall block,
                       In block (getMappedBlocks currentPart s) <->
                       firstfreeslot pdentry = block \/ In block (getMappedBlocks currentPart s0)) by intuition.
              rewrite HgetMappedChildEq in Hres. specialize(Hres block). destruct Hres as (Hres & _).
              specialize(Hres HblockMappedChild). intuition.
            - rewrite <-beqAddrFalse in HbeqChildCurr.
              assert(Hres: forall partition, partition <> currentPart -> isPDT partition s0
                              -> getMappedBlocks partition s = getMappedBlocks partition s0) by intuition.
              rewrite <-HgetMappedChildEq in HblockMappedChild.
              rewrite Hres in HblockMappedChild; try(assumption); try(apply childrenArePDT with currentPart;
                  unfold consistency in *; unfold consistency1 in *; intuition). right. assumption.
          }
          assert(HchildNotCurr: child <> currentPart).
          {
            destruct (beqAddr child currentPart) eqn:HbeqChildCurr; try(rewrite beqAddrFalse; assumption).
            exfalso. rewrite <-beqAddrTrue in HbeqChildCurr. subst child.
            rewrite <-HgetChildrenEqs0 in HchildIsChild. rewrite HgetChildrenEq in HchildIsChild.
            assert(HparentCycle: pdentryParent currentPart currentPart s1).
            {
              assert(Hparent: isParent s1) by (unfold consistency1 in *; intuition).
              rewrite <-HgetPartsEqs1s2 in HparentIsPart.
              specialize(Hparent currentPart currentPart HparentIsPart HchildIsChild). assumption.
            }
            assert(HparentOfPart: parentOfPartitionIsPartition s1) by (unfold consistency1 in *; intuition).
            unfold pdentryParent in HparentCycle.
            destruct (lookup currentPart (memory s1) beqAddr) eqn:HlookupCurrs1; try(congruence).
            destruct v; try(congruence). specialize(HparentOfPart currentPart p HlookupCurrs1).
            destruct HparentOfPart as (_ & _ & Hcontra). rewrite <-HparentCycle in Hcontra. congruence.
          }
          destruct HgetMappedChilds0 as [(_ & Hcontra) | HblockMappedChilds0]; try(congruence).
          assert(HblockParentMappeds0: firstfreeslot pdentry = blockToShareInCurrPartAddr
                                    \/ In blockToShareInCurrPartAddr (getMappedBlocks currentPart s0)).
          {
            assert(Hres: forall block,
                     In block (getMappedBlocks currentPart s) <->
                     firstfreeslot pdentry = block \/ In block (getMappedBlocks currentPart s0)) by intuition.
            rewrite HgetMappedParentEq in Hres. specialize(Hres blockToShareInCurrPartAddr).
            destruct Hres as (Hres & _). apply Hres. assumption.
          }
          destruct (beqAddr (firstfreeslot pdentry) blockToShareInCurrPartAddr) eqn:HbeqFreeBlock.
          {
            rewrite <-beqAddrTrue in HbeqFreeBlock. rewrite <-HbeqFreeBlock in *.
            assert(HfirstFree: FirstFreeSlotPointerIsBEAndFreeSlot s0)
                by (unfold consistency in *; unfold consistency1 in *; intuition).
            assert(HlookupCurrs0: lookup currentPart (memory s0) beqAddr = Some (PDT pdentry)) by intuition.
            rewrite <-beqAddrFalse in HbeqBlockNull.
            specialize(HfirstFree currentPart pdentry HlookupCurrs0 HbeqBlockNull).
            destruct HfirstFree as (_ & HfirstFree). unfold isFreeSlot in HfirstFree.
            assert(HPFlagBlockParent: bentryPFlag (firstfreeslot pdentry) true s0) by intuition.
            unfold bentryPFlag in HPFlagBlockParent. rewrite HlookupBlocks0 in *.
            destruct (lookup (CPaddr (firstfreeslot pdentry + sh1offset)) (memory s0) beqAddr); try(congruence).
            destruct v; try(congruence).
            destruct (lookup (CPaddr (firstfreeslot pdentry + scoffset)) (memory s0) beqAddr); try(congruence).
            destruct v; try(congruence). destruct HfirstFree as (_ & _ & _ & _ & Hpresent & _). congruence.
          }
          rewrite <-beqAddrFalse in HbeqFreeBlock.
          destruct HblockParentMappeds0 as [Hcontra | HblockParentMappeds0]; try(congruence).
          assert(HbeqNewBlockParent: beqAddr idNewSubblock blockToShareInCurrPartAddr = false) by intuition.
          assert(HstartParents0: bentryStartAddr blockToShareInCurrPartAddr startParent s0).
          {
            unfold bentryStartAddr in HstartParent. rewrite Hs1 in HstartParent. simpl in HstartParent.
            rewrite HbeqSceBlock in HstartParent. rewrite HbeqSubblockSce in HstartParent. simpl in HstartParent.
            rewrite HbeqNewBlockParent in HstartParent. rewrite InternalLemmas.beqAddrTrue in HstartParent.
            rewrite HbeqCurrSubblock in HstartParent. rewrite <-beqAddrFalse in *.
            rewrite removeDupIdentity in HstartParent; try(apply not_eq_sym; assumption).
            rewrite removeDupIdentity in HstartParent; try(apply not_eq_sym; assumption).
            rewrite removeDupIdentity in HstartParent; try(apply not_eq_sym; assumption).
            rewrite removeDupIdentity in HstartParent; try(apply not_eq_sym; assumption).
            rewrite removeDupIdentity in HstartParent; try(apply not_eq_sym; assumption).
            rewrite removeDupIdentity in HstartParent; try(apply not_eq_sym; assumption).
            rewrite removeDupIdentity in HstartParent; try(apply not_eq_sym; assumption). simpl in HstartParent.
            rewrite beqAddrFalse in HbeqCurrBlock. rewrite HbeqCurrBlock in HstartParent.
            rewrite InternalLemmas.beqAddrTrue in HstartParent. rewrite <-beqAddrFalse in *.
            rewrite removeDupIdentity in HstartParent; try(apply not_eq_sym; assumption).
            rewrite removeDupIdentity in HstartParent; try(apply not_eq_sym; assumption).
            rewrite removeDupIdentity in HstartParent; try(apply not_eq_sym; assumption). assumption.
          }
          assert(HendParents0: bentryEndAddr blockToShareInCurrPartAddr endParent s0).
          {
            unfold bentryEndAddr in HendParent. rewrite Hs1 in HendParent. simpl in HendParent.
            rewrite HbeqSceBlock in HendParent. rewrite HbeqSubblockSce in HendParent. simpl in HendParent.
            rewrite HbeqNewBlockParent in HendParent. rewrite InternalLemmas.beqAddrTrue in HendParent.
            rewrite HbeqCurrSubblock in HendParent. rewrite <-beqAddrFalse in *.
            rewrite removeDupIdentity in HendParent; try(apply not_eq_sym; assumption).
            rewrite removeDupIdentity in HendParent; try(apply not_eq_sym; assumption).
            rewrite removeDupIdentity in HendParent; try(apply not_eq_sym; assumption).
            rewrite removeDupIdentity in HendParent; try(apply not_eq_sym; assumption).
            rewrite removeDupIdentity in HendParent; try(apply not_eq_sym; assumption).
            rewrite removeDupIdentity in HendParent; try(apply not_eq_sym; assumption).
            rewrite removeDupIdentity in HendParent; try(apply not_eq_sym; assumption). simpl in HendParent.
            rewrite beqAddrFalse in HbeqCurrBlock. rewrite HbeqCurrBlock in HendParent.
            rewrite InternalLemmas.beqAddrTrue in HendParent. rewrite <-beqAddrFalse in *.
            rewrite removeDupIdentity in HendParent; try(apply not_eq_sym; assumption).
            rewrite removeDupIdentity in HendParent; try(apply not_eq_sym; assumption).
            rewrite removeDupIdentity in HendParent; try(apply not_eq_sym; assumption). assumption.
          }
          destruct (beqAddr idNewSubblock block) eqn:HbeqNewBlock.
          {
            assert(HnewIsFirstFree: pdentryFirstFreeSlot currentPart idNewSubblock s0) by intuition.
            rewrite <-beqAddrTrue in HbeqNewBlock. subst block. unfold pdentryFirstFreeSlot in HnewIsFirstFree.
            assert(HlookupCurrs0: lookup currentPart (memory s0) beqAddr = Some (PDT pdentry)) by intuition.
            rewrite HlookupCurrs0 in HnewIsFirstFree. subst idNewSubblock.
            destruct HgetKSEq as [kslist (_ & _ & Hkslist & HfirstFreeIsKS)]. subst kslist.
            unfold getMappedBlocks in HblockMappedChilds0. apply InFilterPresentInList in HblockMappedChilds0.
            assert(Hdisjoint: DisjointKSEntries s0)
                by (unfold consistency in *; unfold consistency1 in *; intuition).
            assert(HchildIsPDT: isPDT child s0).
            {
              apply childrenArePDT with currentPart; try(assumption).
              unfold consistency in *; unfold consistency1 in *; intuition.
            }
            assert(HcurrIsPDT: isPDT currentPart s0).
            {
              unfold isPDT. rewrite HlookupCurrs0. trivial.
            }
            specialize(Hdisjoint child currentPart HchildIsPDT HcurrIsPDT HchildNotCurr).
            destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
            specialize(Hdisjoint (firstfreeslot pdentry) HblockMappedChilds0). congruence.
          }
          assert(HstartChilds0: bentryStartAddr block startChild s0).
          {
            unfold bentryStartAddr in HstartChilds1. rewrite Hs1 in HstartChilds1. simpl in HstartChilds1.
            destruct (beqAddr sceaddr block) eqn:HbeqSceBlockChild; try(exfalso; congruence).
            rewrite HbeqSubblockSce in HstartChilds1. simpl in HstartChilds1.
            rewrite HbeqNewBlock in HstartChilds1. rewrite InternalLemmas.beqAddrTrue in HstartChilds1.
            rewrite HbeqCurrSubblock in HstartChilds1. rewrite <-beqAddrFalse in *.
            rewrite removeDupIdentity in HstartChilds1; try(apply not_eq_sym; assumption).
            rewrite removeDupIdentity in HstartChilds1; try(apply not_eq_sym; assumption).
            rewrite removeDupIdentity in HstartChilds1; try(apply not_eq_sym; assumption).
            rewrite removeDupIdentity in HstartChilds1; try(apply not_eq_sym; assumption).
            rewrite removeDupIdentity in HstartChilds1; try(apply not_eq_sym; assumption).
            rewrite removeDupIdentity in HstartChilds1; try(apply not_eq_sym; assumption).
            rewrite removeDupIdentity in HstartChilds1; try(apply not_eq_sym; assumption). simpl in HstartChilds1.
            destruct (beqAddr currentPart block) eqn:HbeqCurrBlockChild; try(exfalso; congruence).
            rewrite InternalLemmas.beqAddrTrue in HstartChilds1. rewrite <-beqAddrFalse in HbeqCurrBlockChild.
            rewrite removeDupIdentity in HstartChilds1; try(apply not_eq_sym; assumption).
            rewrite removeDupIdentity in HstartChilds1; try(apply not_eq_sym; assumption).
            rewrite removeDupIdentity in HstartChilds1; try(apply not_eq_sym; assumption). assumption.
          }
          assert(HendChilds0: bentryEndAddr block endChild s0).
          {
            unfold bentryEndAddr in HendChilds1. rewrite Hs1 in HendChilds1. simpl in HendChilds1.
            destruct (beqAddr sceaddr block) eqn:HbeqSceBlockChild; try(exfalso; congruence).
            rewrite HbeqSubblockSce in HendChilds1. simpl in HendChilds1.
            rewrite HbeqNewBlock in HendChilds1. rewrite InternalLemmas.beqAddrTrue in HendChilds1.
            rewrite HbeqCurrSubblock in HendChilds1. rewrite <-beqAddrFalse in *.
            rewrite removeDupIdentity in HendChilds1; try(apply not_eq_sym; assumption).
            rewrite removeDupIdentity in HendChilds1; try(apply not_eq_sym; assumption).
            rewrite removeDupIdentity in HendChilds1; try(apply not_eq_sym; assumption).
            rewrite removeDupIdentity in HendChilds1; try(apply not_eq_sym; assumption).
            rewrite removeDupIdentity in HendChilds1; try(apply not_eq_sym; assumption).
            rewrite removeDupIdentity in HendChilds1; try(apply not_eq_sym; assumption).
            rewrite removeDupIdentity in HendChilds1; try(apply not_eq_sym; assumption). simpl in HendChilds1.
            destruct (beqAddr currentPart block) eqn:HbeqCurrBlockChild; try(exfalso; congruence).
            rewrite InternalLemmas.beqAddrTrue in HendChilds1. rewrite <-beqAddrFalse in HbeqCurrBlockChild.
            rewrite removeDupIdentity in HendChilds1; try(apply not_eq_sym; assumption).
            rewrite removeDupIdentity in HendChilds1; try(apply not_eq_sym; assumption).
            rewrite removeDupIdentity in HendChilds1; try(apply not_eq_sym; assumption). assumption.
          }
          assert(HPFlags0: bentryPFlag block true s0).
          {
            unfold bentryPFlag in HPFlags1. rewrite Hs1 in HPFlags1. simpl in HPFlags1.
            destruct (beqAddr sceaddr block) eqn:HbeqSceBlockChild; try(exfalso; congruence).
            rewrite HbeqSubblockSce in HPFlags1. simpl in HPFlags1.
            rewrite HbeqNewBlock in HPFlags1. rewrite InternalLemmas.beqAddrTrue in HPFlags1.
            rewrite HbeqCurrSubblock in HPFlags1. rewrite <-beqAddrFalse in *.
            rewrite removeDupIdentity in HPFlags1; try(apply not_eq_sym; assumption).
            rewrite removeDupIdentity in HPFlags1; try(apply not_eq_sym; assumption).
            rewrite removeDupIdentity in HPFlags1; try(apply not_eq_sym; assumption).
            rewrite removeDupIdentity in HPFlags1; try(apply not_eq_sym; assumption).
            rewrite removeDupIdentity in HPFlags1; try(apply not_eq_sym; assumption).
            rewrite removeDupIdentity in HPFlags1; try(apply not_eq_sym; assumption).
            rewrite removeDupIdentity in HPFlags1; try(apply not_eq_sym; assumption). simpl in HPFlags1.
            destruct (beqAddr currentPart block) eqn:HbeqCurrBlockChild; try(exfalso; congruence).
            rewrite InternalLemmas.beqAddrTrue in HPFlags1. rewrite <-beqAddrFalse in HbeqCurrBlockChild.
            rewrite removeDupIdentity in HPFlags1; try(apply not_eq_sym; assumption).
            rewrite removeDupIdentity in HPFlags1; try(apply not_eq_sym; assumption).
            rewrite removeDupIdentity in HPFlags1; try(apply not_eq_sym; assumption). assumption.
          }
          assert(HPFlagBlocks0: bentryPFlag blockToShareInCurrPartAddr true s0) by intuition.
          specialize(HchildBlockProps child currentPart block startChild endChild blockToShareInCurrPartAddr
              startParent endParent HparentIsPart HchildIsChild HblockMappedChilds0 HstartChilds0 HendChilds0
              HPFlags0 HblockParentMappeds0 HstartParents0 HendParents0 HPFlagBlocks0 Hstart Hend).
          destruct HchildBlockProps as (_ & HPDChildEquiv & _).
          destruct HPDChild as [sh1entry [sh1entryaddr (HlookupSh1 & HPDChild & Hsh1)]].
          unfold sh1entryAddr in Hsh1. rewrite HlookupBlocks0 in Hsh1. rewrite <-Hsh1 in *.
          specialize(HPDChildEquiv PDChildAddr HPDChild). rewrite <-beqAddrTrue in HPDChildNull.
          congruence.
        + exists startParent. exists endParent. split. assumption.
          assert(HlookupBlockParentEq: lookup blockParent (memory s) beqAddr
                                        = lookup blockParent (memory s1) beqAddr).
          {
            rewrite Hs. simpl. rewrite HbeqBlockBlockParent. rewrite <-beqAddrFalse in HbeqBlockBlockParent.
            rewrite removeDupIdentity; intuition.
          }
          split. unfold bentryStartAddr. rewrite HlookupBlockParentEq. assumption.
          split. unfold bentryEndAddr. rewrite HlookupBlockParentEq. assumption. split; assumption.
      (* END blockInChildHasAtLeastEquivalentBlockInParent *)
    }

    assert(partitionTreeIsTree s).
    { (* BEGIN partitionTreeIsTree s *)
      assert(Hcons0: partitionTreeIsTree s1) by (unfold consistency1 in *; intuition).
      intros child pdparent parentsList HchildNotRoot HchildIsPart HchildIsChild HparentsList.
      rewrite HgetPartsEq in HchildIsPart.
      assert(HchildIsChilds1: pdentryParent child pdparent s1).
      {
        unfold pdentryParent in HchildIsChild. rewrite Hs in HchildIsChild. simpl in HchildIsChild.
        destruct (beqAddr blockToShareInCurrPartAddr child) eqn:HbeqBlockChild; try(exfalso; congruence).
        rewrite <-beqAddrFalse in HbeqBlockChild. rewrite removeDupIdentity in HchildIsChild; intuition.
      }
      assert(HparentsLists1: isParentsList s1 parentsList pdparent).
      {
        rewrite Hs in HparentsList. revert HparentsList. apply isParentsListEqBERev with bentryShare.
        - unfold pdentryParent in HchildIsChilds1.
          destruct (lookup child (memory s1) beqAddr) eqn:HlookupChilds1; try(exfalso; congruence).
          destruct v; try(exfalso; congruence). assert(HparentOfPart: parentOfPartitionIsPartition s1)
              by (unfold consistency1 in *; intuition). specialize(HparentOfPart child p HlookupChilds1).
          destruct HparentOfPart as (HparentIsPart & _). specialize(HparentIsPart HchildNotRoot).
          destruct HparentIsPart. rewrite HchildIsChilds1. assumption.
        - assumption.
        - unfold consistency1 in *; intuition.
      }
      unfold partitionTreeIsTree in Hcons0. apply Hcons0 with pdparent; assumption.
      (* END partitionTreeIsTree *)
    }

    assert(kernelEntriesAreValid s).
    { (* BEGIN kernelEntriesAreValid s *)
      assert(Hcons0: kernelEntriesAreValid s1) by (unfold consistency1 in *; intuition).
      intros kernel idx HkernIsKS HidxBounded.
      assert(HkernIsKSs1: isKS kernel s1).
      {
        unfold isKS in HkernIsKS. rewrite Hs in HkernIsKS. simpl in HkernIsKS.
        destruct (beqAddr blockToShareInCurrPartAddr kernel) eqn:HbeqBlockKern.
        - rewrite <-beqAddrTrue in HbeqBlockKern. subst kernel. rewrite HnewB in HkernIsKS. simpl in HkernIsKS.
          unfold isKS. rewrite HlookupBlocks1. assumption.
        - rewrite <-beqAddrFalse in HbeqBlockKern. rewrite removeDupIdentity in HkernIsKS; intuition.
      }
      specialize(Hcons0 kernel idx HkernIsKSs1 HidxBounded). unfold isBE in *. rewrite Hs. simpl.
      destruct (beqAddr blockToShareInCurrPartAddr (CPaddr (kernel + idx))) eqn:HbeqBlockKernIdx; try(trivial).
      rewrite <-beqAddrFalse in HbeqBlockKernIdx. rewrite removeDupIdentity; intuition.
      (* END kernelEntriesAreValid *)
    }

    assert(nextKernelIsValid s).
    { (* BEGIN nextKernelIsValid s *)
      assert(Hcons0: nextKernelIsValid s1) by (unfold consistency1 in *; intuition).
      intros kernel HkernIsKS.
      assert(HkernIsKSs1: isKS kernel s1).
      {
        unfold isKS in HkernIsKS. rewrite Hs in HkernIsKS. simpl in HkernIsKS.
        destruct (beqAddr blockToShareInCurrPartAddr kernel) eqn:HbeqBlockKern.
        - rewrite <-beqAddrTrue in HbeqBlockKern. subst kernel. rewrite HnewB in HkernIsKS. simpl in HkernIsKS.
          unfold isKS. rewrite HlookupBlocks1. assumption.
        - rewrite <-beqAddrFalse in HbeqBlockKern. rewrite removeDupIdentity in HkernIsKS; intuition.
      }
      specialize(Hcons0 kernel HkernIsKSs1).
      destruct Hcons0 as (HkernNext & [nextAddr (HlookupNext & HnextAddr)]). split. assumption. exists nextAddr.
      split.
      - intro Hp. specialize(HlookupNext Hp). rewrite Hs. simpl.
        destruct (beqAddr blockToShareInCurrPartAddr {| p := kernel + nextoffset; Hp := Hp |}) eqn:HbeqBlockNext.
        {
          rewrite <-beqAddrTrue in HbeqBlockNext. rewrite <-HbeqBlockNext in HlookupNext. exfalso; congruence.
        }
        rewrite <-beqAddrFalse in HbeqBlockNext. rewrite removeDupIdentity; intuition.
      - destruct HnextAddr as [HnextAddr | Hnull]; try(right; assumption). left. unfold isKS in *. rewrite Hs.
        simpl. destruct (beqAddr blockToShareInCurrPartAddr nextAddr) eqn:HbeqBlockNext.
        + rewrite <-beqAddrTrue in HbeqBlockNext. subst nextAddr. rewrite HnewB. simpl.
          rewrite HlookupBlocks1 in HnextAddr. assumption.
        + rewrite <-beqAddrFalse in HbeqBlockNext. rewrite removeDupIdentity; intuition.
      (* END nextKernelIsValid *)
    }

    assert(noDupListOfKerns s).
    { (* BEGIN noDupListOfKerns s *)
      assert(Hcons0: noDupListOfKerns s1) by (unfold consistency1 in *; intuition).
      intros partition kernList HkernList.
      assert(HkernLists1: isListOfKernels kernList partition s1).
      {
        revert HkernList. rewrite Hs. apply isListOfKernelsEqBE.
      }
      specialize(Hcons0 partition kernList HkernLists1). assumption.
      (* END noDupListOfKerns *)
    }

    assert(MPUsizeIsBelowMax s).
    { (* BEGIN MPUsizeIsBelowMax s *)
      assert(Hcons0: MPUsizeIsBelowMax s1) by (unfold consistency1 in *; intuition).
      intros partition MPUlist HMPU.
      assert(HMPUs1: pdentryMPU partition MPUlist s1).
      {
        unfold pdentryMPU in HMPU. rewrite Hs in HMPU. simpl in HMPU.
        destruct (beqAddr blockToShareInCurrPartAddr partition) eqn:HbeqBlockPart; try(exfalso; congruence).
        rewrite <-beqAddrFalse in HbeqBlockPart. rewrite removeDupIdentity in HMPU; intuition.
      }
      specialize(Hcons0 partition MPUlist HMPUs1). assumption.
      (* END MPUsizeIsBelowMax *)
    }

    assert(originIsParentBlocksStart s).
    { (* BEGIN originIsParentBlocksStart s *)
      assert(Hcons0: originIsParentBlocksStart s1) by (unfold consistency1 in *; intuition).
      intros part pdentryPart block scentryaddr scorigin HpartIsPart HlookupPart HblockMapped Hsce Horigin.
      rewrite HgetPartsEq in HpartIsPart.
      assert(HlookupParts1: lookup part (memory s1) beqAddr = Some (PDT pdentryPart)).
      {
        rewrite Hs in HlookupPart. simpl in HlookupPart.
        destruct (beqAddr blockToShareInCurrPartAddr part) eqn:HbeqBlockPart; try(exfalso; congruence).
        rewrite <-beqAddrFalse in HbeqBlockPart.
        rewrite removeDupIdentity in HlookupPart; try(apply not_eq_sym; assumption). assumption.
      }
      assert(HgetMappedBlocksPartEq: getMappedBlocks part s = getMappedBlocks part s1).
      {
        rewrite Hs. apply getMappedBlocksEqBENoChange with bentryShare; try(assumption).
        rewrite HnewB. simpl. reflexivity.
      }
      rewrite HgetMappedBlocksPartEq in HblockMapped.
      assert(Horigins1: scentryOrigin scentryaddr scorigin s1).
      {
        unfold scentryOrigin in Horigin. rewrite Hs in Horigin. simpl in Horigin.
        destruct (beqAddr blockToShareInCurrPartAddr scentryaddr) eqn:HbeqBlockSce; try(exfalso; congruence).
        rewrite <-beqAddrFalse in HbeqBlockSce.
        rewrite removeDupIdentity in Horigin; try(apply not_eq_sym; assumption). assumption.
      }
      specialize(Hcons0 part pdentryPart block scentryaddr scorigin HpartIsPart HlookupParts1 HblockMapped Hsce
          Horigins1). destruct Hcons0 as (Hcons0 & HstartAbove). split.
      - intro HbeqPartRoot. specialize(Hcons0 HbeqPartRoot).
        destruct Hcons0 as [blockParent (HblockParentMapped & HstartParent & Hincl)].
        exists blockParent.
        assert(HgetMappedBlocksParentEq: getMappedBlocks (parent pdentryPart) s
                                          = getMappedBlocks (parent pdentryPart) s1).
        {
          rewrite Hs. apply getMappedBlocksEqBENoChange with bentryShare; try(assumption).
          rewrite HnewB. simpl. reflexivity.
        }
        rewrite HgetMappedBlocksParentEq. split. assumption.
        destruct (beqAddr blockToShareInCurrPartAddr blockParent) eqn:HbeqBlockBlockParent.
        {
          rewrite <-DTL.beqAddrTrue in HbeqBlockBlockParent. subst blockParent. exfalso.
          assert(HblockParentMappedCurr: In blockToShareInCurrPartAddr (getMappedBlocks currentPart s)).
          {
            intuition. destruct H114 as [optionfreeslotslist [s2 [n0 [n1 [n2 [nbleft Hprops]]]]]].
            assert(HgetBlocksCurrEq: (forall block, In block (getMappedBlocks currentPart s) <->
                firstfreeslot pdentry = block \/ In block (getMappedBlocks currentPart s0))) by intuition.
            apply HgetBlocksCurrEq. right. assumption.
          }
          rewrite <-HgetMappedBlocksParentEq in HblockParentMapped.
          assert(HbeqParentCurr: parent pdentryPart = currentPart).
          {
            destruct (beqAddr (parent pdentryPart) currentPart) eqn:HbeqParentCurr;
                try(rewrite beqAddrTrue; assumption).
            rewrite <-beqAddrFalse in HbeqParentCurr. exfalso. unfold getMappedBlocks in HblockParentMapped.
            unfold getMappedBlocks in HblockParentMappedCurr. apply InFilterPresentInList in HblockParentMapped.
            apply InFilterPresentInList in HblockParentMappedCurr.
            assert(Hdisjoint: DisjointKSEntries s) by assumption.
            assert(HcurrIsPDT: isPDT currentPart s).
            {
              assert(Hlookup: lookup currentPart (memory s) beqAddr = Some (PDT newpdentry)) by intuition.
              unfold isPDT. rewrite Hlookup. trivial.
            }
            assert(HparentIsPDT: isPDT (parent pdentryPart) s).
            {
              unfold isPDT. unfold getKSEntries in HblockParentMapped.
              destruct (lookup (parent pdentryPart) (memory s) beqAddr);
                  try(simpl in HblockParentMapped; congruence).
              destruct v; try(simpl in HblockParentMapped; congruence). trivial.
            }
            specialize(Hdisjoint (parent pdentryPart) currentPart HparentIsPDT HcurrIsPDT HbeqParentCurr).
            destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
            specialize(Hdisjoint blockToShareInCurrPartAddr HblockParentMapped). congruence.
          }
          rewrite HbeqParentCurr in *.
          assert(HPDChild: exists sh1entry sh1entryaddr,
                                 lookup sh1entryaddr (memory s0) beqAddr = Some (SHE sh1entry) /\
                                 sh1entryPDchild sh1entryaddr PDChildAddr s0 /\
                                 sh1entryAddr blockToShareInCurrPartAddr sh1entryaddr s0) by intuition.
          assert(HbeqNullChild: beqAddr nullAddr PDChildAddr = true) by intuition.
          rewrite <-DTL.beqAddrTrue in HbeqNullChild. subst PDChildAddr.
          destruct HPDChild as [sh1entry [sh1entryaddr (HlookupSh1 & HPDChild & Hsh1)]].
          assert(HnoChild: noChildImpliesAddressesNotShared s0)
              by (unfold consistency in *; unfold consistency2 in *; intuition).
          assert(HgetPartsEqs1: getPartitions multiplexer s1 = getPartitions multiplexer s0).
          {
            intuition. destruct H114 as [optionfreeslotslist [s2 [n0 [n1 [n2 [nbleft Hprops]]]]]].
            assert(Hs2s0: getPartitions multiplexer s2 = getPartitions multiplexer s0) by intuition.
            assert(Hs1s2: getPartitions multiplexer s1 = getPartitions multiplexer s2) by intuition.
            rewrite <-Hs2s0. assumption.
          }
          assert(HparentOfPart: parentOfPartitionIsPartition s1)
              by (unfold consistency in *; unfold consistency1 in *; intuition).
          specialize(HparentOfPart part pdentryPart HlookupParts1).
          destruct HparentOfPart as (HparentOfPart & _ & HbeqParentPart). specialize(HparentOfPart HbeqPartRoot).
          destruct HparentOfPart as ([parentEntry HlookupParent] & HparentIsParts1). rewrite HbeqParentCurr in *.
          assert(HparentIsPart: In currentPart (getPartitions multiplexer s0)).
          { rewrite <-HgetPartsEqs1. assumption. }
          assert(HlookupParents0: lookup currentPart (memory s0) beqAddr = Some(PDT pdentry)) by intuition.
          assert(HblockParentMappeds0: In blockToShareInCurrPartAddr (getMappedBlocks currentPart s0))
            by intuition.
          unfold sh1entryAddr in Hsh1. rewrite HlookupBlocks0 in Hsh1.
          assert(HpartIsChild: In part (getChildren currentPart s0)).
          {
            rewrite HgetPartsEqs1 in HpartIsPart.
            assert(Hchild: isChild s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
            specialize(Hchild part currentPart HpartIsPart). apply Hchild. unfold pdentryParent.
            rewrite Hs1 in HlookupParts1. simpl in HlookupParts1.
            destruct (beqAddr sceaddr part) eqn:HbeqScePart; try(exfalso; congruence).
            rewrite HbeqSubblockSce in HlookupParts1. simpl in HlookupParts1.
            destruct (beqAddr idNewSubblock part) eqn:HbeqNewPart; try(exfalso; congruence).
            rewrite InternalLemmas.beqAddrTrue in HlookupParts1. rewrite HbeqCurrSubblock in HlookupParts1.
            rewrite <-beqAddrFalse in *.
            rewrite removeDupIdentity in HlookupParts1; try(apply not_eq_sym; congruence).
            rewrite removeDupIdentity in HlookupParts1; try(apply not_eq_sym; congruence).
            rewrite removeDupIdentity in HlookupParts1; try(apply not_eq_sym; congruence).
            rewrite removeDupIdentity in HlookupParts1; try(apply not_eq_sym; congruence).
            rewrite removeDupIdentity in HlookupParts1; try(apply not_eq_sym; congruence).
            rewrite removeDupIdentity in HlookupParts1; try(apply not_eq_sym; congruence).
            rewrite removeDupIdentity in HlookupParts1; try(apply not_eq_sym; congruence). simpl in HlookupParts1.
            destruct (beqAddr currentPart part) eqn:HbeqCurrPart.
            - rewrite <-beqAddrTrue in HbeqCurrPart. subst part.
              assert(HlookupCurrs0: lookup currentPart (memory s0) beqAddr = Some (PDT pdentry)) by intuition.
              rewrite HlookupCurrs0. injection HlookupParts1 as HpdentriesEq. rewrite <-HbeqParentCurr.
              rewrite <-HpdentriesEq. simpl.
              assert(Hpdentry0: pdentryInter0 =
                                              {|
                                                structure := structure pdentry;
                                                firstfreeslot := newFirstFreeSlotAddr;
                                                nbfreeslots := nbfreeslots pdentry;
                                                nbprepare := nbprepare pdentry;
                                                parent := parent pdentry;
                                                MPU := MPU pdentry;
                                                vidtAddr := vidtAddr pdentry
                                              |}) by intuition. rewrite Hpdentry0. simpl. reflexivity.
            - rewrite InternalLemmas.beqAddrTrue in HlookupParts1. rewrite <-beqAddrFalse in HbeqCurrPart.
              rewrite removeDupIdentity in HlookupParts1; try(apply not_eq_sym; congruence).
              rewrite removeDupIdentity in HlookupParts1; try(apply not_eq_sym; congruence).
              rewrite removeDupIdentity in HlookupParts1; try(apply not_eq_sym; congruence).
              rewrite HlookupParts1. apply eq_sym. assumption.
          }
          destruct (beqAddr idNewSubblock block) eqn:HbeqNewBlock.
          {
            exfalso. rewrite <-beqAddrTrue in HbeqNewBlock. subst block. intuition.
            destruct H114 as [optionfreeslotslist [s2 [n0 [n1 [n2 [nbleft Hprops]]]]]].
            assert(HgetBlocksCurrEq: forall block, In block (getMappedBlocks currentPart s) <->
                      firstfreeslot pdentry = block \/ In block (getMappedBlocks currentPart s0)) by intuition.
            assert(HnewMapped: In idNewSubblock (getMappedBlocks currentPart s)).
            {
              apply HgetBlocksCurrEq. left.
              assert(Hfirst: pdentryFirstFreeSlot currentPart idNewSubblock s0) by assumption.
              unfold pdentryFirstFreeSlot in Hfirst. rewrite HlookupParents0 in Hfirst. apply eq_sym. assumption.
            }
            rewrite HgetMappedBlocksParentEq in HnewMapped.
            assert(HbeqParentPartBis: currentPart <> part) by assumption.
            assert(Hdisjoint: DisjointKSEntries s1) by (unfold consistency1 in *; intuition).
            assert(HcurrIsPDT: isPDT currentPart s1).
            { unfold isPDT. rewrite HlookupParent. trivial. }
            assert(HpartIsPDT: isPDT part s1).
            { unfold isPDT. rewrite HlookupParts1. trivial. }
            specialize(Hdisjoint currentPart part HcurrIsPDT HpartIsPDT HbeqParentPartBis).
            destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
            unfold getMappedBlocks in HnewMapped. unfold getMappedBlocks in HblockMapped.
            apply InFilterPresentInList in HnewMapped. apply InFilterPresentInList in HblockMapped.
            specialize(Hdisjoint idNewSubblock HnewMapped). congruence.
          }
          assert(HlookupBlockBis: (exists bentryBlock, lookup block (memory s1) beqAddr = Some(BE bentryBlock)
                                                      /\ lookup block (memory s0) beqAddr = Some(BE bentryBlock))
                                  /\ bentryPFlag block true s1).
          {
            apply mappedBlockIsBE in HblockMapped.
            destruct HblockMapped as [bentryBlock (HlookupBlockBiss1 & Hpresent)]. split.
            - exists bentryBlock. split. assumption. rewrite Hs1 in HlookupBlockBiss1. simpl in HlookupBlockBiss1.
              destruct (beqAddr sceaddr block) eqn:HbeqSceBlockBis; try(exfalso; congruence).
              rewrite HbeqSubblockSce in HlookupBlockBiss1.
              rewrite InternalLemmas.beqAddrTrue in HlookupBlockBiss1.
              simpl in HlookupBlockBiss1. rewrite HbeqNewBlock in HlookupBlockBiss1.
              rewrite HbeqCurrSubblock in HlookupBlockBiss1. rewrite <-beqAddrFalse in *.
              rewrite removeDupIdentity in HlookupBlockBiss1; try(apply not_eq_sym; assumption).
              rewrite removeDupIdentity in HlookupBlockBiss1; try(apply not_eq_sym; assumption).
              rewrite removeDupIdentity in HlookupBlockBiss1; try(apply not_eq_sym; assumption).
              rewrite removeDupIdentity in HlookupBlockBiss1; try(apply not_eq_sym; assumption).
              rewrite removeDupIdentity in HlookupBlockBiss1; try(apply not_eq_sym; assumption).
              rewrite removeDupIdentity in HlookupBlockBiss1; try(apply not_eq_sym; assumption).
              rewrite removeDupIdentity in HlookupBlockBiss1; try(apply not_eq_sym; assumption).
              simpl in HlookupBlockBiss1.
              destruct (beqAddr currentPart block) eqn:HbeqCurrBlockBis; try(exfalso; congruence).
              rewrite InternalLemmas.beqAddrTrue in HlookupBlockBiss1. rewrite <-beqAddrFalse in HbeqCurrBlockBis.
              rewrite removeDupIdentity in HlookupBlockBiss1; try(apply not_eq_sym; assumption).
              rewrite removeDupIdentity in HlookupBlockBiss1; try(apply not_eq_sym; assumption).
              rewrite removeDupIdentity in HlookupBlockBiss1; try(apply not_eq_sym; assumption). assumption.
            - unfold bentryPFlag. rewrite HlookupBlockBiss1. apply eq_sym. assumption.
          }
          destruct HlookupBlockBis as ([bentryBlock (HlookupBlockBiss1 & HlookupBlockBiss0)] & HPFlagBlockBis).
          pose proof(lookupBEntryStartAddr block s1 bentryBlock HlookupBlockBiss1) as HstartBlockBis.
          pose proof(lookupBEntryEndAddr block s1 bentryBlock HlookupBlockBiss1) as HendBlockBis.
          set(addr := startAddr (blockrange bentryBlock)). fold addr in HstartBlockBis.
          assert(HwellFormed: wellFormedBlock s1) by (unfold consistency1 in *; intuition).
          specialize(HwellFormed block addr (endAddr (blockrange bentryBlock)) HPFlagBlockBis HstartBlockBis
            HendBlockBis). destruct HwellFormed as (HltAddrEndBlockBis & _).
          assert(HaddrInBlockBiss1: In addr (getAllPaddrAux [block] s1)).
          {
            simpl. rewrite HlookupBlockBiss1. rewrite app_nil_r. fold addr. apply getAllPaddrBlockIncl; lia.
          }
          specialize(Hincl addr HaddrInBlockBiss1).
          assert(HaddrInBlocks0: In addr (getAllPaddrAux [blockToShareInCurrPartAddr] s0)).
          {
            simpl. simpl in Hincl. rewrite HlookupBlocks0. rewrite HlookupBlocks1 in Hincl. assumption.
          }
          specialize(HnoChild currentPart pdentry blockToShareInCurrPartAddr sh1entryaddr HparentIsPart
              HlookupParents0 HblockParentMappeds0 Hsh1 HPDChild part addr HpartIsChild HaddrInBlocks0).
          assert(Hcontra: In addr (getMappedPaddr part s0)).
          {
            assert(HaddrInBlockBiss0: In addr (getAllPaddrAux [block] s0)).
            {
              simpl. simpl in HaddrInBlockBiss1. rewrite HlookupBlockBiss0.
              rewrite HlookupBlockBiss1 in HaddrInBlockBiss1. assumption.
            }
            assert(HblockMappeds0: In block (getMappedBlocks part s0)).
            {
              rewrite <-HgetMappedBlocksPartEq in HblockMapped. intuition.
              destruct H114 as [optionfreeslotslist [s2 [n0 [n1 [n2 [nbleft Hprops]]]]]].
              assert(HgetBlocksEq: forall partition, partition <> currentPart -> isPDT partition s0
                                  -> getMappedBlocks partition s = getMappedBlocks partition s0) by intuition.
              rewrite HgetBlocksEq in HblockMapped; try(assumption). intuition.
              apply childrenArePDT with currentPart; try(assumption).
              unfold consistency in *; unfold consistency1 in *; intuition.
            }
            pose proof (blockIsMappedAddrInPaddrList block addr (getMappedBlocks part s0) s0 HblockMappeds0
                HaddrInBlockBiss0) as HaddrInAllPaddr. assumption.
          }
          congruence.
        }
        assert(HlookupBlockParentEq: lookup blockParent (memory s) beqAddr
                                      = lookup blockParent (memory s1) beqAddr).
        {
          rewrite Hs. simpl. rewrite HbeqBlockBlockParent. rewrite <-beqAddrFalse in HbeqBlockBlockParent.
          rewrite removeDupIdentity; try(apply not_eq_sym; assumption). reflexivity.
        }
        split. unfold bentryStartAddr. rewrite HlookupBlockParentEq. assumption. intros addr HaddrInBlock.
        assert(HaddrInBlocks1: In addr (getAllPaddrAux [block] s1)).
        {
          rewrite Hs in HaddrInBlock. simpl in HaddrInBlock. simpl.
          destruct (beqAddr blockToShareInCurrPartAddr block) eqn:HbeqBlocks.
          - rewrite <-beqAddrTrue in HbeqBlocks. subst block. rewrite HnewB in HaddrInBlock.
            simpl in HaddrInBlock.
            unfold CBlock in HaddrInBlock. assert(cutAddr <= maxIdx) by (rewrite maxIdxEqualMaxAddr; apply Hp).
            destruct (Compare_dec.le_dec (cutAddr - startAddr (blockrange bentryShare)) maxIdx); try(lia).
            simpl in HaddrInBlock. rewrite HlookupBlocks1. rewrite app_nil_r in *.
            apply getAllPaddrBlockInclRev in HaddrInBlock. destruct HaddrInBlock as (HleStartAddr & HltAddrCut &
              _).
            unfold StateLib.Paddr.leb in *. apply eq_sym in HlebEndCut. apply PeanoNat.Nat.leb_gt in HlebEndCut.
            assert(HendBlock: bentryEndAddr blockToShareInCurrPartAddr blockToCutEndAddr s0) by intuition.
            unfold bentryEndAddr in HendBlock. rewrite HlookupBlocks0 in HendBlock. rewrite <-HendBlock in *.
            apply getAllPaddrBlockIncl; lia.
          - rewrite <-beqAddrFalse in HbeqBlocks.
            rewrite removeDupIdentity in HaddrInBlock; try(apply not_eq_sym); assumption.
        }
        specialize(Hincl addr HaddrInBlocks1). simpl in Hincl. simpl. rewrite HlookupBlockParentEq. assumption.
      - intros startBlock HstartBlock. apply HstartAbove. unfold bentryStartAddr in *. rewrite Hs in HstartBlock.
        simpl in HstartBlock. destruct (beqAddr blockToShareInCurrPartAddr block) eqn:HbeqBlocks.
        + rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupBlocks1.
          rewrite HnewB in HstartBlock. simpl in HstartBlock. unfold CBlock in HstartBlock.
          assert(cutAddr <= maxIdx) by (rewrite maxIdxEqualMaxAddr; apply Hp).
          destruct (Compare_dec.le_dec (cutAddr - startAddr (blockrange bentryShare)) maxIdx); try(lia).
          simpl in HstartBlock. assumption.
        + rewrite <-beqAddrFalse in HbeqBlocks.
          rewrite removeDupIdentity in HstartBlock; try(apply not_eq_sym); assumption.
      (* END originIsParentBlocksStart *)
    }

    assert(nextImpliesBlockWasCut s).
    { (* BEGIN nextImpliesBlockWasCut s *)
      assert(Hcons0: nextImpliesBlockWasCut s1) by (unfold consistency1 in *; intuition).
      intros part pdentryPart block scentryaddr scnext endaddr HpartIsPart HlookupPart HblockMapped HendBlock Hsce
        HbeqNextNull Hnext HbeqPartRoot. rewrite HgetPartsEq in HpartIsPart.
      assert(HlookupParts1: lookup part (memory s1) beqAddr = Some (PDT pdentryPart)).
      {
        rewrite Hs in HlookupPart. simpl in HlookupPart.
        destruct (beqAddr blockToShareInCurrPartAddr part) eqn:HbeqBlockPart; try(exfalso; congruence).
        rewrite <-beqAddrFalse in HbeqBlockPart.
        rewrite removeDupIdentity in HlookupPart; try(apply not_eq_sym; assumption). assumption.
      }
      assert(HgetMappedBlocksPartEq: getMappedBlocks part s = getMappedBlocks part s1).
      {
        rewrite Hs. apply getMappedBlocksEqBENoChange with bentryShare; try(assumption).
        rewrite HnewB. simpl. reflexivity.
      }
      rewrite HgetMappedBlocksPartEq in HblockMapped.
      assert(HgetBlocksParentEq: getMappedBlocks (parent pdentryPart) s
                                  = getMappedBlocks (parent pdentryPart) s1).
      {
        rewrite Hs. apply getMappedBlocksEqBENoChange with bentryShare; try(assumption).
        rewrite HnewB. simpl. reflexivity.
      }
      rewrite HgetBlocksParentEq.
      assert(Hnexts1: scentryNext scentryaddr scnext s1).
      {
        unfold scentryNext in *. rewrite Hs in Hnext. simpl in Hnext.
        destruct (beqAddr blockToShareInCurrPartAddr scentryaddr) eqn:HbeqBlockSce; try(exfalso; congruence).
        rewrite <-beqAddrFalse in HbeqBlockSce.
        rewrite removeDupIdentity in Hnext; try(apply not_eq_sym); assumption.
      }
      destruct (beqAddr blockToShareInCurrPartAddr block) eqn:HbeqBlocks.
      - rewrite <-beqAddrTrue in HbeqBlocks. subst block.
        assert(HendBlocks1: bentryEndAddr blockToShareInCurrPartAddr blockToCutEndAddr s1).
        {
          assert(HendBlocks0: bentryEndAddr blockToShareInCurrPartAddr blockToCutEndAddr s0) by intuition.
          unfold bentryEndAddr. rewrite <-HlookupBlocks1 in HlookupBlocks0. rewrite <-HlookupBlocks0.
          assumption.
        }
        specialize(Hcons0 part pdentryPart blockToShareInCurrPartAddr scentryaddr scnext blockToCutEndAddr
            HpartIsPart HlookupParts1 HblockMapped HendBlocks1 Hsce HbeqNextNull Hnexts1 HbeqPartRoot).
        destruct Hcons0 as [blockParent [endParent (HblockParentMapped & HendParent & HltEndEndParent & Hincl)]].
        exists blockParent. exists endParent.
        assert(HpartIsCurr: part = currentPart).
        {
          destruct (beqAddr part currentPart) eqn:HbeqPartCurr; try(apply beqAddrTrue; assumption).
          exfalso. rewrite <-beqAddrFalse in HbeqPartCurr.
          assert(HblockParentMappedCurr: In blockToShareInCurrPartAddr (getMappedBlocks currentPart s)).
          {
            intuition. destruct H115 as [optionfreeslotslist [s2 [n0 [n1 [n2 [nbleft Hprops]]]]]].
            assert(HgetBlocksCurrEq: (forall block, In block (getMappedBlocks currentPart s) <->
                firstfreeslot pdentry = block \/ In block (getMappedBlocks currentPart s0))) by intuition.
            apply HgetBlocksCurrEq. right. intuition.
          }
          rewrite <-HgetMappedBlocksPartEq in HblockMapped. unfold getMappedBlocks in HblockMapped.
          unfold getMappedBlocks in HblockParentMappedCurr. apply InFilterPresentInList in HblockMapped.
          apply InFilterPresentInList in HblockParentMappedCurr.
          assert(Hdisjoint: DisjointKSEntries s) by assumption.
          assert(HpartIsPDT: isPDT part s).
          { unfold isPDT. rewrite HlookupPart. trivial. }
          assert(HcurrIsPDT: isPDT currentPart s) by intuition.
          specialize(Hdisjoint part currentPart HpartIsPDT HcurrIsPDT HbeqPartCurr).
          destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
          specialize(Hdisjoint blockToShareInCurrPartAddr HblockMapped). congruence.
        }
        subst part.
        assert(HparentOfPart: parentOfPartitionIsPartition s1) by (unfold consistency1 in *; intuition).
        specialize(HparentOfPart currentPart pdentryPart HlookupParts1).
        destruct HparentOfPart as (HparentIsPart & _ & HbeqParentCurr).
        destruct (beqAddr blockToShareInCurrPartAddr blockParent) eqn:HbeqBlockBlockParent.
        {
          exfalso. rewrite <-beqAddrTrue in HbeqBlockBlockParent. subst blockParent.
          assert(Hdisjoint: DisjointKSEntries s1) by (unfold consistency1 in *; intuition).
          assert(HpartIsPDT: isPDT (parent pdentryPart) s1).
          {
            specialize(HparentIsPart HbeqPartRoot). destruct HparentIsPart as ([parentEntry HlookupParent] & _).
            unfold isPDT. rewrite HlookupParent. trivial.
          }
          assert(HcurrIsPDT: isPDT currentPart s1).
          { unfold isPDT. rewrite HlookupParts1. trivial. }
          specialize(Hdisjoint (parent pdentryPart) currentPart HpartIsPDT HcurrIsPDT HbeqParentCurr).
          destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
          unfold getMappedBlocks in HblockParentMapped. unfold getMappedBlocks in HblockMapped.
          apply InFilterPresentInList in HblockParentMapped. apply InFilterPresentInList in HblockMapped.
          specialize(Hdisjoint blockToShareInCurrPartAddr HblockParentMapped). congruence.
        }
        assert(HlookupBlockParentEq: lookup blockParent (memory s) beqAddr
                                      = lookup blockParent (memory s1) beqAddr).
        {
          rewrite Hs. simpl. rewrite HbeqBlockBlockParent. rewrite <-beqAddrFalse in HbeqBlockBlockParent.
          rewrite removeDupIdentity; try(apply not_eq_sym; assumption). reflexivity.
        }
        split. assumption. split. unfold bentryEndAddr. rewrite HlookupBlockParentEq. assumption.
        assert(Hbentry7: bentry7 = CBlockEntry (read bentryShare) (write bentryShare) (exec bentryShare)
                (present bentryShare) (accessible bentryShare) (blockindex bentryShare)
                (CBlock (startAddr (blockrange bentryShare)) cutAddr)) by intuition.
        unfold CBlockEntry in Hbentry7.
        assert(blockindex bentryShare < kernelStructureEntriesNb) by (apply Hidx).
        destruct (Compare_dec.lt_dec (blockindex bentryShare) kernelStructureEntriesNb); try(lia).
        assert(cutAddr <= maxIdx) by (rewrite maxIdxEqualMaxAddr; apply Hp).
        unfold StateLib.Paddr.leb in HlebEndCut. apply eq_sym in HlebEndCut.
        apply PeanoNat.Nat.leb_gt in HlebEndCut. split.
        + unfold bentryEndAddr in HendBlock. rewrite HlookupBlocks in HendBlock.
          rewrite Hbentry7 in HendBlock. simpl in HendBlock. unfold CBlock in HendBlock.
          destruct (Compare_dec.le_dec (cutAddr - startAddr (blockrange bentryShare)) maxIdx); try(lia).
          simpl in HendBlock. subst endaddr. lia.
        + intros addr HaddrInBlocks.
          assert(HaddrInBlocks1: In addr (getAllPaddrAux [blockToShareInCurrPartAddr] s1)).
          {
            simpl. simpl in HaddrInBlocks. rewrite HlookupBlocks1. rewrite HlookupBlocks in HaddrInBlocks.
            rewrite app_nil_r in *. unfold CBlock in Hbentry7.
            destruct (Compare_dec.le_dec (cutAddr - startAddr (blockrange bentryShare)) maxIdx); try(lia).
            rewrite Hbentry7 in HaddrInBlocks. simpl in HaddrInBlocks.
            apply getAllPaddrBlockInclRev in HaddrInBlocks.
            destruct HaddrInBlocks as (HleStartAddr & HltAddrCut & _). unfold bentryEndAddr in HendBlocks1.
            rewrite HlookupBlocks1 in HendBlocks1. rewrite <-HendBlocks1.
            apply getAllPaddrBlockIncl; lia.
          }
          specialize(Hincl addr HaddrInBlocks1). simpl. simpl in Hincl. rewrite HlookupBlockParentEq.
          assumption.
      - assert(HlookupBlockBisEq: lookup block (memory s) beqAddr = lookup block (memory s1) beqAddr).
        {
          rewrite Hs. simpl. rewrite HbeqBlocks. rewrite <-beqAddrFalse in HbeqBlocks.
          rewrite removeDupIdentity; try(apply not_eq_sym; assumption). reflexivity.
        }
        unfold bentryEndAddr in HendBlock. rewrite HlookupBlockBisEq in HendBlock.
        specialize(Hcons0 part pdentryPart block scentryaddr scnext endaddr HpartIsPart HlookupParts1
            HblockMapped HendBlock Hsce HbeqNextNull Hnexts1 HbeqPartRoot).
        destruct Hcons0 as [blockParent [endParent (HblockParentMapped & HendParent & HltEndEndParent & Hincl)]].
        destruct (beqAddr blockToShareInCurrPartAddr blockParent) eqn:HbeqBlockBlockParent.
        {
          rewrite <-beqAddrTrue in HbeqBlockBlockParent. subst blockParent. exfalso.
          assert(HblockParentMappeds0: In blockToShareInCurrPartAddr (getMappedBlocks currentPart s0))
              by intuition.
          assert(HblockParentMappeds1: In blockToShareInCurrPartAddr (getMappedBlocks currentPart s)).
          {
            intuition. destruct H115 as [optionfreeslotslist [s2 [n0 [n1 [n2 [nbleft Hprops]]]]]].
            assert(HgetBlocksCurrEq: (forall block, In block (getMappedBlocks currentPart s) <->
                firstfreeslot pdentry = block \/ In block (getMappedBlocks currentPart s0))) by intuition.
            apply HgetBlocksCurrEq. right. intuition.
          }
          assert(HparentIsCurr: parent pdentryPart = currentPart).
          {
            destruct (beqAddr (parent pdentryPart) currentPart) eqn:HbeqParentCurr;
                try(apply beqAddrTrue; assumption). exfalso. rewrite <-beqAddrFalse in HbeqParentCurr.
            rewrite <-HgetBlocksParentEq in HblockParentMapped. unfold getMappedBlocks in HblockParentMapped.
            unfold getMappedBlocks in HblockParentMappeds1. apply InFilterPresentInList in HblockParentMapped.
            apply InFilterPresentInList in HblockParentMappeds1.
            assert(Hdisjoint: DisjointKSEntries s) by assumption.
            assert(HpartIsPDT: isPDT (parent pdentryPart) s).
            {
              unfold isPDT. unfold getKSEntries in HblockParentMapped.
              destruct (lookup (parent pdentryPart) (memory s) beqAddr);
                  try(simpl in HblockParentMapped; congruence).
              destruct v; try(simpl in HblockParentMapped; congruence). trivial.
            }
            assert(HcurrIsPDT: isPDT currentPart s) by intuition.
            specialize(Hdisjoint (parent pdentryPart) currentPart HpartIsPDT HcurrIsPDT HbeqParentCurr).
            destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
            specialize(Hdisjoint blockToShareInCurrPartAddr HblockParentMapped). congruence.
          }
          rewrite HparentIsCurr in *.
          assert(HnoChild: noChildImpliesAddressesNotShared s0)
            by (unfold consistency in *; unfold consistency2 in *; intuition).
          assert(HgetPartsEqs1: getPartitions multiplexer s1 = getPartitions multiplexer s0).
          {
            intuition. destruct H115 as [optionfreeslotslist [s2 [n0 [n1 [n2 [nbleft Hprops]]]]]].
            assert(Hs2s0: getPartitions multiplexer s2 = getPartitions multiplexer s0) by intuition.
            assert(Hs1s2: getPartitions multiplexer s1 = getPartitions multiplexer s2) by intuition.
            rewrite <-Hs2s0. assumption.
          }
          assert(HparentOfPart: parentOfPartitionIsPartition s1)
              by (unfold consistency in *; unfold consistency1 in *; intuition).
          specialize(HparentOfPart part pdentryPart HlookupParts1). rewrite HparentIsCurr in *.
          destruct HparentOfPart as (HparentOfPart & _ & HbeqParentPart). specialize(HparentOfPart HbeqPartRoot).
          destruct HparentOfPart as ([parentEntry HlookupParent] & HparentIsParts1).
          assert(HparentIsPart: In currentPart (getPartitions multiplexer s0)).
          { rewrite <-HgetPartsEqs1. assumption. }
          assert(HlookupParents0: lookup currentPart (memory s0) beqAddr = Some(PDT pdentry)) by intuition.
          assert(HPDChild: exists sh1entry sh1entryaddr,
                              lookup sh1entryaddr (memory s0) beqAddr = Some (SHE sh1entry) /\
                              sh1entryPDchild sh1entryaddr PDChildAddr s0 /\
                              sh1entryAddr blockToShareInCurrPartAddr sh1entryaddr s0) by intuition.
          assert(HbeqNullPDChild: beqAddr nullAddr PDChildAddr = true) by intuition.
          assert(HpartIsChild: In part (getChildren currentPart s0)).
          {
            rewrite HgetPartsEqs1 in HpartIsPart.
            assert(Hchild: isChild s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
            specialize(Hchild part currentPart HpartIsPart). apply Hchild. unfold pdentryParent.
            rewrite Hs1 in HlookupParts1. simpl in HlookupParts1.
            destruct (beqAddr sceaddr part) eqn:HbeqScePart; try(exfalso; congruence).
            rewrite HbeqSubblockSce in HlookupParts1. simpl in HlookupParts1.
            destruct (beqAddr idNewSubblock part) eqn:HbeqNewPart; try(exfalso; congruence).
            rewrite InternalLemmas.beqAddrTrue in HlookupParts1. rewrite HbeqCurrSubblock in HlookupParts1.
            rewrite <-beqAddrFalse in *.
            rewrite removeDupIdentity in HlookupParts1; try(apply not_eq_sym; congruence).
            rewrite removeDupIdentity in HlookupParts1; try(apply not_eq_sym; congruence).
            rewrite removeDupIdentity in HlookupParts1; try(apply not_eq_sym; congruence).
            rewrite removeDupIdentity in HlookupParts1; try(apply not_eq_sym; congruence).
            rewrite removeDupIdentity in HlookupParts1; try(apply not_eq_sym; congruence).
            rewrite removeDupIdentity in HlookupParts1; try(apply not_eq_sym; congruence).
            rewrite removeDupIdentity in HlookupParts1; try(apply not_eq_sym; congruence). simpl in HlookupParts1.
            rewrite beqAddrFalse in HbeqParentPart. rewrite HbeqParentPart in HlookupParts1.
            rewrite InternalLemmas.beqAddrTrue in HlookupParts1. rewrite <-beqAddrFalse in HbeqParentPart.
            rewrite removeDupIdentity in HlookupParts1; try(apply not_eq_sym; congruence).
            rewrite removeDupIdentity in HlookupParts1; try(apply not_eq_sym; congruence).
            rewrite removeDupIdentity in HlookupParts1; try(apply not_eq_sym; congruence).
            rewrite HlookupParts1. apply eq_sym. assumption.
          }
          destruct (beqAddr idNewSubblock block) eqn:HbeqNewBlock.
          {
            exfalso. rewrite <-beqAddrTrue in HbeqNewBlock. subst block. intuition.
            destruct H115 as [optionfreeslotslist [s2 [n0 [n1 [n2 [nbleft Hprops]]]]]].
            assert(HgetBlocksCurrEq: forall block, In block (getMappedBlocks currentPart s) <->
                      firstfreeslot pdentry = block \/ In block (getMappedBlocks currentPart s0)) by intuition.
            assert(HnewMapped: In idNewSubblock (getMappedBlocks currentPart s)).
            {
              apply HgetBlocksCurrEq. left.
              assert(Hfirst: pdentryFirstFreeSlot currentPart idNewSubblock s0) by assumption.
              unfold pdentryFirstFreeSlot in Hfirst. rewrite HlookupParents0 in Hfirst. apply eq_sym. assumption.
            }
            rewrite HgetBlocksParentEq in HnewMapped.
            assert(HbeqParentPartBis: currentPart <> part) by assumption.
            assert(Hdisjoint: DisjointKSEntries s1) by (unfold consistency1 in *; intuition).
            assert(HcurrIsPDT: isPDT currentPart s1).
            { unfold isPDT. rewrite HlookupParent. trivial. }
            assert(HpartIsPDT: isPDT part s1).
            { unfold isPDT. rewrite HlookupParts1. trivial. }
            specialize(Hdisjoint currentPart part HcurrIsPDT HpartIsPDT HbeqParentPartBis).
            destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
            unfold getMappedBlocks in HnewMapped. unfold getMappedBlocks in HblockMapped.
            apply InFilterPresentInList in HnewMapped. apply InFilterPresentInList in HblockMapped.
            specialize(Hdisjoint idNewSubblock HnewMapped). congruence.
          }
          assert(HlookupBlockBis: (exists bentryBlock, lookup block (memory s1) beqAddr = Some(BE bentryBlock)
                                                      /\ lookup block (memory s0) beqAddr = Some(BE bentryBlock))
                                  /\ bentryPFlag block true s1).
          {
            apply mappedBlockIsBE in HblockMapped.
            destruct HblockMapped as [bentryBlock (HlookupBlockBiss1 & Hpresent)]. split.
            - exists bentryBlock. split. assumption. rewrite Hs1 in HlookupBlockBiss1. simpl in HlookupBlockBiss1.
              destruct (beqAddr sceaddr block) eqn:HbeqSceBlockBis; try(exfalso; congruence).
              rewrite HbeqSubblockSce in HlookupBlockBiss1.
              rewrite InternalLemmas.beqAddrTrue in HlookupBlockBiss1.
              simpl in HlookupBlockBiss1. rewrite HbeqNewBlock in HlookupBlockBiss1.
              rewrite HbeqCurrSubblock in HlookupBlockBiss1. rewrite <-beqAddrFalse in *.
              rewrite removeDupIdentity in HlookupBlockBiss1; try(apply not_eq_sym; assumption).
              rewrite removeDupIdentity in HlookupBlockBiss1; try(apply not_eq_sym; assumption).
              rewrite removeDupIdentity in HlookupBlockBiss1; try(apply not_eq_sym; assumption).
              rewrite removeDupIdentity in HlookupBlockBiss1; try(apply not_eq_sym; assumption).
              rewrite removeDupIdentity in HlookupBlockBiss1; try(apply not_eq_sym; assumption).
              rewrite removeDupIdentity in HlookupBlockBiss1; try(apply not_eq_sym; assumption).
              rewrite removeDupIdentity in HlookupBlockBiss1; try(apply not_eq_sym; assumption).
              simpl in HlookupBlockBiss1.
              destruct (beqAddr currentPart block) eqn:HbeqCurrBlockBis; try(exfalso; congruence).
              rewrite InternalLemmas.beqAddrTrue in HlookupBlockBiss1. rewrite <-beqAddrFalse in HbeqCurrBlockBis.
              rewrite removeDupIdentity in HlookupBlockBiss1; try(apply not_eq_sym; assumption).
              rewrite removeDupIdentity in HlookupBlockBiss1; try(apply not_eq_sym; assumption).
              rewrite removeDupIdentity in HlookupBlockBiss1; try(apply not_eq_sym; assumption). assumption.
            - unfold bentryPFlag. rewrite HlookupBlockBiss1. apply eq_sym. assumption.
          }
          destruct HlookupBlockBis as ([bentryBlock (HlookupBlockBiss1 & HlookupBlockBiss0)] & HPFlagBlockBis).
          pose proof(lookupBEntryStartAddr block s1 bentryBlock HlookupBlockBiss1) as HstartBlockBis.
          pose proof(lookupBEntryEndAddr block s1 bentryBlock HlookupBlockBiss1) as HendBlockBis.
          set(addr := startAddr (blockrange bentryBlock)). fold addr in HstartBlockBis.
          assert(HwellFormed: wellFormedBlock s1) by (unfold consistency1 in *; intuition).
          specialize(HwellFormed block addr (endAddr (blockrange bentryBlock)) HPFlagBlockBis HstartBlockBis
            HendBlockBis). destruct HwellFormed as (HltAddrEndBlockBis & _).
          assert(HaddrInBlockBiss1: In addr (getAllPaddrAux [block] s1)).
          {
            simpl. rewrite HlookupBlockBiss1. rewrite app_nil_r. fold addr. apply getAllPaddrBlockIncl; lia.
          }
          specialize(Hincl addr HaddrInBlockBiss1).
          assert(HaddrInBlocks0: In addr (getAllPaddrAux [blockToShareInCurrPartAddr] s0)).
          {
            simpl. simpl in Hincl. rewrite HlookupBlocks0. rewrite HlookupBlocks1 in Hincl. assumption.
          }
          destruct HPDChild as [sh1entry [sh1entryaddr (HlookupSh1 & HPDChild & Hsh1)]].
          unfold sh1entryAddr in Hsh1. rewrite HlookupBlocks0 in Hsh1. rewrite <-beqAddrTrue in HbeqNullPDChild.
          subst PDChildAddr.
          specialize(HnoChild currentPart pdentry blockToShareInCurrPartAddr sh1entryaddr HparentIsPart
              HlookupParents0 HblockParentMappeds0 Hsh1 HPDChild part addr HpartIsChild HaddrInBlocks0).
          assert(Hcontra: In addr (getMappedPaddr part s0)).
          {
            assert(HaddrInBlockBiss0: In addr (getAllPaddrAux [block] s0)).
            {
              simpl. simpl in HaddrInBlockBiss1. rewrite HlookupBlockBiss0.
              rewrite HlookupBlockBiss1 in HaddrInBlockBiss1. assumption.
            }
            assert(HblockMappeds0: In block (getMappedBlocks part s0)).
            {
              rewrite <-HgetMappedBlocksPartEq in HblockMapped. intuition.
              destruct H115 as [optionfreeslotslist [s2 [n0 [n1 [n2 [nbleft Hprops]]]]]].
              assert(HgetBlocksEq: forall partition, partition <> currentPart -> isPDT partition s0
                                  -> getMappedBlocks partition s = getMappedBlocks partition s0) by intuition.
              rewrite HgetBlocksEq in HblockMapped; try(assumption). intuition.
              apply childrenArePDT with currentPart; try(assumption).
              unfold consistency in *; unfold consistency1 in *; intuition.
            }
            pose proof (blockIsMappedAddrInPaddrList block addr (getMappedBlocks part s0) s0 HblockMappeds0
                HaddrInBlockBiss0) as HaddrInAllPaddr. assumption.
          }
          congruence.
        }
        exists blockParent. exists endParent.
        assert(HlookupBlockParentEq: lookup blockParent (memory s) beqAddr
                                      = lookup blockParent (memory s1) beqAddr).
        {
          rewrite Hs. simpl. rewrite HbeqBlockBlockParent. rewrite <-beqAddrFalse in HbeqBlockBlockParent.
          rewrite removeDupIdentity; try(apply not_eq_sym; assumption). reflexivity.
        }
        split. assumption. split. unfold bentryEndAddr. rewrite HlookupBlockParentEq. assumption. split.
        assumption. simpl. simpl in Hincl. rewrite HlookupBlockBisEq. rewrite HlookupBlockParentEq.
        assumption.
      (* END nextImpliesBlockWasCut *)
    }

    unfold consistency1. intuition.
  }
  split. apply Hprops. destruct Hprops as ((((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & [s1 [s0 [pdentry [pdentryInter0 [pdentryInter1 [newpdentry [bentry [bentry0 [bentry1 [bentry2 [bentry3
    [bentry4 [bentry5 [bentry6 [bentryShare [bentry7 [scentry [predCurrentNbFreeSlots [sceaddr
    [newFirstFreeSlotAddr Hprops]]]]]]]]]]]]]]]]]]]]) & _) & _) & _). split. intuition. split.
  {
    assert(HlookupCurr: lookup currentPart (memory s) beqAddr = Some (PDT newpdentry)) by intuition.
    assert(Hnull: nullAddrExists s) by (unfold consistency1 in *; intuition). unfold nullAddrExists in Hnull.
    unfold isPADDR in Hnull. intro Hcontra. subst currentPart. rewrite HlookupCurr in Hnull. congruence.
  }
  split.
  {
    assert(HlookupCurr: lookup currentPart (memory s) beqAddr = Some (PDT newpdentry)) by intuition.
    unfold isPDT. rewrite HlookupCurr. trivial.
  }
  intro HbeqBlockNull. unfold getAccessibleMappedBlocks.
  assert(HlookupCurr: lookup currentPart (memory s) beqAddr = Some (PDT newpdentry)) by intuition.
  rewrite HlookupCurr.
  assert(HblockMapped: In blockToShareInCurrPartAddr (getMappedBlocks currentPart s1)) by intuition.
  apply accessibleIsInFilterAccessible with bentry7. intuition.
  - assert(HAFlag: bentryAFlag blockToShareInCurrPartAddr true s) by intuition.
    assert(HlookupBlocks: lookup blockToShareInCurrPartAddr (memory s) beqAddr = Some (BE bentry7)) by intuition.
    unfold bentryAFlag in HAFlag. rewrite HlookupBlocks in HAFlag. apply eq_sym. assumption.
  - assert(HpropsBis: exists optionfreeslotslist s2 n0 n1 n2 nbleft,
              nbleft = CIndex (nbFreeSlots - 1) /\
              nbleft < maxIdx /\
              s0 =
              {|
                currentPartition := currentPartition s1;
                memory :=
                  add sceaddr (SCE {| origin := blockOrigin; next := next scentry |}) (memory s2) beqAddr
              |} /\
              optionfreeslotslist = getFreeSlotsListRec n1 newFirstFreeSlotAddr s2 nbleft /\
              getFreeSlotsListRec n2 newFirstFreeSlotAddr s0 nbleft = optionfreeslotslist /\
              optionfreeslotslist = getFreeSlotsListRec n0 newFirstFreeSlotAddr s1 nbleft /\
              n0 <= n1 /\
              nbleft < n0 /\
              n1 <= n2 /\
              nbleft < n2 /\
              n2 <= maxIdx + 1 /\
              (wellFormedFreeSlotsList optionfreeslotslist = False -> False) /\
              NoDup (filterOptionPaddr optionfreeslotslist) /\
              (In (firstfreeslot pdentry) (filterOptionPaddr optionfreeslotslist) -> False) /\
              (exists optionentrieslist : list optionPaddr,
                 optionentrieslist = getKSEntries currentPart s2 /\
                 getKSEntries currentPart s = optionentrieslist /\
                 optionentrieslist = getKSEntries currentPart s1 /\
                 In (firstfreeslot pdentry) (filterOptionPaddr optionentrieslist)) /\
              isPDT multiplexer s /\
              getPartitions multiplexer s2 = getPartitions multiplexer s1 /\
              getPartitions multiplexer s0 = getPartitions multiplexer s2 /\
              getChildren currentPart s2 = getChildren currentPart s1 /\
              getChildren currentPart s0 = getChildren currentPart s2 /\
              getConfigBlocks currentPart s2 = getConfigBlocks currentPart s1 /\
              getConfigBlocks currentPart s0 = getConfigBlocks currentPart s2 /\
              getConfigPaddr currentPart s2 = getConfigPaddr currentPart s1 /\
              getConfigPaddr currentPart s0 = getConfigPaddr currentPart s2 /\
              (forall block : paddr,
               In block (getMappedBlocks currentPart s) <->
               firstfreeslot pdentry = block \/ In block (getMappedBlocks currentPart s1)) /\
              ((forall addr : paddr,
                In addr (getMappedPaddr currentPart s) <-> In addr (getMappedPaddr currentPart s1)) /\
               length (getMappedPaddr currentPart s) = length (getMappedPaddr currentPart s1)) /\
              (forall block : paddr,
               In block (getAccessibleMappedBlocks currentPart s) <->
               firstfreeslot pdentry = block \/ In block (getAccessibleMappedBlocks currentPart s1)) /\
              (forall addr : paddr,
               In addr (getAccessibleMappedPaddr currentPart s) <->
               In addr
                 (getAllPaddrBlock (startAddr (blockrange bentry6)) (endAddr (blockrange bentry6)) ++
                  getAccessibleMappedPaddr currentPart s1)) /\
              (forall partition : paddr,
               (partition = currentPart -> False) ->
               isPDT partition s1 -> getKSEntries partition s = getKSEntries partition s1) /\
              (forall partition : paddr,
               (partition = currentPart -> False) ->
               isPDT partition s1 -> getMappedPaddr partition s = getMappedPaddr partition s1) /\
              (forall partition : paddr,
               (partition = currentPart -> False) ->
               isPDT partition s1 -> getConfigPaddr partition s = getConfigPaddr partition s1) /\
              (forall partition : paddr,
               (partition = currentPart -> False) ->
               isPDT partition s1 -> getPartitions partition s = getPartitions partition s1) /\
              (forall partition : paddr,
               (partition = currentPart -> False) ->
               isPDT partition s1 -> getChildren partition s = getChildren partition s1) /\
              (forall partition : paddr,
               (partition = currentPart -> False) ->
               isPDT partition s1 -> getMappedBlocks partition s = getMappedBlocks partition s1) /\
              (forall partition : paddr,
               (partition = currentPart -> False) ->
               isPDT partition s1 ->
               getAccessibleMappedBlocks partition s = getAccessibleMappedBlocks partition s1) /\
              (forall partition : paddr,
               (partition = currentPart -> False) ->
               isPDT partition s1 ->
               getAccessibleMappedPaddr partition s = getAccessibleMappedPaddr partition s1) /\
              (forall partition : paddr, isPDT partition s = isPDT partition s1)) by intuition.
    destruct HpropsBis as [optionfreeslotslist [s2 [n0 [n1 [n2 [nbleft (Hnbleft & Hlnbleft & Hs1Bis & _ &
          Hlists1 & Hlists0 & Hlebn0n1 & Hltnbleftn0 & Hlebn1n2 & Hltnbleftn2 & Hlebn2 & HwellFormed & HnoDup
          & HfirstFreeChanged & HgetKSEq & _ & HgetPartsEqs2s0 & HgetPartsEqs1s2 & HpropsBis)]]]]]].
    assert(HgetMappedEquiv: forall block, In block (getMappedBlocks currentPart s) <->
             firstfreeslot pdentry = block \/ In block (getMappedBlocks currentPart s1)) by intuition.
    apply HgetMappedEquiv. right. assumption.
}
  intro blockToShareEnabled. eapply bindRev.
{ (** readSCNextFromBlockEntryAddr **)
  eapply weaken. eapply readSCNextFromBlockEntryAddr.
  intros s Hprops. simpl. split. eapply Hprops. destruct Hprops as [s2 Hprops]. split. intuition.
  destruct Hprops as (Hprops1 & Hprops2).
  destruct Hprops1 as ((((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [s0 [s1 [_ [_ [_ [_ [_ [_ [_ [_ [_ [_
      [_ [_ [bentryShare [bentry7 [_ [_ [_ [_ (_ & _ & _ & _ & _ & HlookupBlocks2 & _)]]]]]]]]]]]]]]]]]]]]) & _)
      & _) & _).
  destruct Hprops2 as (_ & _ & _ & _ & _ & _ & [pdentry Hprops2]).
  destruct Hprops2 as (HlookupCurr & _ & _ & _ & Henabled & HnotEnabled). destruct blockToShareEnabled.
  - assert(Htriv: is_true true) by (unfold is_true; reflexivity). specialize(Henabled Htriv). exists bentry7.
    destruct Henabled as [_ (Hs & _)]. rewrite Hs. simpl.
    destruct (beqAddr currentPart blockToShareInCurrPartAddr) eqn:HbeqCurrBlock.
    {
      rewrite <-beqAddrTrue in HbeqCurrBlock. subst currentPart. exfalso; congruence.
    }
    rewrite <-beqAddrFalse in HbeqCurrBlock. rewrite removeDupIdentity; intuition.
  - assert(Htriv: ~ is_true false) by (unfold is_true; intro Hcontra; congruence). specialize(HnotEnabled Htriv).
    subst s. exists bentry7. assumption.
}
  intro originalNextSubblock. eapply bindRev.
{ (** writeSCNextFromBlockEntryAddr **)
  eapply weaken. apply writeSCNextFromBlockEntryAddr.
  intros s Hprops. simpl. destruct Hprops as ([s2 (Hprops & Hconsists2 & HcurrIsPDTs2 & Hconsists & HbeqCurrNull
      & _ & HcurrIsPDTs & Hprops2)] & HnextRight). split. unfold consistency1 in Hconsists; intuition.
  split. unfold consistency1 in Hconsists; intuition. split. unfold consistency1 in Hconsists; intuition.
  split. unfold consistency1 in Hconsists; intuition.
  destruct Hprops as ((((HnewIsBEs2 & Hzero & HlebNbFreeZero & HbeqNullPDChild & HlebCutStart & HlebEndCut &
    HsubCutStart & HsubEndCut & HminSize & Hsize1 & Hsize2 & HcutValid & [s0 [s1 [pdentry [pdentryInter0
    [pdentryInter1 [newpdentry [bentry [bentry0 [bentry1 [bentry2 [bentry3 [bentry4 [bentry5 [bentry6 [bentryShare
    [bentry7 [scentry [predCurrentNbFreeSlots [sceaddr [newFirstFreeSlotAddr (Hs2 & HlookupNews0 & HlookupNews2
    & Hprops)]]]]]]]]]]]]]]]]]]]]) & HkernNb) & HsuccKernNb) & HMPU).
  destruct Hprops2 as [pdentryCurrs2 (HlookupCurrs2 & HgetKSCurrEq & Hprops2 & HpartPDTEq & Henabled &
    HnotEnabled)]. exists bentry6. exists (blockindex bentry6).
  assert(HwellFormedShadow: wellFormedShadowCutIfBlockEntry s) by (unfold consistency1 in Hconsists; intuition).
  assert(HlookupNews: lookup idNewSubblock (memory s) beqAddr = Some (BE bentry6)).
  {
    destruct blockToShareEnabled.
    - assert(Htriv: is_true true) by (unfold is_true; reflexivity). specialize(Henabled Htriv).
      destruct Henabled as [pdentryCurrs (Hs & Henabled)]. rewrite Hs. simpl.
      destruct (beqAddr currentPart idNewSubblock) eqn:HbeqCurrNew.
      {
        rewrite <-beqAddrTrue in HbeqCurrNew. subst currentPart. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in HbeqCurrNew. rewrite removeDupIdentity; intuition.
    - assert(Htriv: ~is_true false) by (unfold is_true; intro Hcontra; congruence). specialize(HnotEnabled Htriv).
      subst s. assumption.
  }
  assert(HnewIsBEs: isBE idNewSubblock s) by (unfold isBE; rewrite HlookupNews; trivial).
  specialize(HwellFormedShadow idNewSubblock HnewIsBEs). destruct HwellFormedShadow as [scentryaddr (HsceIsSCE &
      Hsce)]. subst scentryaddr. unfold isSCE in HsceIsSCE.
  destruct (lookup (CPaddr (idNewSubblock + scoffset)) (memory s) beqAddr) eqn:HlookupNewSce;
      try(exfalso; congruence). destruct v; try(exfalso; congruence). exists s3. split. assumption. split.
  reflexivity. split. reflexivity. intuition.
  instantiate(1 := fun _ s => exists s3 s2 s1 s0
      predCurrentNbFreeSlots
      sceaddr newFirstFreeSlotAddr
      scentry scentryNew
      pdentryCurrs0 pdentryInter0 pdentryCurrs2
      bentry bentry0 bentry1 bentry2 bentry3 bentry4 bentry5 bentry6 bentryShares0 bentryShares2,
        s = {|
              currentPartition := currentPartition s3;
              memory :=
                add (CPaddr (idNewSubblock + scoffset))
                  (SCE {| origin := origin scentryNew; next := originalNextSubblock |}) (memory s3) beqAddr
            |}
        /\ consistency1 s
        /\ sceaddr = CPaddr (idNewSubblock + scoffset)
        /\ ~ isFreeSlot blockToShareInCurrPartAddr s
        /\ ~ isFreeSlot idNewSubblock s
        (* Properties in state s3 *)
        /\ consistency1 s3
        /\ isPDT currentPart s3
        /\ isBE idNewSubblock s3
        /\ (forall partition, isPDT partition s3 = isPDT partition s2)
        /\ getKSEntries currentPart s3 = getKSEntries currentPart s2
        /\ scentryNext (CPaddr (blockToShareInCurrPartAddr + scoffset)) originalNextSubblock s3
        /\ lookup idNewSubblock (memory s3) beqAddr = Some (BE bentry6)
        /\ lookup (CPaddr (idNewSubblock + scoffset)) (memory s3) beqAddr = Some (SCE scentryNew)
        /\ (forall partition, partition <> currentPart -> isPDT partition s2
                              -> getPartitions partition s3 = getPartitions partition s2)
        /\ (forall partition, partition <> currentPart -> isPDT partition s2
                              -> getConfigPaddr partition s3 = getConfigPaddr partition s2)
        /\ (forall partition, partition <> currentPart -> isPDT partition s2
                            -> getAccessibleMappedBlocks partition s3 = getAccessibleMappedBlocks partition s2)
        /\ (forall partition, partition <> currentPart -> isPDT partition s2
                              -> getChildren partition s3 = getChildren partition s2)
        /\ (forall partition, partition <> currentPart -> isPDT partition s2
                              -> getMappedBlocks partition s3 = getMappedBlocks partition s2)
        /\ (forall partition, partition <> currentPart -> isPDT partition s2
                              -> getMappedPaddr partition s3 = getMappedPaddr partition s2)
        /\ (forall partition, partition <> currentPart -> isPDT partition s2
                              -> getAccessibleMappedPaddr partition s3 = getAccessibleMappedPaddr partition s2)
        /\ ((~ is_true blockToShareEnabled) -> s3 = s2)
        /\ (is_true blockToShareEnabled ->
                exists pdentry1,
                  s3 =
                  {|
                    currentPartition := currentPartition s2;
                    memory :=
                      add currentPart
                        (PDT
                           {|
                             structure := structure pdentryCurrs2;
                             firstfreeslot := firstfreeslot pdentryCurrs2;
                             nbfreeslots := nbfreeslots pdentryCurrs2;
                             nbprepare := nbprepare pdentryCurrs2;
                             parent := parent pdentryCurrs2;
                             MPU :=
                               addElementAt blockMPURegionNb blockToShareInCurrPartAddr 
                                 (MPU pdentryCurrs2) nullAddr;
                             vidtAddr := vidtAddr pdentryCurrs2
                           |}) (memory s2) beqAddr
                  |} /\
                  lookup currentPart (memory s3) beqAddr = Some (PDT pdentry1) /\
                  pdentry1 =
                  {|
                    structure := structure pdentryCurrs2;
                    firstfreeslot := firstfreeslot pdentryCurrs2;
                    nbfreeslots := nbfreeslots pdentryCurrs2;
                    nbprepare := nbprepare pdentryCurrs2;
                    parent := parent pdentryCurrs2;
                    MPU := addElementAt blockMPURegionNb blockToShareInCurrPartAddr (MPU pdentryCurrs2) nullAddr;
                    vidtAddr := vidtAddr pdentryCurrs2
                  |} /\ pdentryNbFreeSlots currentPart (nbfreeslots pdentryCurrs2) s3)
        (* Properties in state s2 *)
        /\ s2 =
                {|
                  currentPartition := currentPartition s1;
                  memory :=
                    add blockToShareInCurrPartAddr
                      (BE
                         (CBlockEntry (read bentryShares0) (write bentryShares0) (exec bentryShares0)
                            (present bentryShares0) (accessible bentryShares0) (blockindex bentryShares0)
                            (CBlock (startAddr (blockrange bentryShares0)) cutAddr))) (memory s1) beqAddr
                |}
        /\ consistency1 s2
        /\ isBE idNewSubblock s2
        /\ lookup idNewSubblock (memory s2) beqAddr = Some (BE bentry6)
        /\ isPDT currentPart s2
        /\ lookup currentPart (memory s2) beqAddr = Some (PDT pdentryCurrs2)
        /\ isSCE sceaddr s2
        /\ isBE (firstfreeslot pdentryCurrs0) s2
        /\ pdentryNbFreeSlots currentPart predCurrentNbFreeSlots s2
        /\ bentryAFlag blockToShareInCurrPartAddr true s2
        /\ sh1entryPDflag (CPaddr (blockToShareInCurrPartAddr + sh1offset)) false s2
        /\ lookup blockToShareInCurrPartAddr (memory s2) beqAddr = Some (BE bentryShares2)
        /\ (exists MPUlist,
              pdentryMPU currentPart MPUlist s2
              /\ (blockMPURegionNb = CIndex defaultidx /\ (~ In blockToShareInCurrPartAddr MPUlist)
                    \/ nth blockMPURegionNb MPUlist nullAddr = blockToShareInCurrPartAddr))
        /\ (exists optionfreeslotslist s4 n0 n1 n2 nbleft,
                nbleft = CIndex (nbFreeSlots - 1) /\
                nbleft < maxIdx /\
                s1 =
                {|
                  currentPartition := currentPartition s0;
                  memory :=
                    add sceaddr (SCE {| origin := blockOrigin; next := next scentry |}) (memory s4) beqAddr
                |} /\
                optionfreeslotslist = getFreeSlotsListRec n1 newFirstFreeSlotAddr s4 nbleft /\
                getFreeSlotsListRec n2 newFirstFreeSlotAddr s1 nbleft = optionfreeslotslist /\
                optionfreeslotslist = getFreeSlotsListRec n0 newFirstFreeSlotAddr s0 nbleft /\
                n0 <= n1 /\
                nbleft < n0 /\
                n1 <= n2 /\
                nbleft < n2 /\
                n2 <= maxIdx + 1 /\
                (wellFormedFreeSlotsList optionfreeslotslist = False -> False) /\
                NoDup (filterOptionPaddr optionfreeslotslist) /\
                (~ In (firstfreeslot pdentryCurrs0) (filterOptionPaddr optionfreeslotslist)) /\
                (exists optionentrieslist : list optionPaddr,
                   optionentrieslist = getKSEntries currentPart s4 /\
                   getKSEntries currentPart s2 = optionentrieslist /\
                   optionentrieslist = getKSEntries currentPart s0 /\
                   In (firstfreeslot pdentryCurrs0) (filterOptionPaddr optionentrieslist)) /\
                isPDT multiplexer s2 /\
                getPartitions multiplexer s4 = getPartitions multiplexer s0 /\
                getPartitions multiplexer s1 = getPartitions multiplexer s4 /\
                getChildren currentPart s4 = getChildren currentPart s0 /\
                getChildren currentPart s1 = getChildren currentPart s4 /\
                getConfigBlocks currentPart s4 = getConfigBlocks currentPart s0 /\
                getConfigBlocks currentPart s1 = getConfigBlocks currentPart s4 /\
                getConfigPaddr currentPart s4 = getConfigPaddr currentPart s0 /\
                getConfigPaddr currentPart s1 = getConfigPaddr currentPart s4 /\
                (forall block : paddr,
                 In block (getMappedBlocks currentPart s2) <->
                 firstfreeslot pdentryCurrs0 = block \/ In block (getMappedBlocks currentPart s0)) /\
                ((forall addr : paddr,
                  In addr (getMappedPaddr currentPart s2) <-> In addr (getMappedPaddr currentPart s0))
                  /\ length (getMappedPaddr currentPart s2) = length (getMappedPaddr currentPart s0)) /\
                (forall block : paddr,
                 In block (getAccessibleMappedBlocks currentPart s2) <->
                 firstfreeslot pdentryCurrs0 = block \/ In block (getAccessibleMappedBlocks currentPart s0)) /\
                (forall addr : paddr,
                 In addr (getAccessibleMappedPaddr currentPart s2) <->
                 In addr
                   (getAllPaddrBlock (startAddr (blockrange bentry6)) (endAddr (blockrange bentry6)) ++
                    getAccessibleMappedPaddr currentPart s0)) /\
                (forall partition : paddr,
                 (partition = currentPart -> False) ->
                 isPDT partition s0 -> getKSEntries partition s2 = getKSEntries partition s0) /\
                (forall partition : paddr,
                 (partition = currentPart -> False) ->
                 isPDT partition s0 -> getMappedPaddr partition s2 = getMappedPaddr partition s0) /\
                (forall partition : paddr,
                 (partition = currentPart -> False) ->
                 isPDT partition s0 -> getConfigPaddr partition s2 = getConfigPaddr partition s0) /\
                (forall partition : paddr,
                 (partition = currentPart -> False) ->
                 isPDT partition s0 -> getPartitions partition s2 = getPartitions partition s0) /\
                (forall partition : paddr,
                 (partition = currentPart -> False) ->
                 isPDT partition s0 -> getChildren partition s2 = getChildren partition s0) /\
                (forall partition : paddr,
                 (partition = currentPart -> False) ->
                 isPDT partition s0 -> getMappedBlocks partition s2 = getMappedBlocks partition s0) /\
                (forall partition : paddr,
                 (partition = currentPart -> False) ->
                 isPDT partition s0 ->
                 getAccessibleMappedBlocks partition s2 = getAccessibleMappedBlocks partition s0) /\
                (forall partition : paddr,
                 (partition = currentPart -> False) ->
                 isPDT partition s0 ->
                 getAccessibleMappedPaddr partition s2 = getAccessibleMappedPaddr partition s0) /\
                (forall partition : paddr, isPDT partition s2 = isPDT partition s0))
        (* Properties in state s1 *)
        /\ s1 =
                {|
                  currentPartition := currentPartition s0;
                  memory :=
                    add sceaddr (SCE {| origin := blockOrigin; next := next scentry |})
                      (add idNewSubblock
                         (BE
                            (CBlockEntry (read bentry5) (write bentry5) blockX (present bentry5)
                               (accessible bentry5) (blockindex bentry5) (blockrange bentry5)))
                         (add idNewSubblock
                            (BE
                               (CBlockEntry (read bentry4) blockW (exec bentry4) (present bentry4)
                                  (accessible bentry4) (blockindex bentry4) (blockrange bentry4)))
                            (add idNewSubblock
                               (BE
                                  (CBlockEntry blockR (write bentry3) (exec bentry3) (present bentry3)
                                     (accessible bentry3) (blockindex bentry3) (blockrange bentry3)))
                               (add idNewSubblock
                                  (BE
                                     (CBlockEntry (read bentry2) (write bentry2) (exec bentry2) 
                                        (present bentry2) true (blockindex bentry2) (blockrange bentry2)))
                                  (add idNewSubblock
                                     (BE
                                        (CBlockEntry (read bentry1) (write bentry1) (exec bentry1) true
                                           (accessible bentry1) (blockindex bentry1) (blockrange bentry1)))
                                     (add idNewSubblock
                                        (BE
                                           (CBlockEntry (read bentry0) (write bentry0) 
                                              (exec bentry0) (present bentry0) (accessible bentry0)
                                              (blockindex bentry0)
                                              (CBlock (startAddr (blockrange bentry0)) blockEndAddr)))
                                        (add idNewSubblock
                                           (BE
                                              (CBlockEntry (read bentry) (write bentry) 
                                                 (exec bentry) (present bentry) (accessible bentry)
                                                 (blockindex bentry)
                                                 (CBlock cutAddr (endAddr (blockrange bentry)))))
                                           (add currentPart
                                              (PDT
                                                 {|
                                                   structure := structure pdentryInter0;
                                                   firstfreeslot := firstfreeslot pdentryInter0;
                                                   nbfreeslots := predCurrentNbFreeSlots;
                                                   nbprepare := nbprepare pdentryInter0;
                                                   parent := parent pdentryInter0;
                                                   MPU := MPU pdentryInter0;
                                                   vidtAddr := vidtAddr pdentryInter0
                                                 |})
                                              (add currentPart
                                                 (PDT
                                                    {|
                                                      structure := structure pdentryCurrs0;
                                                      firstfreeslot := newFirstFreeSlotAddr;
                                                      nbfreeslots := nbfreeslots pdentryCurrs0;
                                                      nbprepare := nbprepare pdentryCurrs0;
                                                      parent := parent pdentryCurrs0;
                                                      MPU := MPU pdentryCurrs0;
                                                      vidtAddr := vidtAddr pdentryCurrs0
                                                    |}) (memory s0) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr)
                                  beqAddr) beqAddr) beqAddr) beqAddr) beqAddr
                |}
        /\ consistency1 s1
        /\ sh1entryPDflag (CPaddr (blockToShareInCurrPartAddr + sh1offset)) false s1
        /\ lookup blockToShareInCurrPartAddr (memory s1) beqAddr = Some (BE bentryShares0)
        (* Properties in state s0 *)
        /\ kernelDataIsolation s0
        /\ verticalSharing s0
        /\ partitionsIsolation s0
        /\ consistency s0
        /\ isPDT currentPart s0
        /\ lookup currentPart (memory s0) beqAddr = Some (PDT pdentryCurrs0)
        /\ currentPart = currentPartition s0
        /\ pdentryNbFreeSlots currentPart nbFreeSlots s0
        /\ pdentryFirstFreeSlot currentPart idNewSubblock s0
        /\ isSCE sceaddr s0
        /\ lookup blockToShareInCurrPartAddr (memory s0) beqAddr = Some (BE bentryShares0)
        /\ bentryEndAddr blockToShareInCurrPartAddr blockEndAddr s0
        /\ bentryEndAddr blockToShareInCurrPartAddr blockToCutEndAddr s0
        /\ bentryStartAddr blockToShareInCurrPartAddr blockToCutStartAddr s0
        /\ bentryXFlag blockToShareInCurrPartAddr blockX s0
        /\ bentryRFlag blockToShareInCurrPartAddr blockR s0
        /\ bentryWFlag blockToShareInCurrPartAddr blockW s0
        /\ bentryPFlag blockToShareInCurrPartAddr true s0
        /\ bentryAFlag blockToShareInCurrPartAddr true s0
        /\ isBE (firstfreeslot pdentryCurrs0) s0
        /\ bentryEndAddr (firstfreeslot pdentryCurrs0) newFirstFreeSlotAddr s0
        /\ lookup idNewSubblock (memory s0) beqAddr = Some (BE bentry)
        /\ In blockToShareInCurrPartAddr (getMappedBlocks currentPart s0)
        /\ scentryOrigin (CPaddr (blockToShareInCurrPartAddr + scoffset)) blockOrigin s0
        /\ lookup sceaddr (memory s0) beqAddr = Some (SCE scentry)
        /\ (exists sh1entry sh1entryaddr,
                    lookup sh1entryaddr (memory s0) beqAddr = Some (SHE sh1entry)
                    /\ sh1entryPDchild sh1entryaddr PDChildAddr s0
                    /\ sh1entryAddr blockToShareInCurrPartAddr sh1entryaddr s0)
        /\ (forall blockInParentPartitionAddr,
             In blockInParentPartitionAddr (getMappedBlocks (parent pdentryCurrs0) s0)
             -> bentryStartAddr blockInParentPartitionAddr blockToCutStartAddr s0
             -> bentryEndAddr blockInParentPartitionAddr blockToCutEndAddr s0
             -> bentryAFlag blockInParentPartitionAddr false s0)
        (* Other properties *)
        /\ bentry6 = CBlockEntry (read bentry5) (write bentry5) blockX (present bentry5)
                          (accessible bentry5) (blockindex bentry5) (blockrange bentry5)
        /\ bentry5 = CBlockEntry (read bentry4) blockW (exec bentry4) (present bentry4)
                          (accessible bentry4) (blockindex bentry4) (blockrange bentry4)
        /\ bentry4 = CBlockEntry blockR (write bentry3) (exec bentry3) (present bentry3)
                          (accessible bentry3) (blockindex bentry3) (blockrange bentry3)
        /\ bentry3 = CBlockEntry (read bentry2) (write bentry2) (exec bentry2) (present bentry2) true
                          (blockindex bentry2) (blockrange bentry2)
        /\ bentry2 = CBlockEntry (read bentry1) (write bentry1) (exec bentry1) true (accessible bentry1)
                          (blockindex bentry1) (blockrange bentry1)
        /\ bentry1 = CBlockEntry (read bentry0) (write bentry0) (exec bentry0) (present bentry0)
                          (accessible bentry0) (blockindex bentry0)
                          (CBlock (startAddr (blockrange bentry0)) blockEndAddr)
        /\ bentry0 = CBlockEntry (read bentry) (write bentry) (exec bentry) (present bentry)
                          (accessible bentry) (blockindex bentry) (CBlock cutAddr (endAddr (blockrange bentry)))
        /\ false = StateLib.Paddr.leb cutAddr blockToCutStartAddr
        /\ false = StateLib.Paddr.leb blockToCutEndAddr cutAddr
        /\ StateLib.Paddr.subPaddr cutAddr blockToCutStartAddr = Some subblock1Size
        /\ StateLib.Paddr.subPaddr blockToCutEndAddr cutAddr = Some subblock2Size
        /\ isBlock1TooSmall = StateLib.Index.ltb subblock1Size Constants.minBlockSize
        /\ isBlock2TooSmall = StateLib.Index.ltb subblock2Size Constants.minBlockSize
        /\ pdentryInter0 = {|
                             structure := structure pdentryCurrs0;
                             firstfreeslot := newFirstFreeSlotAddr;
                             nbfreeslots := nbfreeslots pdentryCurrs0;
                             nbprepare := nbprepare pdentryCurrs0;
                             parent := parent pdentryCurrs0;
                             MPU := MPU pdentryCurrs0;
                             vidtAddr := vidtAddr pdentryCurrs0
                           |}
        /\ beqAddr nullAddr PDChildAddr = true).
  simpl. exists s. exists s2. exists s1. exists s0. exists predCurrentNbFreeSlots. exists sceaddr.
  exists newFirstFreeSlotAddr. exists scentry. exists s3. exists pdentry. exists pdentryInter0.
  exists pdentryCurrs2. exists bentry. exists bentry0. exists bentry1. exists bentry2. exists bentry3.
  exists bentry4. exists bentry5. exists bentry6. exists bentryShare. exists bentry7. subst minBlockSize.
  intuition.
  - set(newS := {|
                  currentPartition := currentPartition s;
                  memory :=
                    add (CPaddr (idNewSubblock + scoffset))
                      (SCE {| origin := origin s3; next := originalNextSubblock |}) (memory s) beqAddr
                |}).
    assert(HwellFormedShadow: wellFormedShadowCutIfBlockEntry s) by (unfold consistency1 in *; intuition).
    specialize(HwellFormedShadow idNewSubblock HnewIsBEs). clear HsceIsSCE.
    destruct HwellFormedShadow as [sce (HsceIsSCE & Hsce)]. subst sce.

    assert(nullAddrExists newS).
    { (* BEGIN nullAddrExists newS *)
      assert(Hcons0: nullAddrExists s) by (unfold consistency1 in *; intuition).
      unfold nullAddrExists in *. unfold isPADDR in *. simpl.
      destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) nullAddr) eqn:HbeqNewSceNull.
      {
        rewrite <-beqAddrTrue in HbeqNewSceNull. rewrite HbeqNewSceNull in *.
        unfold isSCE in HsceIsSCE. destruct (lookup nullAddr (memory s) beqAddr); try(exfalso; congruence).
        destruct v; congruence.
      }
      rewrite <-beqAddrFalse in HbeqNewSceNull. rewrite removeDupIdentity; intuition.
      (* END nullAddrExists *)
    }

    assert(wellFormedFstShadowIfBlockEntry newS).
    { (* BEGIN wellFormedFstShadowIfBlockEntry newS *)
      assert(Hcons0: wellFormedFstShadowIfBlockEntry s) by (unfold consistency1 in *; intuition).
      intros pa HpaIsBE.
      assert(HpaIsBEs: isBE pa s).
      {
        unfold isBE in HpaIsBE. simpl in HpaIsBE.
        destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) pa) eqn:HbeqNewScePa; try(exfalso; congruence).
        rewrite <-beqAddrFalse in HbeqNewScePa. rewrite removeDupIdentity in HpaIsBE; intuition.
      }
      specialize(Hcons0 pa HpaIsBEs). unfold isSHE in *. simpl.
      destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) (CPaddr (pa + sh1offset))) eqn:HbeqNewScePaSh1.
      {
        unfold isSCE in HsceIsSCE. rewrite <-beqAddrTrue in HbeqNewScePaSh1. rewrite HbeqNewScePaSh1 in *.
        destruct (lookup (CPaddr (pa + sh1offset)) (memory s) beqAddr); try(congruence). destruct v; congruence.
      }
      rewrite <-beqAddrFalse in HbeqNewScePaSh1. rewrite removeDupIdentity; intuition.
      (* END wellFormedFstShadowIfBlockEntry *)
    }

    assert(PDTIfPDFlag newS).
    { (* BEGIN PDTIfPDFlag newS *)
      assert(Hcons0: PDTIfPDFlag s) by (unfold consistency1 in *; intuition).
      intros idPDchild sh1entryaddr (HcheckChild & Hsh1entry).
      assert(HcheckChilds: true = checkChild idPDchild s sh1entryaddr
                            /\ sh1entryAddr idPDchild sh1entryaddr s).
      {
        unfold checkChild in *. unfold sh1entryAddr in *. simpl in HcheckChild. simpl in Hsh1entry.
        destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) idPDchild) eqn:HbeqNewSceId;
            try(exfalso; congruence). rewrite <-beqAddrFalse in HbeqNewSceId.
        rewrite removeDupIdentity in Hsh1entry; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in HcheckChild; try(apply not_eq_sym; assumption). split; try(assumption).
        destruct (lookup idPDchild (memory s) beqAddr); try(congruence). destruct v; try(congruence).
        destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) sh1entryaddr) eqn:HbeqNewSceIdSh1;
            try(exfalso; congruence). rewrite <-beqAddrFalse in HbeqNewSceIdSh1.
        rewrite removeDupIdentity in HcheckChild; intuition.
      }
      specialize(Hcons0 idPDchild sh1entryaddr HcheckChilds). destruct Hcons0 as (HAFlag & HPFlag & [startaddr
        (Hstart & HentryStart)]).
      assert(HlookupEq: lookup idPDchild (memory newS) beqAddr = lookup idPDchild (memory s) beqAddr).
      {
        simpl. unfold sh1entryAddr in Hsh1entry. simpl in Hsh1entry.
        destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) idPDchild) eqn:HbeqNewSceId;
            try(exfalso; congruence). rewrite <-beqAddrFalse in HbeqNewSceId.
        rewrite removeDupIdentity; intuition.
      }
      unfold bentryAFlag. unfold bentryPFlag. unfold bentryStartAddr. unfold entryPDT in *. rewrite HlookupEq.
      split. assumption. split. assumption. exists startaddr. split. assumption.
      destruct (lookup idPDchild (memory s) beqAddr); try(congruence). destruct v; try(congruence). simpl.
      destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) (startAddr (blockrange b))) eqn:HbeqNewSceStart.
      {
        rewrite <-beqAddrTrue in HbeqNewSceStart. unfold isSCE in HsceIsSCE. rewrite HbeqNewSceStart in *.
        destruct (lookup (startAddr (blockrange b)) (memory s) beqAddr); try(congruence). destruct v; congruence.
      }
      rewrite <-beqAddrFalse in HbeqNewSceStart. rewrite removeDupIdentity; intuition.
      (* END PDTIfPDFlag *)
    }

    assert(AccessibleNoPDFlag newS).
    { (* BEGIN AccessibleNoPDFlag newS *)
      assert(Hcons0: AccessibleNoPDFlag s) by (unfold consistency1 in *; intuition).
      intros block sh1entryaddr HblockIsBE Hsh1 HAFlag.
      assert(HlookupEq: lookup block (memory newS) beqAddr = lookup block (memory s) beqAddr).
      {
        unfold isBE in HblockIsBE. simpl. simpl in HblockIsBE.
        destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) block) eqn:HbeqNewSceBlock;
            try(exfalso; congruence). rewrite <-beqAddrFalse in HbeqNewSceBlock.
        rewrite removeDupIdentity; intuition.
      }
      unfold isBE in HblockIsBE. unfold sh1entryAddr in Hsh1. unfold bentryAFlag in HAFlag.
      rewrite HlookupEq in *. specialize(Hcons0 block sh1entryaddr HblockIsBE Hsh1 HAFlag).
      unfold sh1entryPDflag in *. simpl.
      destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) sh1entryaddr) eqn:HbeqNewSceBlockSh1.
      {
        unfold isSCE in HsceIsSCE. rewrite <-beqAddrTrue in HbeqNewSceBlockSh1. rewrite HbeqNewSceBlockSh1 in *.
        destruct (lookup sh1entryaddr (memory s) beqAddr); try(congruence). destruct v; congruence.
      }
      rewrite <-beqAddrFalse in HbeqNewSceBlockSh1. rewrite removeDupIdentity; intuition.
      (* END AccessibleNoPDFlag *)
    }

    assert(FirstFreeSlotPointerIsBEAndFreeSlot newS).
    { (* BEGIN FirstFreeSlotPointerIsBEAndFreeSlot newS *)
      assert(Hcons0: FirstFreeSlotPointerIsBEAndFreeSlot s) by (unfold consistency1 in *; intuition).
      intros pd pdentryPd HlookupPd HbeqFirstFreeNull.
      assert(HlookupPds: lookup pd (memory s) beqAddr = Some (PDT pdentryPd)).
      {
        simpl in HlookupPd.
        destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) pd) eqn:HbeqNewScePd; try(exfalso; congruence).
        rewrite <-beqAddrFalse in HbeqNewScePd. rewrite removeDupIdentity in HlookupPd; intuition.
      }
      specialize(Hcons0 pd pdentryPd HlookupPds HbeqFirstFreeNull). destruct Hcons0 as (_ & HfirstIsFree).
      unfold isBE. unfold isFreeSlot in *. simpl.
      destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) (firstfreeslot pdentryPd)) eqn:HbeqNewSceFirst.
      {
        unfold isSCE in HsceIsSCE. rewrite <-beqAddrTrue in HbeqNewSceFirst. rewrite HbeqNewSceFirst in *.
        exfalso. destruct (lookup (firstfreeslot pdentryPd) (memory s) beqAddr); try(congruence).
        destruct v; congruence.
      }
      rewrite <-beqAddrFalse in HbeqNewSceFirst. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      destruct (lookup (firstfreeslot pdentryPd) (memory s) beqAddr) eqn:HlookupFirst; try(exfalso; congruence).
      destruct v; try(exfalso; congruence). split. trivial.
      destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) (CPaddr (firstfreeslot pdentryPd + sh1offset)))
        eqn:HbeqNewSceFirstSh1.
      {
        rewrite <-beqAddrTrue in HbeqNewSceFirstSh1. rewrite <-HbeqNewSceFirstSh1 in *. unfold isSCE in HsceIsSCE.
        destruct (lookup (CPaddr (idNewSubblock + scoffset)) (memory s) beqAddr); try(congruence).
        destruct v; congruence.
      }
      rewrite <-beqAddrFalse in HbeqNewSceFirstSh1. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      destruct (lookup (CPaddr (firstfreeslot pdentryPd + sh1offset)) (memory s) beqAddr); try(congruence).
      destruct v; try(congruence).
      destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) (CPaddr (firstfreeslot pdentryPd + scoffset)))
        eqn:HbeqNewSceFirstSce.
      {
        rewrite <-beqAddrTrue in HbeqNewSceFirstSce. rewrite <-HbeqNewSceFirstSce in *. exfalso.
        destruct (beqAddr idNewSubblock (firstfreeslot pdentryPd)) eqn:HbeqNewFirst.
        - rewrite <-beqAddrTrue in HbeqNewFirst. subst idNewSubblock. rewrite HlookupNews in HlookupFirst.
          injection HlookupFirst as HbentriesEq. subst b.
          destruct (lookup (CPaddr (firstfreeslot pdentryPd + scoffset)) (memory s) beqAddr) eqn:HlookupFirstSce;
              try(congruence).
          destruct v; try(congruence). destruct HfirstIsFree as (_ & _ & _ & _ & _ & Hcontra & _).
          rewrite H15 in Hcontra. unfold CBlockEntry in Hcontra.
          assert(blockindex bentry5 < kernelStructureEntriesNb) by (apply Hidx).
          destruct (Compare_dec.lt_dec (blockindex bentry5) kernelStructureEntriesNb); try(lia).
          simpl in Hcontra. rewrite H17 in Hcontra. unfold CBlockEntry in Hcontra.
          assert(blockindex bentry4 < kernelStructureEntriesNb) by (apply Hidx).
          destruct (Compare_dec.lt_dec (blockindex bentry4) kernelStructureEntriesNb); try(lia).
          simpl in Hcontra. rewrite H19 in Hcontra. unfold CBlockEntry in Hcontra.
          assert(blockindex bentry3 < kernelStructureEntriesNb) by (apply Hidx).
          destruct (Compare_dec.lt_dec (blockindex bentry3) kernelStructureEntriesNb); try(lia).
          simpl in Hcontra. rewrite H21 in Hcontra. unfold CBlockEntry in Hcontra.
          assert(blockindex bentry2 < kernelStructureEntriesNb) by (apply Hidx).
          destruct (Compare_dec.lt_dec (blockindex bentry2) kernelStructureEntriesNb); try(lia).
          simpl in Hcontra. congruence.
        - rewrite <-beqAddrFalse in HbeqNewFirst. unfold CPaddr in HbeqNewSceFirstSce.
          destruct (Compare_dec.le_dec (idNewSubblock + scoffset) maxAddr) eqn:HleNewSceMax.
          + destruct (Compare_dec.le_dec (firstfreeslot pdentryPd + scoffset) maxAddr).
            * injection HbeqNewSceFirstSce as HsceEq. contradict HbeqNewFirst.
              destruct idNewSubblock. destruct (firstfreeslot pdentryPd).  simpl in HsceEq.
              assert(p = p0) by lia. subst p0. f_equal. apply proof_irrelevance.
            * assert(HbeqNewSceNull: CPaddr (idNewSubblock + scoffset) = nullAddr).
              {
                unfold nullAddr. injection HbeqNewSceFirstSce as HbeqNewSceNull. rewrite HbeqNewSceNull.
                reflexivity.
              }
              assert(Hnull: nullAddrExists s) by (unfold consistency1 in *; intuition).
              unfold nullAddrExists in Hnull. unfold isPADDR in Hnull. rewrite HbeqNewSceNull in *.
              rewrite HlookupNewSce in Hnull. congruence.
          + assert(HbeqNewScenull: CPaddr (idNewSubblock + scoffset) = nullAddr).
            {
              unfold nullAddr. unfold CPaddr. rewrite HleNewSceMax.
              destruct (Compare_dec.le_dec 0 maxAddr); try(lia). f_equal. apply proof_irrelevance.
            }
            assert(Hnull: nullAddrExists s) by (unfold consistency1 in *; intuition).
            unfold nullAddrExists in Hnull. unfold isPADDR in Hnull. rewrite HbeqNewScenull in *.
            rewrite HlookupNewSce in Hnull. congruence.
      }
      rewrite <-beqAddrFalse in HbeqNewSceFirstSce. rewrite removeDupIdentity; intuition.
      (* END FirstFreeSlotPointerIsBEAndFreeSlot *)
    }

    assert(multiplexerIsPDT newS).
    { (* BEGIN multiplexerIsPDT newS *)
      assert(Hcons0: multiplexerIsPDT s) by (unfold consistency1 in *; intuition).
      unfold multiplexerIsPDT in *. unfold isPDT in *. simpl.
      destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) multiplexer) eqn:HbeqNewSceMult.
      {
        rewrite <-beqAddrTrue in HbeqNewSceMult. rewrite HbeqNewSceMult in *. unfold isSCE in HsceIsSCE.
        destruct (lookup multiplexer (memory s) beqAddr); try(congruence). destruct v; congruence.
      }
      rewrite <-beqAddrFalse in HbeqNewSceMult. rewrite removeDupIdentity; intuition.
      (* END multiplexerIsPDT *)
    }

    assert(HcurrPartEq: currentPartition newS = currentPartition s).
    { simpl. reflexivity. }

    assert(HgetPartsEq: getPartitions multiplexer newS = getPartitions multiplexer s).
    {
      apply getPartitionsEqSCE; try(assumption). unfold consistency1 in *; intuition.
    }

    assert(currentPartitionInPartitionsList newS).
    { (* BEGIN currentPartitionInPartitionsList newS *)
      assert(Hcons0: currentPartitionInPartitionsList s) by (unfold consistency1 in *; intuition).
      unfold currentPartitionInPartitionsList. rewrite HcurrPartEq. rewrite HgetPartsEq. assumption.
      (* END currentPartitionInPartitionsList *)
    }

    assert(wellFormedShadowCutIfBlockEntry newS).
    { (* BEGIN wellFormedShadowCutIfBlockEntry newS *)
      assert(Hcons0: wellFormedShadowCutIfBlockEntry s) by (unfold consistency1 in *; intuition).
      intros block HblockIsBE.
      assert(HblockIsBEs: isBE block s).
      {
        unfold isBE in HblockIsBE. simpl in HblockIsBE.
        destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) block) eqn:HbeqNewSceBlock;
            try(exfalso; congruence).
        rewrite <-beqAddrFalse in HbeqNewSceBlock. rewrite removeDupIdentity in HblockIsBE; intuition.
      }
      specialize(Hcons0 block HblockIsBEs). destruct Hcons0 as [sce (HsceIsSCEBis & Hsce)]. exists sce.
      split; try(assumption). unfold isSCE. simpl.
      destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) sce) eqn:HbeqNewSceSce; try(trivial).
      rewrite <-beqAddrFalse in HbeqNewSceSce. rewrite removeDupIdentity; intuition.
      (* END wellFormedShadowCutIfBlockEntry *)
    }

    assert(BlocksRangeFromKernelStartIsBE newS).
    { (* BEGIN BlocksRangeFromKernelStartIsBE newS *)
      assert(Hcons0: BlocksRangeFromKernelStartIsBE s) by (unfold consistency1 in *; intuition).
      intros kernel idx HkernIsKS HidxBounded.
      assert(HkernIsKSs: isKS kernel s).
      {
        unfold isKS in HkernIsKS. simpl in HkernIsKS.
        destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) kernel) eqn:HbeqNewSceKern;
            try(exfalso; congruence). rewrite <-beqAddrFalse in HbeqNewSceKern.
        rewrite removeDupIdentity in HkernIsKS; intuition.
      }
      specialize(Hcons0 kernel idx HkernIsKSs HidxBounded). unfold isBE in *. simpl.
      destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) (CPaddr (kernel + idx))) eqn:HbeqNewSceKernIdx.
      {
        rewrite <-beqAddrTrue in HbeqNewSceKernIdx. rewrite HbeqNewSceKernIdx in *.
        rewrite HlookupNewSce in Hcons0. congruence.
      }
      rewrite <-beqAddrFalse in HbeqNewSceKernIdx. rewrite removeDupIdentity; intuition.
      (* END BlocksRangeFromKernelStartIsBE *)
    }

    assert(KernelStructureStartFromBlockEntryAddrIsKS newS).
    { (* BEGIN KernelStructureStartFromBlockEntryAddrIsKS newS *)
      assert(Hcons0: KernelStructureStartFromBlockEntryAddrIsKS s) by (unfold consistency1 in *; intuition).
      intros block idx HblockIsBE Hblockidx.
      assert(HlookupEq: lookup block (memory newS) beqAddr = lookup block (memory s) beqAddr).
      {
        unfold isBE in HblockIsBE. simpl. simpl in HblockIsBE.
        destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) block) eqn:HbeqNewSceBlock;
            try(exfalso; congruence). rewrite <-beqAddrFalse in HbeqNewSceBlock.
        rewrite removeDupIdentity; intuition.
      }
      unfold isBE in HblockIsBE. unfold bentryBlockIndex in Hblockidx. rewrite HlookupEq in *.
      specialize(Hcons0 block idx HblockIsBE Hblockidx). unfold isKS in *. simpl.
      destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) (CPaddr (block - idx))) eqn:HbeqNewSceBlockMIdx.
      {
        rewrite <-beqAddrTrue in HbeqNewSceBlockMIdx. rewrite HbeqNewSceBlockMIdx in *.
        rewrite HlookupNewSce in Hcons0; congruence.
      }
      rewrite <-beqAddrFalse in HbeqNewSceBlockMIdx. rewrite removeDupIdentity; intuition.
      (* END KernelStructureStartFromBlockEntryAddrIsKS *)
    }

    assert(sh1InChildLocationIsBE newS).
    { (* BEGIN sh1InChildLocationIsBE newS *)
      assert(Hcons0: sh1InChildLocationIsBE s) by (unfold consistency1 in *; intuition).
      intros sh1entryaddr sh1entry HlookupSh1 HbeqChildLocNull.
      assert(HlookupSh1s: lookup sh1entryaddr (memory s) beqAddr = Some (SHE sh1entry)).
      {
        simpl in HlookupSh1. destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) sh1entryaddr)
            eqn:HbeqNewSceSh1; try(exfalso; congruence). rewrite <-beqAddrFalse in HbeqNewSceSh1.
        rewrite removeDupIdentity in HlookupSh1; intuition.
      }
      specialize(Hcons0 sh1entryaddr sh1entry HlookupSh1s HbeqChildLocNull).
      unfold isBE in *. simpl.
      destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) (inChildLocation sh1entry)) eqn:HbeqNewSceChildLoc.
      {
        rewrite <-beqAddrTrue in HbeqNewSceChildLoc. rewrite HbeqNewSceChildLoc in *.
        rewrite HlookupNewSce in Hcons0; congruence.
      }
      rewrite <-beqAddrFalse in HbeqNewSceChildLoc. rewrite removeDupIdentity; intuition.
      (* END sh1InChildLocationIsBE *)
    }

    assert(StructurePointerIsKS newS).
    { (* BEGIN StructurePointerIsKS newS *)
      assert(Hcons0: StructurePointerIsKS s) by (unfold consistency1 in *; intuition).
      intros entryaddr entry HlookupEntry HbeqStructNull.
      assert(HlookupEntrys: lookup entryaddr (memory s) beqAddr = Some (PDT entry)).
      {
        simpl in HlookupEntry. destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) entryaddr)
            eqn:HbeqNewSceEntry; try(exfalso; congruence). rewrite <-beqAddrFalse in HbeqNewSceEntry.
        rewrite removeDupIdentity in HlookupEntry; intuition.
      }
      specialize(Hcons0 entryaddr entry HlookupEntrys HbeqStructNull). unfold isKS in *. simpl.
      destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) (structure entry)) eqn:HbeqNewSceStruct.
      {
        rewrite <-beqAddrTrue in HbeqNewSceStruct. rewrite HbeqNewSceStruct in *.
        rewrite HlookupNewSce in Hcons0. congruence.
      }
      rewrite <-beqAddrFalse in HbeqNewSceStruct. rewrite removeDupIdentity; intuition.
      (* END StructurePointerIsKS *)
    }

    assert(NextKSIsKS newS).
    { (* BEGIN NextKSIsKS newS *)
      assert(Hcons0: NextKSIsKS s) by (unfold consistency1 in *; intuition).
      intros kernel nextKSaddr nextKS HkernIsKS HnextAddr HnextKS HbeqNextNull.
      assert(HlookupEq: lookup kernel (memory newS) beqAddr = lookup kernel (memory s) beqAddr).
      {
        unfold isKS in HkernIsKS. simpl in HkernIsKS. simpl.
        destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) kernel) eqn:HbeqNewSceKern;
            try(exfalso; congruence). rewrite <-beqAddrFalse in HbeqNewSceKern.
        rewrite removeDupIdentity; intuition.
      }
      unfold isKS in HkernIsKS. unfold nextKSAddr in HnextAddr. rewrite HlookupEq in *.
      assert(HnextKSs: nextKSentry nextKSaddr nextKS s).
      {
        unfold nextKSentry in *. simpl in HnextKS.
        destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) nextKSaddr) eqn:HbeqNewSceNextAddr;
            try(exfalso; congruence). rewrite <-beqAddrFalse in HbeqNewSceNextAddr.
        rewrite removeDupIdentity in HnextKS; intuition.
      }
      specialize(Hcons0 kernel nextKSaddr nextKS HkernIsKS HnextAddr HnextKSs HbeqNextNull). unfold isKS in *.
      simpl. destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) nextKS) eqn:HbeqNewSceNextKS.
      {
        rewrite <-beqAddrTrue in HbeqNewSceNextKS. rewrite HbeqNewSceNextKS in *. rewrite HlookupNewSce in Hcons0.
        congruence.
      }
      rewrite <-beqAddrFalse in HbeqNewSceNextKS. rewrite removeDupIdentity; intuition.
      (* END NextKSIsKS *)
    }

    assert(NextKSOffsetIsPADDR newS).
    { (* BEGIN NextKSOffsetIsPADDR newS *)
      assert(Hcons0: NextKSOffsetIsPADDR s) by (unfold consistency1 in *; intuition).
      intros kernel nextAddr HkernIsKS HnextAddr.
      assert(HlookupEq: lookup kernel (memory newS) beqAddr = lookup kernel (memory s) beqAddr).
      {
        unfold isKS in HkernIsKS. simpl in HkernIsKS. simpl.
        destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) kernel) eqn:HbeqNewSceKern;
            try(exfalso; congruence). rewrite <-beqAddrFalse in HbeqNewSceKern.
        rewrite removeDupIdentity; intuition.
      }
      unfold isKS in HkernIsKS. unfold nextKSAddr in HnextAddr. rewrite HlookupEq in *.
      specialize(Hcons0 kernel nextAddr HkernIsKS HnextAddr). destruct Hcons0 as (HnextIsPADDR & HbeqNextNull).
      split; try(assumption). unfold isPADDR in *. simpl.
      destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) nextAddr) eqn:HbeqNewSceNextAddr.
      {
        rewrite <-beqAddrTrue in HbeqNewSceNextAddr. rewrite HbeqNewSceNextAddr in *.
        rewrite HlookupNewSce in HnextIsPADDR. congruence.
      }
      rewrite <-beqAddrFalse in HbeqNewSceNextAddr. rewrite removeDupIdentity; intuition.
      (* END NextKSOffsetIsPADDR *)
    }

    assert(NoDupInFreeSlotsList newS).
    { (* BEGIN NoDupInFreeSlotsList newS *)
      assert(Hcons0: NoDupInFreeSlotsList s) by (unfold consistency1 in *; intuition).
      intros pd pdentryPd HlookupPd.
      assert(HlookupPds: lookup pd (memory s) beqAddr = Some (PDT pdentryPd)).
      {
        simpl in HlookupPd.
        destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) pd) eqn:HbeqNewScePd; try(exfalso; congruence).
        rewrite <-beqAddrFalse in HbeqNewScePd. rewrite removeDupIdentity in HlookupPd; intuition.
      }
      specialize(Hcons0 pd pdentryPd HlookupPds).
      destruct Hcons0 as [slotsList (HslotsList & HwellFormed & HnoDup)]. exists slotsList.
      split; try(split; assumption). subst slotsList. unfold getFreeSlotsList in *. rewrite HlookupPd.
      rewrite HlookupPds. destruct (beqAddr (firstfreeslot pdentryPd) nullAddr) eqn:HbeqFirstNull;
        try(reflexivity). apply eq_sym. apply getFreeSlotsListRecEqSCE.
      - intro Hcontra. rewrite <-Hcontra in *.
        assert(HfirstFree: FirstFreeSlotPointerIsBEAndFreeSlot s) by (unfold consistency1 in *; intuition).
        assert(HfirstIsBE: isBE (firstfreeslot pdentryPd) s).
        {
          specialize(HfirstFree pd pdentryPd). apply HfirstFree. assumption. rewrite beqAddrFalse.
          assumption.
        }
        unfold isBE in HfirstIsBE. rewrite HlookupNewSce in HfirstIsBE. congruence.
      - unfold isBE. rewrite HlookupNewSce. intuition.
      - unfold isPADDR. rewrite HlookupNewSce. intuition.
      (* END NoDupInFreeSlotsList *)
    }

    assert(freeSlotsListIsFreeSlot newS).
    { (* BEGIN freeSlotsListIsFreeSlot newS *)
      assert(Hcons0: freeSlotsListIsFreeSlot s) by (unfold consistency1 in *; intuition).
      intros pd freeslot optSlotsList slotsList HpdIsPDT HoptSlotsList HslotsList HbeqFreeNull.
      assert(HlookupPdEq: lookup pd (memory newS) beqAddr = lookup pd (memory s) beqAddr).
      {
        unfold isPDT in HpdIsPDT. simpl in HpdIsPDT. simpl.
        destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) pd) eqn:HbeqNewScePd; try(exfalso; congruence).
        rewrite <-beqAddrFalse in HbeqNewScePd. rewrite removeDupIdentity; intuition.
      }
      destruct HoptSlotsList as (HoptSlotsList & HwellFormed).
      assert(HoptSlotsLists: optSlotsList = getFreeSlotsList pd s
                              /\ wellFormedFreeSlotsList optSlotsList <> False).
      {
        split; try(assumption). subst optSlotsList. unfold getFreeSlotsList. rewrite HlookupPdEq.
        unfold isPDT in HpdIsPDT. destruct (lookup pd (memory s) beqAddr) eqn:HlookupPd; try(reflexivity).
        destruct v; try(reflexivity).
        destruct (beqAddr (firstfreeslot p) nullAddr) eqn:HbeqFirstNull; try(reflexivity).
        rewrite <-beqAddrFalse in HbeqFirstNull. apply getFreeSlotsListRecEqSCE.
        - intro Hcontra. rewrite <-Hcontra in *.
          assert(HfirstFree: FirstFreeSlotPointerIsBEAndFreeSlot s) by (unfold consistency1 in *; intuition).
          assert(HfirstIsBE: isBE (firstfreeslot p) s).
          {
            specialize(HfirstFree pd p). apply HfirstFree. assumption. assumption.
          }
          unfold isBE in HfirstIsBE. rewrite HlookupNewSce in HfirstIsBE. congruence.
        - unfold isBE. rewrite HlookupNewSce. intuition.
        - unfold isPADDR. rewrite HlookupNewSce. intuition.
      }
      unfold isPDT in HpdIsPDT. rewrite HlookupPdEq in HpdIsPDT.
      specialize(Hcons0 pd freeslot optSlotsList slotsList HpdIsPDT HoptSlotsLists HslotsList HbeqFreeNull).
      unfold isFreeSlot in *. simpl.
      destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) freeslot) eqn:HbeqNewSceFree.
      {
        rewrite <-beqAddrTrue in HbeqNewSceFree. rewrite HbeqNewSceFree in *. rewrite HlookupNewSce in Hcons0.
        congruence.
      }
      rewrite <-beqAddrFalse in HbeqNewSceFree. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      destruct (lookup freeslot (memory s) beqAddr) eqn:HlookupFree; try(congruence). destruct v; try(congruence).
      destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) (CPaddr (freeslot + sh1offset)))
          eqn:HbeqNewSceFreeSh1.
      {
        rewrite <-beqAddrTrue in HbeqNewSceFreeSh1. rewrite HbeqNewSceFreeSh1 in *.
        rewrite HlookupNewSce in Hcons0. congruence.
      }
      rewrite <-beqAddrFalse in HbeqNewSceFreeSh1. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      destruct (lookup (CPaddr (freeslot + sh1offset)) (memory s) beqAddr); try(congruence).
      destruct v; try(congruence).
      destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) (CPaddr (freeslot + scoffset)))
          eqn:HbeqNewSceFreeSce.
      {
        rewrite <-beqAddrTrue in HbeqNewSceFreeSce. rewrite <-HbeqNewSceFreeSce in *. exfalso.
        destruct (beqAddr idNewSubblock freeslot) eqn:HbeqNewFree.
        - rewrite <-beqAddrTrue in HbeqNewFree. subst idNewSubblock. rewrite HlookupNews in HlookupFree.
          injection HlookupFree as HbentriesEq. subst b.
          destruct (lookup (CPaddr (freeslot + scoffset)) (memory s) beqAddr) eqn:HlookupFreeSce;
              try(congruence).
          destruct v; try(congruence). destruct Hcons0 as (_ & _ & _ & _ & _ & Hcontra & _).
          rewrite H15 in Hcontra. unfold CBlockEntry in Hcontra.
          assert(blockindex bentry5 < kernelStructureEntriesNb) by (apply Hidx).
          destruct (Compare_dec.lt_dec (blockindex bentry5) kernelStructureEntriesNb); try(lia).
          simpl in Hcontra. rewrite H17 in Hcontra. unfold CBlockEntry in Hcontra.
          assert(blockindex bentry4 < kernelStructureEntriesNb) by (apply Hidx).
          destruct (Compare_dec.lt_dec (blockindex bentry4) kernelStructureEntriesNb); try(lia).
          simpl in Hcontra. rewrite H19 in Hcontra. unfold CBlockEntry in Hcontra.
          assert(blockindex bentry3 < kernelStructureEntriesNb) by (apply Hidx).
          destruct (Compare_dec.lt_dec (blockindex bentry3) kernelStructureEntriesNb); try(lia).
          simpl in Hcontra. rewrite H21 in Hcontra. unfold CBlockEntry in Hcontra.
          assert(blockindex bentry2 < kernelStructureEntriesNb) by (apply Hidx).
          destruct (Compare_dec.lt_dec (blockindex bentry2) kernelStructureEntriesNb); try(lia).
          simpl in Hcontra. congruence.
        - rewrite <-beqAddrFalse in HbeqNewFree. unfold CPaddr in HbeqNewSceFreeSce.
          destruct (Compare_dec.le_dec (idNewSubblock + scoffset) maxAddr) eqn:HleNewSceMax.
          + destruct (Compare_dec.le_dec (freeslot + scoffset) maxAddr).
            * injection HbeqNewSceFreeSce as HsceEq. contradict HbeqNewFree.
              destruct idNewSubblock. destruct freeslot.  simpl in HsceEq.
              assert(p = p0) by lia. subst p0. f_equal. apply proof_irrelevance.
            * assert(HbeqNewSceNull: CPaddr (idNewSubblock + scoffset) = nullAddr).
              {
                unfold nullAddr. injection HbeqNewSceFreeSce as HbeqNewSceNull. rewrite HbeqNewSceNull.
                reflexivity.
              }
              assert(Hnull: nullAddrExists s) by (unfold consistency1 in *; intuition).
              unfold nullAddrExists in Hnull. unfold isPADDR in Hnull. rewrite HbeqNewSceNull in *.
              rewrite HlookupNewSce in Hnull. congruence.
          + assert(HbeqNewScenull: CPaddr (idNewSubblock + scoffset) = nullAddr).
            {
              unfold nullAddr. unfold CPaddr. rewrite HleNewSceMax.
              destruct (Compare_dec.le_dec 0 maxAddr); try(lia). f_equal. apply proof_irrelevance.
            }
            assert(Hnull: nullAddrExists s) by (unfold consistency1 in *; intuition).
            unfold nullAddrExists in Hnull. unfold isPADDR in Hnull. rewrite HbeqNewScenull in *.
            rewrite HlookupNewSce in Hnull. congruence.
      }
      rewrite <-beqAddrFalse in HbeqNewSceFreeSce. rewrite removeDupIdentity; intuition.
      (* END freeSlotsListIsFreeSlot *)
    }

    assert(DisjointFreeSlotsLists newS).
    { (* BEGIN DisjointFreeSlotsLists newS *)
      assert(Hcons0: DisjointFreeSlotsLists s) by (unfold consistency1 in *; intuition).
      intros pd1 pd2 Hpd1IsPDT Hpd2IsPDT HbeqPd1Pd2.
      assert(HlookupPd1Eq: lookup pd1 (memory newS) beqAddr = lookup pd1 (memory s) beqAddr).
      {
        unfold isPDT in Hpd1IsPDT. simpl in Hpd1IsPDT. simpl.
        destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) pd1) eqn:HbeqNewScePd; try(exfalso; congruence).
        rewrite <-beqAddrFalse in HbeqNewScePd. rewrite removeDupIdentity; intuition.
      }
      assert(HlookupPd2Eq: lookup pd2 (memory newS) beqAddr = lookup pd2 (memory s) beqAddr).
      {
        unfold isPDT in Hpd2IsPDT. simpl in Hpd2IsPDT. simpl.
        destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) pd2) eqn:HbeqNewScePd; try(exfalso; congruence).
        rewrite <-beqAddrFalse in HbeqNewScePd. rewrite removeDupIdentity; intuition.
      }
      unfold isPDT in *. rewrite HlookupPd1Eq in Hpd1IsPDT. rewrite HlookupPd2Eq in Hpd2IsPDT.
      specialize(Hcons0 pd1 pd2 Hpd1IsPDT Hpd2IsPDT HbeqPd1Pd2).
      destruct Hcons0 as [list1 [list2 (Hlist1 & HwellFormed1 & Hlist2 & HwellFormed2 & Hdisjoint)]].
      exists list1. exists list2. split.
      - subst list1. apply eq_sym. unfold getFreeSlotsList. rewrite HlookupPd1Eq.
        destruct (lookup pd1 (memory s) beqAddr) eqn:HlookupPd1; try(reflexivity). destruct v; try(reflexivity).
        destruct (beqAddr (firstfreeslot p) nullAddr) eqn:HbeqFirstNull; try(reflexivity).
        rewrite <-beqAddrFalse in HbeqFirstNull. apply getFreeSlotsListRecEqSCE.
        + intro Hcontra. rewrite <-Hcontra in *.
          assert(HfirstFree: FirstFreeSlotPointerIsBEAndFreeSlot s) by (unfold consistency1 in *; intuition).
          assert(HfirstIsBE: isBE (firstfreeslot p) s).
          {
            specialize(HfirstFree pd1 p). apply HfirstFree. assumption. assumption.
          }
          unfold isBE in HfirstIsBE. rewrite HlookupNewSce in HfirstIsBE. congruence.
        + unfold isBE. rewrite HlookupNewSce. intuition.
        + unfold isPADDR. rewrite HlookupNewSce. intuition.
      - split. assumption. split; try(split; assumption). subst list2. apply eq_sym. unfold getFreeSlotsList.
        rewrite HlookupPd2Eq. destruct (lookup pd2 (memory s) beqAddr) eqn:HlookupPd2; try(reflexivity).
        destruct v; try(reflexivity).
        destruct (beqAddr (firstfreeslot p) nullAddr) eqn:HbeqFirstNull; try(reflexivity).
        rewrite <-beqAddrFalse in HbeqFirstNull. apply getFreeSlotsListRecEqSCE.
        + intro Hcontra. rewrite <-Hcontra in *.
          assert(HfirstFree: FirstFreeSlotPointerIsBEAndFreeSlot s) by (unfold consistency1 in *; intuition).
          assert(HfirstIsBE: isBE (firstfreeslot p) s).
          {
            specialize(HfirstFree pd2 p). apply HfirstFree. assumption. assumption.
          }
          unfold isBE in HfirstIsBE. rewrite HlookupNewSce in HfirstIsBE. congruence.
        + unfold isBE. rewrite HlookupNewSce. intuition.
        + unfold isPADDR. rewrite HlookupNewSce. intuition.
      (* END DisjointFreeSlotsLists *)
    }

    assert(inclFreeSlotsBlockEntries newS).
    { (* BEGIN inclFreeSlotsBlockEntries newS *)
      assert(Hcons0: inclFreeSlotsBlockEntries s) by (unfold consistency1 in *; intuition).
      intros pd HpdIsPDT.
      assert(HlookupPdEq: lookup pd (memory newS) beqAddr = lookup pd (memory s) beqAddr).
      {
        unfold isPDT in HpdIsPDT. simpl in HpdIsPDT. simpl.
        destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) pd) eqn:HbeqNewScePd; try(exfalso; congruence).
        rewrite <-beqAddrFalse in HbeqNewScePd. rewrite removeDupIdentity; intuition.
      }
      unfold isPDT in HpdIsPDT. rewrite HlookupPdEq in HpdIsPDT. specialize(Hcons0 pd HpdIsPDT).
      assert(HgetFreeEq: getFreeSlotsList pd newS = getFreeSlotsList pd s).
      {
        unfold getFreeSlotsList. rewrite HlookupPdEq.
        destruct (lookup pd (memory s) beqAddr) eqn:HlookupPd; try(reflexivity). destruct v; try(reflexivity).
        destruct (beqAddr (firstfreeslot p) nullAddr) eqn:HbeqFirstNull; try(reflexivity).
        rewrite <-beqAddrFalse in HbeqFirstNull. apply getFreeSlotsListRecEqSCE.
        + intro Hcontra. rewrite <-Hcontra in *.
          assert(HfirstFree: FirstFreeSlotPointerIsBEAndFreeSlot s) by (unfold consistency1 in *; intuition).
          assert(HfirstIsBE: isBE (firstfreeslot p) s).
          {
            specialize(HfirstFree pd p). apply HfirstFree. assumption. assumption.
          }
          unfold isBE in HfirstIsBE. rewrite HlookupNewSce in HfirstIsBE. congruence.
        + unfold isBE. rewrite HlookupNewSce. intuition.
        + unfold isPADDR. rewrite HlookupNewSce. intuition.
      }
      assert(HgetKSEq: getKSEntries pd newS = getKSEntries pd s).
      {
        destruct (lookup pd (memory s) beqAddr) eqn:HlookupPd; try(exfalso; congruence).
        destruct v; try(exfalso; congruence). apply getKSEntriesEqSCE with p; assumption.
      }
      rewrite HgetFreeEq. rewrite HgetKSEq. assumption.
      (* END inclFreeSlotsBlockEntries *)
    }

    assert(DisjointKSEntries newS).
    { (* BEGIN DisjointKSEntries newS *)
      assert(Hcons0: DisjointKSEntries s) by (unfold consistency1 in *; intuition).
      intros pd1 pd2 Hpd1IsPDT Hpd2IsPDT HbeqPd1Pd2.
      assert(HlookupPd1Eq: lookup pd1 (memory newS) beqAddr = lookup pd1 (memory s) beqAddr).
      {
        unfold isPDT in Hpd1IsPDT. simpl in Hpd1IsPDT. simpl.
        destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) pd1) eqn:HbeqNewScePd; try(exfalso; congruence).
        rewrite <-beqAddrFalse in HbeqNewScePd. rewrite removeDupIdentity; intuition.
      }
      assert(HlookupPd2Eq: lookup pd2 (memory newS) beqAddr = lookup pd2 (memory s) beqAddr).
      {
        unfold isPDT in Hpd2IsPDT. simpl in Hpd2IsPDT. simpl.
        destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) pd2) eqn:HbeqNewScePd; try(exfalso; congruence).
        rewrite <-beqAddrFalse in HbeqNewScePd. rewrite removeDupIdentity; intuition.
      }
      unfold isPDT in *. rewrite HlookupPd1Eq in Hpd1IsPDT. rewrite HlookupPd2Eq in Hpd2IsPDT.
      specialize(Hcons0 pd1 pd2 Hpd1IsPDT Hpd2IsPDT HbeqPd1Pd2).
      destruct Hcons0 as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. exists list1. exists list2. split.
      - subst list1. apply eq_sym.
        destruct (lookup pd1 (memory s) beqAddr) eqn:HlookupPd; try(exfalso; congruence).
        destruct v; try(exfalso; congruence). apply getKSEntriesEqSCE with p; assumption.
      - split; try(assumption). subst list2. apply eq_sym.
        destruct (lookup pd2 (memory s) beqAddr) eqn:HlookupPd; try(exfalso; congruence).
        destruct v; try(exfalso; congruence). apply getKSEntriesEqSCE with p; assumption.
      (* END DisjointKSEntries *)
    }

    assert(noDupPartitionTree newS).
    { (* BEGIN noDupPartitionTree newS *)
      assert(Hcons0: noDupPartitionTree s) by (unfold consistency1 in *; intuition).
      unfold noDupPartitionTree in *. rewrite HgetPartsEq. assumption.
      (* END noDupPartitionTree *)
    }

    assert(isParent newS).
    { (* BEGIN isParent newS *)
      assert(Hcons0: isParent s) by (unfold consistency1 in *; intuition).
      intros partition pdparent HparentIsPart HpartIsChild. rewrite HgetPartsEq in HparentIsPart.
      assert(HgetChildrenEq: getChildren pdparent newS = getChildren pdparent s).
      {
        apply getChildrenEqSCE; try(assumption). apply partitionsArePDT; try(assumption).
        unfold consistency1 in *; intuition.
      }
      rewrite HgetChildrenEq in HpartIsChild. specialize(Hcons0 partition pdparent HparentIsPart HpartIsChild).
      unfold pdentryParent in *. simpl.
      destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) partition) eqn:HbeqNewScePart.
      {
        rewrite <-beqAddrTrue in HbeqNewScePart. rewrite HbeqNewScePart in *. rewrite HlookupNewSce in Hcons0.
        congruence.
      }
      rewrite <-beqAddrFalse in HbeqNewScePart. rewrite removeDupIdentity; intuition.
      (* END isParent *)
    }

    assert(isChild newS).
    { (* BEGIN isChild newS *)
      assert(Hcons0: isChild s) by (unfold consistency1 in *; intuition).
      intros partition pdparent HpartIsPart HparentIsParent. rewrite HgetPartsEq in HpartIsPart.
      assert(HparentIsParents: pdentryParent partition pdparent s).
      {
        unfold pdentryParent in *. simpl in HparentIsParent.
        destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) partition) eqn:HbeqNewScePart;
          try(exfalso; congruence). rewrite <-beqAddrFalse in HbeqNewScePart.
        rewrite removeDupIdentity in HparentIsParent; intuition.
      }
      specialize(Hcons0 partition pdparent HpartIsPart HparentIsParents).
      assert(HgetChildrenEq: getChildren pdparent newS = getChildren pdparent s).
      {
        apply getChildrenEqSCE; try(assumption). unfold pdentryParent in HparentIsParents.
        destruct (lookup partition (memory s) beqAddr) eqn:HlookupPart; try(exfalso; congruence).
        destruct v; try(exfalso; congruence).
        assert(HparentOfPart: parentOfPartitionIsPartition s) by (unfold consistency1 in *; intuition).
        specialize(HparentOfPart partition p HlookupPart).
        destruct HparentOfPart as (HparentIsPart & HparentOfRoot & _).
        destruct (beqAddr partition constantRootPartM) eqn:HbeqPartRoot.
        {
          rewrite <-beqAddrTrue in HbeqPartRoot. specialize(HparentOfRoot HbeqPartRoot).
          rewrite HparentOfRoot in *. rewrite HparentIsParents in *.
          assert(Hnull: nullAddrExists s) by (unfold consistency1 in *; intuition).
          unfold nullAddrExists in Hnull. unfold isPADDR in Hnull. unfold getChildren in Hcons0.
          destruct (lookup nullAddr (memory s) beqAddr); try(exfalso; congruence).
          destruct v; try(exfalso; congruence). simpl in Hcons0. exfalso; congruence.
        }
        rewrite <-beqAddrFalse in HbeqPartRoot. specialize(HparentIsPart HbeqPartRoot).
        destruct HparentIsPart as ([parentEntry HlookupParent] & _). unfold isPDT. rewrite HparentIsParents.
        rewrite HlookupParent. trivial.
      }
      rewrite HgetChildrenEq. assumption.
      (* END isChild *)
    }

    assert(noDupKSEntriesList newS).
    { (* BEGIN noDupKSEntriesList newS *)
      assert(Hcons0: noDupKSEntriesList s) by (unfold consistency1 in *; intuition).
      intros partition HpartIsPDT.
      assert(HpartIsPDTs: isPDT partition s).
      {
        unfold isPDT in *. simpl in HpartIsPDT.
        destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) partition) eqn:HbeqNewScePart;
            try(exfalso; congruence).
        rewrite <-beqAddrFalse in HbeqNewScePart. rewrite removeDupIdentity in HpartIsPDT; intuition.
      }
      specialize(Hcons0 partition HpartIsPDTs).
      assert(HgetKSEq: getKSEntries partition newS = getKSEntries partition s).
      {
        unfold isPDT in HpartIsPDTs.
        destruct (lookup partition (memory s) beqAddr) eqn:HlookupPart; try(exfalso; congruence).
        destruct v; try(exfalso; congruence). apply getKSEntriesEqSCE with p; assumption.
      }
      rewrite HgetKSEq. assumption.
      (* END noDupKSEntriesList *)
    }

    assert(noDupMappedBlocksList newS).
    { (* BEGIN noDupMappedBlocksList newS *)
      assert(Hcons0: noDupMappedBlocksList s) by (unfold consistency1 in *; intuition).
      intros partition HpartIsPDT.
      assert(HpartIsPDTs: isPDT partition s).
      {
        unfold isPDT in *. simpl in HpartIsPDT.
        destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) partition) eqn:HbeqNewScePart;
            try(exfalso; congruence).
        rewrite <-beqAddrFalse in HbeqNewScePart. rewrite removeDupIdentity in HpartIsPDT; intuition.
      }
      specialize(Hcons0 partition HpartIsPDTs).
      assert(HgetMappedBlocksEq: getMappedBlocks partition newS = getMappedBlocks partition s).
      {
        apply getMappedBlocksEqSCE; assumption.
      }
      rewrite HgetMappedBlocksEq. assumption.
      (* END noDupMappedBlocksList *)
    }

    assert(wellFormedBlock newS).
    { (* BEGIN wellFormedBlock newS *)
      assert(Hcons0: wellFormedBlock s) by (unfold consistency1 in *; intuition).
      intros block startaddr endaddr HPFlag Hstart Hend.
      assert(HlookupEq: lookup block (memory newS) beqAddr = lookup block (memory s) beqAddr).
      {
        unfold bentryPFlag in HPFlag. simpl. simpl in HPFlag.
        destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) block) eqn:HbeqNewSceBlock;
            try(exfalso; congruence). rewrite <-beqAddrFalse in HbeqNewSceBlock.
        rewrite removeDupIdentity; intuition.
      }
      unfold bentryPFlag in HPFlag. unfold bentryStartAddr in Hstart. unfold bentryEndAddr in Hend.
      rewrite HlookupEq in *. specialize(Hcons0 block startaddr endaddr HPFlag Hstart Hend).
      assumption.
      (* END wellFormedBlock *)
    }

    assert(parentOfPartitionIsPartition newS).
    { (* BEGIN parentOfPartitionIsPartition newS *)
      assert(Hcons0: parentOfPartitionIsPartition s) by (unfold consistency1 in *; intuition).
      intros partition entry HlookupPart.
      assert(HlookupParts: lookup partition (memory s) beqAddr = Some (PDT entry)).
      {
        simpl in HlookupPart. destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) partition) eqn:HbeqNewScePart.
        {
          rewrite <-beqAddrTrue in HbeqNewScePart. rewrite HbeqNewScePart in *. exfalso; congruence.
        }
        rewrite <-beqAddrFalse in HbeqNewScePart. rewrite removeDupIdentity in HlookupPart; intuition.
      }
      specialize(Hcons0 partition entry HlookupParts).
      destruct Hcons0 as (HparentIsPart & HparentOfRoot & HbeqParentPart). split.
      - intro HbeqPartRoot. specialize(HparentIsPart HbeqPartRoot).
        destruct HparentIsPart as ([parentEntry HlookupParent] & HparentIsPart). rewrite HgetPartsEq.
        split; try(assumption). exists parentEntry. simpl.
        destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) (parent entry)) eqn:HbeqNewSceParent.
        {
          rewrite <-beqAddrTrue in HbeqNewSceParent. rewrite HbeqNewSceParent in *. congruence.
        }
        rewrite <-beqAddrFalse in HbeqNewSceParent. rewrite removeDupIdentity; intuition.
      - split; assumption.
      (* END parentOfPartitionIsPartition *)
    }

    assert(NbFreeSlotsISNbFreeSlotsInList newS).
    { (* BEGIN NbFreeSlotsISNbFreeSlotsInList newS *)
      assert(Hcons0: NbFreeSlotsISNbFreeSlotsInList s) by (unfold consistency1 in *; intuition).
      intros partition nbfreeslots HpartIsPDT HnbFree.
      assert(HlookupEq: lookup partition (memory newS) beqAddr = lookup partition (memory s) beqAddr).
      {
        unfold isPDT in HpartIsPDT. simpl in HpartIsPDT. simpl.
        destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) partition) eqn:HbeqNewScePart;
            try(exfalso; congruence).
        rewrite <-beqAddrFalse in HbeqNewScePart. rewrite removeDupIdentity; intuition.
      }
      unfold isPDT in HpartIsPDT. unfold pdentryNbFreeSlots in HnbFree. rewrite HlookupEq in *.
      specialize(Hcons0 partition nbfreeslots HpartIsPDT HnbFree).
      destruct Hcons0 as [slotsList (HslotsList & HwellFormed & HnbFreeLen)]. exists slotsList.
      split; try(split; assumption). subst slotsList. apply eq_sym. unfold getFreeSlotsList. rewrite HlookupEq.
      destruct (lookup partition (memory s) beqAddr) eqn:HlookupPart; try(reflexivity).
      destruct v; try(reflexivity).
      destruct (beqAddr (firstfreeslot p) nullAddr) eqn:HbeqFirstNull; try(reflexivity).
      rewrite <-beqAddrFalse in HbeqFirstNull. apply getFreeSlotsListRecEqSCE.
      - intro Hcontra. rewrite <-Hcontra in *.
        assert(HfirstFree: FirstFreeSlotPointerIsBEAndFreeSlot s) by (unfold consistency1 in *; intuition).
        assert(HfirstIsBE: isBE (firstfreeslot p) s).
        {
          specialize(HfirstFree partition p). apply HfirstFree. assumption. assumption.
        }
        unfold isBE in HfirstIsBE. rewrite HlookupNewSce in HfirstIsBE. congruence.
      - unfold isBE. rewrite HlookupNewSce. intuition.
      - unfold isPADDR. rewrite HlookupNewSce. intuition.
      (* END NbFreeSlotsISNbFreeSlotsInList *)
    }

    assert(maxNbPrepareIsMaxNbKernels newS).
    { (* BEGIN maxNbPrepareIsMaxNbKernels newS *)
      assert(Hcons0: maxNbPrepareIsMaxNbKernels s) by (unfold consistency1 in *; intuition).
      intros partition kernList HkernList.
      assert(HkernLists: isListOfKernels kernList partition s).
      {
        revert HkernList. apply isListOfKernelsEqSCE.
      }
      specialize(Hcons0 partition kernList HkernLists). assumption.
      (* END maxNbPrepareIsMaxNbKernels *)
    }

    assert(blockInChildHasAtLeastEquivalentBlockInParent newS).
    { (* BEGIN blockInChildHasAtLeastEquivalentBlockInParent newS *)
      assert(Hcons0: blockInChildHasAtLeastEquivalentBlockInParent s) by (unfold consistency1 in *; intuition).
      intros pdparent child block startChild endChild HparentIsPart HchildIsChild HblockMappedChild Hstart Hend
        HPFlag. rewrite HgetPartsEq in HparentIsPart.
      assert(HgetChildrenEq: getChildren pdparent newS = getChildren pdparent s).
      {
        apply getChildrenEqSCE; try(assumption). apply partitionsArePDT; try(assumption).
        unfold consistency1 in *; intuition.
      }
      rewrite HgetChildrenEq in HchildIsChild.
      assert(HgetMappedBlocksChildEq: getMappedBlocks child newS = getMappedBlocks child s).
      {
        apply getMappedBlocksEqSCE; try(assumption). apply childrenArePDT with pdparent.
        unfold consistency1 in *; intuition. assumption.
      }
      assert(HlookupEq: lookup block (memory newS) beqAddr = lookup block (memory s) beqAddr).
      {
        unfold bentryPFlag in HPFlag. simpl. simpl in HPFlag.
        destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) block) eqn:HbeqNewSceBlock;
            try(exfalso; congruence). rewrite <-beqAddrFalse in HbeqNewSceBlock.
        rewrite removeDupIdentity; intuition.
      }
      rewrite HgetMappedBlocksChildEq in HblockMappedChild. unfold bentryPFlag in HPFlag.
      unfold bentryStartAddr in Hstart. unfold bentryEndAddr in Hend. rewrite HlookupEq in *.
      specialize(Hcons0 pdparent child block startChild endChild HparentIsPart HchildIsChild HblockMappedChild
        Hstart Hend HPFlag). destruct Hcons0 as [blockParent [startParent [endParent (HblockParentMapped &
        HstartParent & HendParent & Hbounds)]]]. exists blockParent. exists startParent. exists endParent.
      assert(HgetMappedBlocksParentEq: getMappedBlocks pdparent newS = getMappedBlocks pdparent s).
      {
        apply getMappedBlocksEqSCE; try(assumption). apply partitionsArePDT; try(assumption).
        unfold consistency1 in *; intuition.
      }
      assert(HlookupBlockParentEq: lookup blockParent (memory newS) beqAddr
                                    = lookup blockParent (memory s) beqAddr).
      {
        simpl. destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) blockParent) eqn:HbeqNewSceBlockParent.
        {
          rewrite <-beqAddrTrue in HbeqNewSceBlockParent. unfold bentryStartAddr in HstartParent.
          rewrite HbeqNewSceBlockParent in *. rewrite HlookupNewSce in HstartParent. exfalso; congruence.
        }
        rewrite <-beqAddrFalse in HbeqNewSceBlockParent. rewrite removeDupIdentity; intuition.
      }
      rewrite HgetMappedBlocksParentEq. unfold bentryStartAddr. unfold bentryEndAddr.
      rewrite HlookupBlockParentEq. intuition.
      (* END blockInChildHasAtLeastEquivalentBlockInParent *)
    }

    assert(partitionTreeIsTree newS).
    { (* BEGIN partitionTreeIsTree newS *)
      assert(Hcons0: partitionTreeIsTree s) by (unfold consistency1 in *; intuition).
      intros child pdparent parentsList HbeqChildRoot HchildIsPart HparentIsParent HparentsList.
      rewrite HgetPartsEq in HchildIsPart.
      assert(HparentIsParents: pdentryParent child pdparent s).
      {
        unfold pdentryParent in *. simpl in HparentIsParent.
        destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) child) eqn:HbeqNewSceChild;
          try(exfalso; congruence). rewrite <-beqAddrFalse in HbeqNewSceChild.
        rewrite removeDupIdentity in HparentIsParent; intuition.
      }
      assert(HparentsLists: isParentsList s parentsList pdparent).
      {
        revert HparentsList. apply isParentsListEqSCERev with s3; try(assumption).
        - unfold pdentryParent in HparentIsParents.
          destruct (lookup child (memory s) beqAddr) eqn:HlookupChild; try(exfalso; congruence).
          destruct v; try(exfalso; congruence).
          assert(HparentOfPart: parentOfPartitionIsPartition s) by (unfold consistency1 in *; intuition).
          specialize(HparentOfPart child p HlookupChild).
          destruct HparentOfPart as (HparentIsPart & _ & _). specialize(HparentIsPart HbeqChildRoot).
          destruct HparentIsPart. rewrite HparentIsParents. assumption.
        - unfold consistency1 in *; intuition.
      }
      specialize(Hcons0 child pdparent parentsList HbeqChildRoot HchildIsPart HparentIsParents HparentsLists).
      assumption.
      (* END partitionTreeIsTree *)
    }

    assert(kernelEntriesAreValid newS).
    { (* BEGIN kernelEntriesAreValid newS *)
      assert(Hcons0: kernelEntriesAreValid s) by (unfold consistency1 in *; intuition).
      intros kernel idx HkernIsKS HidxBounded.
      assert(HkernIsKSs: isKS kernel s).
      {
        unfold isKS in HkernIsKS. simpl in HkernIsKS.
        destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) kernel) eqn:HbeqNewSceKern;
            try(exfalso; congruence). rewrite <-beqAddrFalse in HbeqNewSceKern.
        rewrite removeDupIdentity in HkernIsKS; intuition.
      }
      specialize(Hcons0 kernel idx HkernIsKSs HidxBounded). unfold isBE in *. simpl.
      destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) (CPaddr (kernel + idx))) eqn:HbeqNewSceKernIdx.
      {
        rewrite <-beqAddrTrue in HbeqNewSceKernIdx. rewrite HbeqNewSceKernIdx in *.
        rewrite HlookupNewSce in Hcons0. congruence.
      }
      rewrite <-beqAddrFalse in HbeqNewSceKernIdx. rewrite removeDupIdentity; intuition.
      (* END kernelEntriesAreValid *)
    }

    assert(nextKernelIsValid newS).
    { (* BEGIN nextKernelIsValid newS *)
      assert(Hcons0: nextKernelIsValid s) by (unfold consistency1 in *; intuition).
      intros kernel HkernIsKS.
      assert(HkernIsKSs: isKS kernel s).
      {
        unfold isKS in HkernIsKS. simpl in HkernIsKS.
        destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) kernel) eqn:HbeqNewSceKern;
            try(exfalso; congruence). rewrite <-beqAddrFalse in HbeqNewSceKern.
        rewrite removeDupIdentity in HkernIsKS; intuition.
      }
      specialize(Hcons0 kernel HkernIsKSs). destruct Hcons0 as (HnextValid & [nextAddr (HlookupNext & HnextOr)]).
      split. assumption. exists nextAddr. split.
      - intro Hp. specialize(HlookupNext Hp). simpl.
        destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) {| p := kernel + nextoffset; Hp := Hp |})
          eqn:HbeqNewSceNext.
        {
          rewrite <-beqAddrTrue in HbeqNewSceNext. rewrite HbeqNewSceNext in *. congruence.
        }
        rewrite <-beqAddrFalse in HbeqNewSceNext. rewrite removeDupIdentity; intuition.
      - destruct HnextOr as [HnextIsKS | HnextIsNull]; try(right; assumption). left. unfold isKS in *. simpl.
        destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) nextAddr) eqn:HbeqNewSceNext.
        {
          rewrite <-beqAddrTrue in HbeqNewSceNext. rewrite HbeqNewSceNext in *.
          rewrite HlookupNewSce in HnextIsKS. congruence.
        }
        rewrite <-beqAddrFalse in HbeqNewSceNext. rewrite removeDupIdentity; intuition.
      (* END nextKernelIsValid *)
    }

    assert(noDupListOfKerns newS).
    { (* BEGIN noDupListOfKerns newS *)
      assert(Hcons0: noDupListOfKerns s) by (unfold consistency1 in *; intuition).
      intros partition kernList HkernList.
      assert(HkernLists: isListOfKernels kernList partition s).
      {
        revert HkernList. apply isListOfKernelsEqSCE.
      }
      specialize(Hcons0 partition kernList HkernLists). assumption.
      (* END noDupListOfKerns *)
    }

    assert(MPUsizeIsBelowMax newS).
    { (* BEGIN MPUsizeIsBelowMax newS *)
      assert(Hcons0: MPUsizeIsBelowMax s) by (unfold consistency1 in *; intuition).
      intros partition MPUlist HMPUlist.
      assert(HMPUlists: pdentryMPU partition MPUlist s).
      {
        unfold pdentryMPU in HMPUlist. simpl in HMPUlist.
        destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) partition) eqn:HbeqNewScePart;
            try(exfalso; congruence).
        rewrite <-beqAddrFalse in HbeqNewScePart. rewrite removeDupIdentity in HMPUlist; intuition.
      }
      specialize(Hcons0 partition MPUlist HMPUlists). assumption.
      (* END MPUsizeIsBelowMax *)
    }

    assert(originIsParentBlocksStart newS).
    { (* BEGIN originIsParentBlocksStart newS *)
      assert(Hcons0: originIsParentBlocksStart s) by (unfold consistency1 in *; intuition).
      intros part pdentryPart block scentryaddr scorigin HpartIsPart HlookupPart HblockMapped Hsce Horigin.
      rewrite HgetPartsEq in HpartIsPart.
      assert(HlookupParts: lookup part (memory s) beqAddr = Some (PDT pdentryPart)).
      {
        simpl in HlookupPart.
        destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) part) eqn:HbeqNewScePart; try(exfalso; congruence).
        rewrite <-beqAddrFalse in HbeqNewScePart.
        rewrite removeDupIdentity in HlookupPart; try(apply not_eq_sym; assumption). assumption.
      }
      assert(HgetMappedBlocksPartEq: getMappedBlocks part newS = getMappedBlocks part s).
      {
        apply getMappedBlocksEqSCE; try(assumption). apply partitionsArePDT; try(assumption).
        unfold consistency1 in *; intuition.
      }
      assert(HparentOfPart: parentOfPartitionIsPartition s) by (unfold consistency1 in *; intuition).
      specialize(HparentOfPart part pdentryPart HlookupParts).
      assert(Horigins: scentryOrigin scentryaddr scorigin s).
      {
        unfold scentryOrigin in *. simpl in Horigin.
        destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) scentryaddr) eqn:HbeqSceSce.
        - rewrite <-beqAddrTrue in HbeqSceSce. rewrite HbeqSceSce in *. rewrite HlookupNewSce.
          simpl in Horigin. assumption.
        - rewrite <-beqAddrFalse in HbeqSceSce.
          rewrite removeDupIdentity in Horigin; try(apply not_eq_sym; assumption). assumption.
      }
      rewrite HgetMappedBlocksPartEq in HblockMapped.
      specialize(Hcons0 part pdentryPart block scentryaddr scorigin HpartIsPart HlookupParts HblockMapped Hsce
        Horigins). destruct Hcons0 as (Hcons0 & HstartAbove). split.
      - intro HbeqPartRoot. specialize(Hcons0 HbeqPartRoot).
        destruct HparentOfPart as (HparentIsPart & _ & HbeqParentPart). specialize(HparentIsPart HbeqPartRoot).
        destruct HparentIsPart as ([parentEntry HlookupParent] & HparentIsPart).
        assert(HgetBlocksParentEq: getMappedBlocks (parent pdentryPart) newS
                                    = getMappedBlocks (parent pdentryPart) s).
        { apply getMappedBlocksEqSCE; try(assumption). unfold isPDT. rewrite HlookupParent. trivial. }
        rewrite HgetBlocksParentEq.
        destruct Hcons0 as [blockParent (HblockParentMapped & HstartParent & Hincl)].
        exists blockParent.
        assert(HlookupBlockEq: lookup block (memory newS) beqAddr = lookup block (memory s) beqAddr).
        {
          simpl. destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) block) eqn:HbeqNewSceBlock.
          {
            exfalso. rewrite <-beqAddrTrue in HbeqNewSceBlock. subst block.
            apply mappedBlockIsBE in HblockMapped. destruct HblockMapped as [bentryBlock (HlookupBlock & _)].
            unfold isSCE in HsceIsSCE. rewrite HlookupBlock in HsceIsSCE. congruence.
          }
          rewrite <-beqAddrFalse in HbeqNewSceBlock. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
          reflexivity.
        }
        assert(HlookupBlockParentEq: lookup blockParent (memory newS) beqAddr
                                      = lookup blockParent (memory s) beqAddr).
        {
          simpl. destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) blockParent) eqn:HbeqNewSceBlockParent.
          {
            exfalso. rewrite <-beqAddrTrue in HbeqNewSceBlockParent. subst blockParent.
            apply mappedBlockIsBE in HblockParentMapped.
            destruct HblockParentMapped as [bentryBlock (HlookupBlock & _)].
            unfold isSCE in HsceIsSCE. rewrite HlookupBlock in HsceIsSCE. congruence.
          }
          rewrite <-beqAddrFalse in HbeqNewSceBlockParent.
          rewrite removeDupIdentity; try(apply not_eq_sym; assumption). reflexivity.
        }
        split. assumption. split. unfold bentryStartAddr. rewrite HlookupBlockParentEq. assumption.
        cbn -[newS]. simpl in Hincl. rewrite HlookupBlockEq. rewrite HlookupBlockParentEq. assumption.
      - intros startBlock HstartBlock. apply HstartAbove. unfold bentryStartAddr in *. simpl in HstartBlock.
        destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) block) eqn:HbeqNewSceBlock;
          try(exfalso; congruence). rewrite <-beqAddrFalse in HbeqNewSceBlock.
        rewrite removeDupIdentity in HstartBlock; try(apply not_eq_sym); assumption.
      (* END originIsParentBlocksStart *)
    }

    assert(nextImpliesBlockWasCut newS).
    { (* BEGIN nextImpliesBlockWasCut newS *)
      assert(Hcons0: nextImpliesBlockWasCut s) by (unfold consistency1 in *; intuition).
      intros part pdentryPart block scentryaddr scnext endaddr HpartIsPart HlookupPart HblockMapped HendBlock
        Hsce HbeqSceNull Hnext HbeqPartRoot. rewrite HgetPartsEq in HpartIsPart.
      assert(HlookupParts: lookup part (memory s) beqAddr = Some (PDT pdentryPart)).
      {
        simpl in HlookupPart.
        destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) part) eqn:HbeqNewScePart; try(exfalso; congruence).
        rewrite <-beqAddrFalse in HbeqNewScePart.
        rewrite removeDupIdentity in HlookupPart; try(apply not_eq_sym; assumption). assumption.
      }
      assert(HgetMappedBlocksPartEq: getMappedBlocks part newS = getMappedBlocks part s).
      {
        apply getMappedBlocksEqSCE; try(assumption). apply partitionsArePDT; try(assumption).
        unfold consistency1 in *; intuition.
      }
      assert(HparentOfPart: parentOfPartitionIsPartition s) by (unfold consistency1 in *; intuition).
      specialize(HparentOfPart part pdentryPart HlookupParts).
      destruct HparentOfPart as (HparentIsPart & _ & HbeqParentPart). specialize(HparentIsPart HbeqPartRoot).
      destruct HparentIsPart as ([parentEntry HlookupParent] & HparentIsPart).
      assert(HgetBlocksParentEq: getMappedBlocks (parent pdentryPart) newS
                                  = getMappedBlocks (parent pdentryPart) s).
      { apply getMappedBlocksEqSCE; try(assumption). unfold isPDT. rewrite HlookupParent. trivial. }
      rewrite HgetMappedBlocksPartEq in HblockMapped. rewrite HgetBlocksParentEq.
      destruct (beqAddr idNewSubblock block) eqn:HbeqNewBlock.
      - rewrite <-beqAddrTrue in HbeqNewBlock. subst block. rewrite <-Hsce in *. subst sceaddr.
        unfold scentryNext in Hnext. simpl in Hnext. rewrite <-Hsce in Hnext.
        rewrite InternalLemmas.beqAddrTrue in Hnext. simpl in Hnext. subst scnext.
        assert(HpartIsCurr: part = currentPart).
        {
          destruct (beqAddr part currentPart) eqn:HbeqPartCurr; try(rewrite beqAddrTrue; assumption). exfalso.
          rewrite <-beqAddrFalse in HbeqPartCurr.
          assert(HblockMappedCurr: In idNewSubblock (getMappedBlocks currentPart s)).
          {
            intuition. destruct H87 as [optionfreeslotslist [s4 [n0 [n1 [n2 [nbleft Hprops]]]]]].
            assert(HgetBlocksCurrEq: forall block, In block (getMappedBlocks currentPart s2)
                    <-> firstfreeslot pdentry = block \/ In block (getMappedBlocks currentPart s0)) by intuition.
            assert(HgetBlocksCurrEqs: getMappedBlocks currentPart s = getMappedBlocks currentPart s2).
            {
              destruct blockToShareEnabled.
              - assert(Htriv: is_true true) by (unfold is_true; reflexivity). specialize(Henabled Htriv).
                destruct Henabled as [pdentryCurrs (Hs & Henabled)]. rewrite Hs.
                apply getMappedBlocksEqPDT with pdentryCurrs2; try(assumption).
                unfold consistency1 in *; intuition. simpl. reflexivity.
              - assert(Htriv: ~is_true false) by (unfold is_true; intro Hcontra; congruence).
                specialize(HnotEnabled Htriv). subst s. reflexivity.
            }
            rewrite HgetBlocksCurrEqs. apply HgetBlocksCurrEq. left.
            assert(Hres: pdentryFirstFreeSlot currentPart idNewSubblock s0) by assumption.
            unfold pdentryFirstFreeSlot in Hres.
            assert(Hlookup: lookup currentPart (memory s0) beqAddr = Some (PDT pdentry)) by assumption.
            rewrite Hlookup in Hres. apply eq_sym. assumption.
          }
          unfold getMappedBlocks in HblockMapped. unfold getMappedBlocks in HblockMappedCurr.
          apply InFilterPresentInList in HblockMapped. apply InFilterPresentInList in HblockMappedCurr.
          assert(Hdisjoint: DisjointKSEntries s) by (unfold consistency1 in *; intuition).
          assert(HpartIsPDT: isPDT part s) by (unfold isPDT; rewrite HlookupParts; trivial).
          specialize(Hdisjoint part currentPart HpartIsPDT HcurrIsPDTs HbeqPartCurr).
          destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
          specialize(Hdisjoint idNewSubblock HblockMapped). congruence.
        }
        subst part.
        assert(Htriv: CPaddr (blockToShareInCurrPartAddr + scoffset)
                      = CPaddr (blockToShareInCurrPartAddr + scoffset)) by reflexivity.
        assert(Hcons0Bis: nextImpliesBlockWasCut s0)
          by (unfold consistency in *; unfold consistency1 in *; intuition).
        assert(HnextRights0: scentryNext (CPaddr (blockToShareInCurrPartAddr + scoffset)) originalNextSubblock
          s0).
        {
          assert(Hnexts2: scentryNext (CPaddr (blockToShareInCurrPartAddr + scoffset)) originalNextSubblock s2).
          {
            unfold scentryNext in HnextRight. destruct blockToShareEnabled.
            - assert(HtrivTrue: is_true true) by (unfold is_true; reflexivity). specialize(Henabled HtrivTrue).
              destruct Henabled as [pdentryCurrs (Hs & Henabled)]. rewrite Hs in HnextRight. simpl in HnextRight.
              destruct (beqAddr currentPart (CPaddr (blockToShareInCurrPartAddr + scoffset))) eqn:HbeqCurrSce;
                try(exfalso; congruence). rewrite <-beqAddrFalse in HbeqCurrSce.
              rewrite removeDupIdentity in HnextRight; try(apply not_eq_sym; assumption). assumption.
            - assert(HtrivFalse: ~is_true false) by (unfold is_true; intro Hcontra; congruence).
              specialize(HnotEnabled HtrivFalse). subst s. assumption.
          }
          unfold scentryNext in Hnexts2. rewrite Hs2 in Hnexts2. simpl in Hnexts2.
          destruct (beqAddr blockToShareInCurrPartAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)))
              eqn:HbeqBlockSce; try(exfalso; congruence). rewrite <-beqAddrFalse in HbeqBlockSce.
          rewrite removeDupIdentity in Hnexts2; try(apply not_eq_sym; assumption). rewrite H83 in Hnexts2.
          assert(HbeqNewNewSce: beqAddr idNewSubblock (CPaddr (firstfreeslot pdentry + scoffset)) = false).
          {
            rewrite <-beqAddrFalse.
            assert(Hlookup: pdentryFirstFreeSlot currentPart idNewSubblock s0) by assumption.
            unfold pdentryFirstFreeSlot in Hlookup. rewrite H30 in Hlookup. rewrite Hlookup. intuition.
          }
          simpl in Hnexts2. destruct (beqAddr (CPaddr (firstfreeslot pdentry + scoffset))
                (CPaddr (blockToShareInCurrPartAddr + scoffset))) eqn:HbeqSces.
          - (*False, but not a problem*) rewrite <-beqAddrTrue in HbeqSces. rewrite HbeqSces in *.
            unfold scentryNext. rewrite H29. simpl in Hnexts2. assumption.
          - rewrite HbeqNewNewSce in Hnexts2. simpl in Hnexts2.
            destruct (beqAddr idNewSubblock (CPaddr (blockToShareInCurrPartAddr + scoffset))) eqn:HbeqNewBlockSce;
              try(exfalso; congruence). rewrite InternalLemmas.beqAddrTrue in Hnexts2.
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in Hnexts2; try(apply not_eq_sym; assumption).
            rewrite removeDupIdentity in Hnexts2; try(apply not_eq_sym; assumption).
            rewrite removeDupIdentity in Hnexts2; try(apply not_eq_sym; assumption).
            rewrite removeDupIdentity in Hnexts2; try(apply not_eq_sym; assumption).
            rewrite removeDupIdentity in Hnexts2; try(apply not_eq_sym; assumption).
            rewrite removeDupIdentity in Hnexts2; try(apply not_eq_sym; assumption).
            rewrite removeDupIdentity in Hnexts2; try(apply not_eq_sym; assumption).
            rewrite InternalLemmas.beqAddrTrue in Hnexts2.
            destruct (beqAddr currentPart idNewSubblock) eqn:HbeqCurrNew.
            + (*False, but not a problem*) rewrite <-beqAddrTrue in HbeqCurrNew. subst idNewSubblock.
            rewrite removeDupIdentity in Hnexts2; try(apply not_eq_sym; assumption).
            rewrite removeDupIdentity in Hnexts2; try(apply not_eq_sym; assumption).
            rewrite removeDupIdentity in Hnexts2; try(apply not_eq_sym; assumption). assumption.
            + simpl in Hnexts2.
              destruct (beqAddr currentPart (CPaddr (blockToShareInCurrPartAddr + scoffset)))
                eqn:HbeqCurrBlockSce; try(exfalso; congruence). rewrite <-beqAddrFalse in *.
              rewrite removeDupIdentity in Hnexts2; try(apply not_eq_sym; assumption).
              rewrite removeDupIdentity in Hnexts2; try(apply not_eq_sym; assumption).
              rewrite removeDupIdentity in Hnexts2; try(apply not_eq_sym; assumption). assumption.
        }
        assert(HpartIsParts0: In currentPart (getPartitions multiplexer s0)).
        {
          assert(Hres: currentPartitionInPartitionsList s0)
              by (unfold consistency in *; unfold consistency1 in *; intuition).
          unfold currentPartitionInPartitionsList in Hres. subst currentPart. assumption.
        }
        specialize(Hcons0Bis currentPart pdentry blockToShareInCurrPartAddr
          (CPaddr (blockToShareInCurrPartAddr + scoffset)) originalNextSubblock blockToCutEndAddr HpartIsParts0
          H30 H56 H54 Htriv HbeqSceNull HnextRights0 HbeqPartRoot).
        destruct Hcons0Bis as [blockParent [endParent (HblockParentMapped & HendParent & Hends & Hincl)]].
        destruct H87 as [optionfreeslotslist [s4 [n0 [n1 [n2 [nbleft Hprops]]]]]].
        assert(HgetBlocksParentEqs2: forall partition, partition <> currentPart -> isPDT partition s0
                        -> getMappedBlocks partition s2 = getMappedBlocks partition s0) by intuition.
        assert(HparentIsPDT: isPDT (parent pdentryPart) s0).
        {
          apply partitionsArePDT. unfold consistency in *; unfold consistency1 in *; intuition.
          unfold consistency in *; unfold consistency1 in *; intuition.
          assert(Hs4s0: getPartitions multiplexer s4 = getPartitions multiplexer s0) by intuition.
          assert(Hs1s4: getPartitions multiplexer s1 = getPartitions multiplexer s4) by intuition.
          rewrite <-Hs4s0. rewrite <-Hs1s4.
          assert(Hss1: getPartitions multiplexer s = getPartitions multiplexer s1).
          {
            assert(Hss2: getPartitions multiplexer s = getPartitions multiplexer s2).
            {
              destruct blockToShareEnabled.
              - assert(HtrivTrue: is_true true) by (unfold is_true; reflexivity). specialize(Henabled HtrivTrue).
                destruct Henabled as [pdentryCurrs (Hs & Henabled)]. rewrite Hs.
                apply getPartitionsEqPDT with pdentryCurrs2; try(assumption). simpl. reflexivity.
                unfold consistency1 in *; intuition. unfold consistency1 in *; intuition.
              - assert(HtrivFalse: ~is_true false) by (unfold is_true; intro Hcontra; congruence).
                specialize(HnotEnabled HtrivFalse). subst s. reflexivity.
            }
            rewrite Hss2. rewrite Hs2. assert(HcurrEq: currentPartition s0 = currentPartition s1).
            { rewrite H83. simpl. reflexivity. }
            rewrite HcurrEq. apply getPartitionsEqBEPDflagNoChangePresentNoChangeStartNoChange with bentryShare
                (CPaddr (blockToShareInCurrPartAddr + sh1offset)); try(assumption).
            unfold consistency1 in *; intuition. unfold consistency1 in *; intuition.
            apply lookupSh1EntryAddr with bentryShare. assumption.
            unfold sh1entryPDflag in *. rewrite Hs2 in *. simpl in *.
            destruct (beqAddr blockToShareInCurrPartAddr (CPaddr (blockToShareInCurrPartAddr + sh1offset)))
              eqn:HbeqBlockBlockSce; try(exfalso; congruence). rewrite <-beqAddrFalse in HbeqBlockBlockSce.
            rewrite removeDupIdentity; try(apply not_eq_sym; assumption). reflexivity.
            unfold CBlockEntry. assert(blockindex bentryShare < kernelStructureEntriesNb) by (apply Hidx).
            destruct (Compare_dec.lt_dec (blockindex bentryShare) kernelStructureEntriesNb); try(lia).
            simpl. reflexivity.
            unfold CBlockEntry. assert(blockindex bentryShare < kernelStructureEntriesNb) by (apply Hidx).
            destruct (Compare_dec.lt_dec (blockindex bentryShare) kernelStructureEntriesNb); try(lia).
            simpl. unfold CBlock. assert(cutAddr <= maxIdx) by (rewrite maxIdxEqualMaxAddr; apply Hp).
            destruct (Compare_dec.le_dec (cutAddr - startAddr (blockrange bentryShare)) maxIdx); try(lia).
            simpl. reflexivity.
            unfold consistency1 in *; intuition.
          }
          rewrite <-Hss1. assumption.
        }
        specialize(HgetBlocksParentEqs2 (parent pdentryPart) HbeqParentPart HparentIsPDT).
        assert(HgetBlocksParentEqs: getMappedBlocks (parent pdentryPart) s
                                    = getMappedBlocks (parent pdentryPart) s2).
        {
          destruct blockToShareEnabled.
          - assert(HtrivTrue: is_true true) by (unfold is_true; reflexivity). specialize(Henabled HtrivTrue).
            destruct Henabled as [pdentryCurrs (Hs & Henabled)]. rewrite Hs.
            apply getMappedBlocksEqPDT with pdentryCurrs2; try(assumption).
            unfold consistency1 in *; intuition. simpl. reflexivity.
          - assert(HtrivFalse: ~is_true false) by (unfold is_true; intro Hcontra; congruence).
            specialize(HnotEnabled HtrivFalse). subst s. reflexivity.
        }
        assert(HparentsEq: parent pdentryPart = parent pdentry).
        {
          assert(HlookupParts2: exists pdentryParts2,
              lookup currentPart (memory s2) beqAddr = Some (PDT pdentryParts2)
              /\ parent pdentryPart = parent pdentryParts2).
          {
            destruct blockToShareEnabled.
            - assert(HtrivTrue: is_true true) by (unfold is_true; reflexivity). specialize(Henabled HtrivTrue).
              destruct Henabled as [pdentryCurrs (Hs & Henabled)]. rewrite Hs in HlookupParts.
              simpl in HlookupParts. rewrite InternalLemmas.beqAddrTrue in HlookupParts.
              injection HlookupParts as HpdentriesEq. subst pdentryPart. exists pdentryCurrs2. split.
              assumption. simpl. reflexivity.
            - assert(HtrivFalse: ~is_true false) by (unfold is_true; intro Hcontra; congruence).
              specialize(HnotEnabled HtrivFalse). subst s. exists pdentryPart. split. assumption. reflexivity.
          }
          destruct HlookupParts2 as [pdentryParts2 (HlookupParts2 & HparentsEqss2)]. rewrite HparentsEqss2.
          assert(HlookupCurrs2Bis: lookup currentPart (memory s2) beqAddr = Some (PDT newpdentry))
              by assumption. rewrite HlookupCurrs2Bis in HlookupParts2. injection HlookupParts2 as HpdentriesEq.
          subst pdentryParts2. subst newpdentry. subst pdentryInter1. subst pdentryInter0. simpl.
          reflexivity.
        }
        rewrite HparentsEq in *.
        assert(HlookupBlockParentEq: lookup blockParent (memory newS) beqAddr
                                      = lookup blockParent (memory s0) beqAddr).
        {
          simpl. unfold bentryEndAddr in HendParent.
          assert(HsceIsSCEs0: isSCE scentryaddr s0).
          {
            assert(HwellFormedSce: wellFormedShadowCutIfBlockEntry s0)
                by (unfold consistency in *; unfold consistency1 in *; intuition).
            assert(HnewIsBEs0: isBE idNewSubblock s0) by (unfold isBE; rewrite HlookupNews0; trivial).
            specialize(HwellFormedSce idNewSubblock HnewIsBEs0).
            destruct HwellFormedSce as [scentryaddrBis (Hres & HsceBis)]. rewrite <-Hsce in HsceBis.
            subst scentryaddrBis. assumption.
          }
          destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) blockParent) eqn:HbeqNewSceBlockP.
          {
            rewrite <-beqAddrTrue in HbeqNewSceBlockP. rewrite HbeqNewSceBlockP in *. rewrite Hsce in *.
            unfold isSCE in HsceIsSCEs0. exfalso.
            destruct (lookup blockParent (memory s0) beqAddr); try(congruence). destruct v; congruence.
          }
          rewrite <-beqAddrFalse in HbeqNewSceBlockP.
          rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
          assert(Hss2: lookup blockParent (memory s) beqAddr = lookup blockParent (memory s2) beqAddr).
          {
            destruct blockToShareEnabled.
            - assert(HtrivTrue: is_true true) by (unfold is_true; reflexivity). specialize(Henabled HtrivTrue).
              destruct Henabled as [pdentryCurrs (Hs & Henabled)]. rewrite Hs. simpl.
              destruct (beqAddr currentPart blockParent) eqn:HbeqCurrBlockP.
              {
                rewrite <-beqAddrTrue in HbeqCurrBlockP. subst blockParent. rewrite H30 in HendParent.
                exfalso; congruence.
              }
              rewrite <-beqAddrFalse in HbeqCurrBlockP.
              rewrite removeDupIdentity; try(apply not_eq_sym; assumption). reflexivity.
            - assert(HtrivFalse: ~is_true false) by (unfold is_true; intro Hcontra; congruence).
              specialize(HnotEnabled HtrivFalse). subst s. reflexivity.
          }
          rewrite Hss2. rewrite Hs2. simpl.
          destruct (beqAddr blockToShareInCurrPartAddr blockParent) eqn:HbeqBlocks.
          {
            rewrite <-beqAddrTrue in HbeqBlocks. subst blockParent. exfalso.
            assert(HblockParentMappedCurr: In blockToShareInCurrPartAddr (getMappedBlocks currentPart s0))
              by assumption. unfold getMappedBlocks in HblockParentMappedCurr.
            unfold getMappedBlocks in HblockParentMapped. apply InFilterPresentInList in HblockParentMapped.
            apply InFilterPresentInList in HblockParentMappedCurr.
            assert(Hdisjoint: DisjointKSEntries s0)
                by (unfold consistency in *; unfold consistency1 in *; intuition).
            specialize(Hdisjoint (parent pdentry) currentPart HparentIsPDT H40 HbeqParentPart).
            destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
            specialize(Hdisjoint blockToShareInCurrPartAddr HblockParentMapped). congruence.
          }
          rewrite <-beqAddrFalse in HbeqBlocks. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
          rewrite H83. simpl. rewrite beqAddrFalse in HbeqNewSceBlockP.
          assert(Hfirst: pdentryFirstFreeSlot currentPart idNewSubblock s0) by assumption.
          unfold pdentryFirstFreeSlot in Hfirst. rewrite H30 in Hfirst. rewrite <-Hfirst in *.
          rewrite HbeqNewSceBlockP.
          assert(HbeqNewNewSce: beqAddr idNewSubblock (CPaddr (idNewSubblock + scoffset)) = false).
          { rewrite <-beqAddrFalse. intuition. }
          rewrite HbeqNewNewSce. simpl. destruct (beqAddr idNewSubblock blockParent) eqn:HbeqNewBlockP.
          {
            rewrite <-beqAddrTrue in HbeqNewBlockP. subst blockParent. exfalso.
            apply mappedBlockIsBE in HblockParentMapped.
            destruct HblockParentMapped as [bentryNew (HlookupNews0Bis & Hcontra)].
            assert(HfirstIsFree: FirstFreeSlotPointerIsBEAndFreeSlot s0)
                by (unfold consistency in *; unfold consistency1 in *; intuition).
            assert(HbeqFirstNull: firstfreeslot pdentry <> nullAddr).
            {
              rewrite <-Hfirst. intro HbeqFirstNull. rewrite HbeqFirstNull in *.
              assert(Hnull: nullAddrExists s) by (unfold consistency1 in *; intuition).
              unfold nullAddrExists in Hnull. unfold isPADDR in Hnull. rewrite HlookupNews in Hnull. congruence.
            }
            specialize(HfirstIsFree currentPart pdentry H30 HbeqFirstNull).
            destruct HfirstIsFree as (_ & HfirstIsFree). rewrite <-Hfirst in HfirstIsFree.
            unfold isFreeSlot in HfirstIsFree. rewrite HlookupNews0Bis in HfirstIsFree.
            destruct (lookup (CPaddr (idNewSubblock + sh1offset)) (memory s0) beqAddr); try(congruence).
            destruct v; try(congruence).
            destruct (lookup (CPaddr (idNewSubblock + scoffset)) (memory s0) beqAddr); try(congruence).
            destruct v; try(congruence).
            destruct HfirstIsFree as (_ & _ & _ & _ & Hpresent & _). congruence.
          }
          rewrite InternalLemmas.beqAddrTrue.
          assert(HbeqCurrNew: beqAddr currentPart idNewSubblock = false) by (rewrite <-beqAddrFalse; intuition).
          rewrite HbeqCurrNew. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
          rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
          rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
          rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
          rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
          rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
          rewrite removeDupIdentity; try(apply not_eq_sym; assumption). simpl.
          destruct (beqAddr currentPart blockParent) eqn:HbeqCurrBlockP.
          {
            rewrite <-beqAddrTrue in HbeqCurrBlockP. subst blockParent. rewrite H30 in HendParent.
            exfalso; congruence.
          }
          rewrite InternalLemmas.beqAddrTrue. rewrite <-beqAddrFalse in HbeqCurrBlockP.
          rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
          rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
          rewrite removeDupIdentity; try(apply not_eq_sym; assumption). reflexivity.
        }
        exists blockParent. exists endParent. split. rewrite HgetBlocksParentEqs. rewrite HgetBlocksParentEqs2.
        assumption. split. unfold bentryEndAddr. rewrite HlookupBlockParentEq. assumption. split.
        + unfold bentryEndAddr in HendBlock. simpl in HendBlock.
          destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) idNewSubblock) eqn:HbeqNewSceNew;
            try(exfalso; congruence). rewrite <-beqAddrFalse in HbeqNewSceNew.
          rewrite removeDupIdentity in HendBlock; try(apply not_eq_sym; assumption).
          rewrite HlookupNews in HendBlock. subst endaddr. unfold CBlockEntry in *. unfold CBlock in *.
          assert(blockindex bentry5 < kernelStructureEntriesNb) by (apply Hidx).
          assert(blockindex bentry4 < kernelStructureEntriesNb) by (apply Hidx).
          assert(blockindex bentry3 < kernelStructureEntriesNb) by (apply Hidx).
          assert(blockindex bentry2 < kernelStructureEntriesNb) by (apply Hidx).
          assert(blockindex bentry1 < kernelStructureEntriesNb) by (apply Hidx).
          assert(blockindex bentry0 < kernelStructureEntriesNb) by (apply Hidx).
          destruct (Compare_dec.lt_dec (blockindex bentry5) kernelStructureEntriesNb); try(lia).
          destruct (Compare_dec.lt_dec (blockindex bentry4) kernelStructureEntriesNb); try(lia).
          destruct (Compare_dec.lt_dec (blockindex bentry3) kernelStructureEntriesNb); try(lia).
          destruct (Compare_dec.lt_dec (blockindex bentry2) kernelStructureEntriesNb); try(lia).
          destruct (Compare_dec.lt_dec (blockindex bentry1) kernelStructureEntriesNb); try(lia).
          destruct (Compare_dec.lt_dec (blockindex bentry0) kernelStructureEntriesNb); try(lia).
          assert(blockEndAddr <= maxIdx) by (rewrite maxIdxEqualMaxAddr; apply Hp).
          destruct (Compare_dec.le_dec (blockEndAddr - startAddr (blockrange bentry0)) maxIdx); try(lia).
          assert(endAddr (blockrange bentry) <= maxIdx) by (rewrite maxIdxEqualMaxAddr; apply Hp).
          destruct (Compare_dec.le_dec (endAddr (blockrange bentry) - cutAddr) maxIdx); try(lia).
          rewrite H15. simpl. rewrite H17. simpl. rewrite H19. simpl. rewrite H21. simpl. rewrite H23. simpl.
          rewrite H24. simpl.
          assert(Hend1: bentryEndAddr blockToShareInCurrPartAddr blockEndAddr s0) by assumption.
          assert(Hend2: bentryEndAddr blockToShareInCurrPartAddr blockToCutEndAddr s0) by assumption.
          unfold bentryEndAddr in Hend1. unfold bentryEndAddr in Hend2. rewrite H7 in *. subst blockEndAddr.
          rewrite <-Hend2. assumption.
        + intros addr HaddrInNew. cbn -[newS]. rewrite HlookupBlockParentEq. simpl in Hincl. apply Hincl.
          rewrite H7. rewrite app_nil_r.
          assert(Hstart: bentryStartAddr blockToShareInCurrPartAddr blockToCutStartAddr s0) by assumption.
          assert(Hend: bentryEndAddr blockToShareInCurrPartAddr blockEndAddr s0) by assumption.
          unfold bentryStartAddr in Hstart. unfold bentryEndAddr in Hend. rewrite H7 in *. rewrite <-Hstart.
          rewrite <-Hend. simpl in HaddrInNew.
          destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) idNewSubblock) eqn:HbeqNewSceNew;
            try(exfalso; simpl in HaddrInNew; congruence). rewrite <-beqAddrFalse in HbeqNewSceNew.
          rewrite removeDupIdentity in HaddrInNew; try(apply not_eq_sym; assumption).
          rewrite HlookupNews in HaddrInNew. rewrite app_nil_r in HaddrInNew. unfold CBlockEntry in *.
          unfold CBlock in *. assert(blockindex bentry5 < kernelStructureEntriesNb) by (apply Hidx).
          assert(blockindex bentry4 < kernelStructureEntriesNb) by (apply Hidx).
          assert(blockindex bentry3 < kernelStructureEntriesNb) by (apply Hidx).
          assert(blockindex bentry2 < kernelStructureEntriesNb) by (apply Hidx).
          assert(blockindex bentry1 < kernelStructureEntriesNb) by (apply Hidx).
          assert(blockindex bentry0 < kernelStructureEntriesNb) by (apply Hidx).
          assert(blockindex bentry < kernelStructureEntriesNb) by (apply Hidx).
          destruct (Compare_dec.lt_dec (blockindex bentry5) kernelStructureEntriesNb); try(lia).
          destruct (Compare_dec.lt_dec (blockindex bentry4) kernelStructureEntriesNb); try(lia).
          destruct (Compare_dec.lt_dec (blockindex bentry3) kernelStructureEntriesNb); try(lia).
          destruct (Compare_dec.lt_dec (blockindex bentry2) kernelStructureEntriesNb); try(lia).
          destruct (Compare_dec.lt_dec (blockindex bentry1) kernelStructureEntriesNb); try(lia).
          destruct (Compare_dec.lt_dec (blockindex bentry0) kernelStructureEntriesNb); try(lia).
          destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
          assert(blockEndAddr <= maxIdx) by (rewrite maxIdxEqualMaxAddr; apply Hp).
          destruct (Compare_dec.le_dec (blockEndAddr - startAddr (blockrange bentry0)) maxIdx); try(lia).
          assert(endAddr (blockrange bentry) <= maxIdx) by (rewrite maxIdxEqualMaxAddr; apply Hp).
          destruct (Compare_dec.le_dec (endAddr (blockrange bentry) - cutAddr) maxIdx); try(lia).
          rewrite H15 in HaddrInNew. simpl in HaddrInNew. rewrite H17 in HaddrInNew. simpl in HaddrInNew.
          rewrite H19 in HaddrInNew. simpl in HaddrInNew. rewrite H21 in HaddrInNew. simpl in HaddrInNew.
          rewrite H23 in HaddrInNew. simpl in HaddrInNew. rewrite H24 in HaddrInNew. simpl in HaddrInNew.
          rewrite H26 in HaddrInNew. simpl in HaddrInNew. apply getAllPaddrBlockInclRev in HaddrInNew.
          destruct HaddrInNew as (HlebCutAddr & HltAddrEnd & _). unfold StateLib.Paddr.leb in HlebCutStart.
          apply eq_sym in HlebCutStart. apply PeanoNat.Nat.leb_gt in HlebCutStart.
          apply getAllPaddrBlockIncl; lia.
      - assert(HlookupBlockEq: lookup block (memory newS) beqAddr = lookup block (memory s) beqAddr).
        {
          simpl. unfold bentryEndAddr in HendBlock. simpl in HendBlock.
          destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) block) eqn:HbeqNewSceBlock;
            try(exfalso; congruence). rewrite <-beqAddrFalse in HbeqNewSceBlock.
          rewrite removeDupIdentity; try(apply not_eq_sym; assumption). reflexivity.
        }
        unfold bentryEndAddr in HendBlock. rewrite HlookupBlockEq in HendBlock.
        assert(Hnexts: scentryNext scentryaddr scnext s).
        {
          unfold scentryNext in *. simpl in Hnext.
          destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) scentryaddr) eqn:HbeqNewSceBlockSce.
          {
            rewrite <-beqAddrTrue in HbeqNewSceBlockSce. rewrite Hsce in HbeqNewSceBlockSce.
            unfold CPaddr in HbeqNewSceBlockSce. exfalso.
            destruct (Compare_dec.le_dec (idNewSubblock + scoffset) maxAddr) eqn:HleNewSceMax.
            - destruct (Compare_dec.le_dec (block + scoffset) maxAddr).
              + injection HbeqNewSceBlockSce as HscesEq. apply PeanoNat.Nat.add_cancel_r in HscesEq.
                rewrite <-beqAddrFalse in HbeqNewBlock. contradict HbeqNewBlock. destruct idNewSubblock.
                destruct block. simpl in HscesEq. subst p0. f_equal. apply proof_irrelevance.
              + assert(Hcontra: CPaddr (idNewSubblock + scoffset) = nullAddr).
                {
                  unfold nullAddr. unfold CPaddr. rewrite HleNewSceMax. rewrite HbeqNewSceBlockSce.
                  destruct (Compare_dec.le_dec 0 maxAddr); try(lia). f_equal. apply proof_irrelevance.
                }
                assert(Hnull: nullAddrExists s) by (unfold consistency1 in *; intuition). rewrite Hcontra in *.
                unfold nullAddrExists in Hnull. unfold isPADDR in Hnull. rewrite HlookupNewSce in Hnull.
                congruence.
            - assert(Hcontra: CPaddr (idNewSubblock + scoffset) = nullAddr).
              {
                unfold nullAddr. unfold CPaddr. rewrite HleNewSceMax.
                destruct (Compare_dec.le_dec 0 maxAddr); try(lia). f_equal. apply proof_irrelevance.
              }
              assert(Hnull: nullAddrExists s) by (unfold consistency1 in *; intuition). rewrite Hcontra in *.
              unfold nullAddrExists in Hnull. unfold isPADDR in Hnull. rewrite HlookupNewSce in Hnull.
              congruence.
          }
          rewrite <-beqAddrFalse in HbeqNewSceBlockSce.
          rewrite removeDupIdentity in Hnext; try(apply not_eq_sym); assumption.
        }
        specialize(Hcons0 part pdentryPart block scentryaddr scnext endaddr HpartIsPart HlookupParts HblockMapped
            HendBlock Hsce HbeqSceNull Hnexts HbeqPartRoot).
        destruct Hcons0 as [blockParent [endParent (HblockParentMapped & HendParent & Hends & Hincl)]].
        exists blockParent. exists endParent.
        assert(HlookupBlockParentEq: lookup blockParent (memory newS) beqAddr
                                      = lookup blockParent (memory s) beqAddr).
        {
          simpl. destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) blockParent) eqn:HbeqNewSceBlockP.
          {
            rewrite <-beqAddrTrue in HbeqNewSceBlockP. subst blockParent. unfold bentryEndAddr in HendParent.
            rewrite HlookupNewSce in HendParent. exfalso; congruence.
          }
          rewrite <-beqAddrFalse in HbeqNewSceBlockP.
          rewrite removeDupIdentity; try(apply not_eq_sym; assumption). reflexivity.
        }
        split. assumption. split. unfold bentryEndAddr. rewrite HlookupBlockParentEq. assumption. split.
        assumption. cbn -[newS]. simpl in Hincl. rewrite HlookupBlockEq. rewrite HlookupBlockParentEq.
        assumption.
      (* END nextImpliesBlockWasCut *)
    }

    unfold consistency1. intuition.
  - assert(Hcontra: isFreeSlot blockToShareInCurrPartAddr
                                    {|
                                      currentPartition := currentPartition s;
                                      memory :=
                                        add (CPaddr (idNewSubblock + scoffset))
                                          (SCE {| origin := origin s3; next := originalNextSubblock |}) 
                                          (memory s) beqAddr
                                    |}) by intuition.
    unfold isFreeSlot in Hcontra. simpl in Hcontra.
    destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) blockToShareInCurrPartAddr) eqn:HbeqNewSceBlock;
        try(congruence). rewrite <-beqAddrFalse in HbeqNewSceBlock.
    rewrite removeDupIdentity in Hcontra; try(apply not_eq_sym; assumption).
    assert(HlookupBlocks: lookup blockToShareInCurrPartAddr (memory s) beqAddr = Some (BE bentry7)).
    {
      destruct blockToShareEnabled.
      - assert(Htriv: is_true true) by (unfold is_true; reflexivity). specialize(Henabled Htriv).
        destruct Henabled as [pdentryCurrs (Hs & Henabled)]. rewrite Hs. simpl.
        destruct (beqAddr currentPart blockToShareInCurrPartAddr) eqn:HbeqCurrBlock.
        {
          rewrite <-beqAddrTrue in HbeqCurrBlock. rewrite HbeqCurrBlock in *. exfalso; congruence.
        }
        rewrite <-beqAddrFalse in HbeqCurrBlock. rewrite removeDupIdentity; intuition.
      - assert(Htriv: ~is_true false) by (unfold is_true; intuition). specialize(HnotEnabled Htriv).
        subst s. assumption.
    }
    assert(HlookupBlocks2: lookup blockToShareInCurrPartAddr (memory s2) beqAddr = Some (BE bentry7))
        by intuition. unfold bentryAFlag in *. rewrite HlookupBlocks in *. rewrite HlookupBlocks2 in *.
    destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) (CPaddr (blockToShareInCurrPartAddr + sh1offset)))
      eqn:HbeqNewSceBlockSh1; try(congruence). rewrite <-beqAddrFalse in HbeqNewSceBlockSh1.
    rewrite removeDupIdentity in Hcontra; try(apply not_eq_sym; assumption).
    destruct (lookup (CPaddr (blockToShareInCurrPartAddr + sh1offset)) (memory s) beqAddr); try(congruence).
    destruct v; try(congruence).
    destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) (CPaddr (blockToShareInCurrPartAddr + scoffset)))
        eqn:HbeqNewSceBlockSce.
    + destruct Hcontra as (_ & _ & _ & _ & _ & Hcontra & _). apply eq_sym in Hcontra. congruence.
    + rewrite <-beqAddrFalse in HbeqNewSceBlockSce.
      rewrite removeDupIdentity in Hcontra; try(apply not_eq_sym; assumption).
      destruct (lookup (CPaddr (blockToShareInCurrPartAddr + scoffset)) (memory s) beqAddr); try(congruence).
      destruct v; try(congruence).
      destruct Hcontra as (_ & _ & _ & _ & _ & Hcontra & _). apply eq_sym in Hcontra. congruence.
  - assert(Hcontra: isFreeSlot idNewSubblock
                                    {|
                                      currentPartition := currentPartition s;
                                      memory :=
                                        add (CPaddr (idNewSubblock + scoffset))
                                          (SCE {| origin := origin s3; next := originalNextSubblock |}) 
                                          (memory s) beqAddr
                                    |}) by intuition.
    unfold isFreeSlot in Hcontra. simpl in Hcontra.
    destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) idNewSubblock) eqn:HbeqNewSceNew;
        try(congruence). rewrite <-beqAddrFalse in HbeqNewSceNew.
    rewrite removeDupIdentity in Hcontra; try(apply not_eq_sym; assumption). rewrite HlookupNews in Hcontra.
    destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) (CPaddr (idNewSubblock + sh1offset)))
      eqn:HbeqNewSceNewSh1; try(congruence). rewrite <-beqAddrFalse in HbeqNewSceNewSh1.
    rewrite removeDupIdentity in Hcontra; try(apply not_eq_sym; assumption).
    destruct (lookup (CPaddr (idNewSubblock + sh1offset)) (memory s) beqAddr); try(congruence).
    destruct v; try(congruence). rewrite InternalLemmas.beqAddrTrue in Hcontra.
    destruct Hcontra as (_ & _ & _ & _ & _ & Hcontra & _). rewrite H15 in Hcontra. unfold CBlockEntry in Hcontra.
    assert(blockindex bentry5 < kernelStructureEntriesNb) by (apply Hidx).
    destruct (Compare_dec.lt_dec (blockindex bentry5) kernelStructureEntriesNb); try(lia). simpl in Hcontra.
    rewrite H17 in Hcontra. unfold CBlockEntry in Hcontra.
    assert(blockindex bentry4 < kernelStructureEntriesNb) by (apply Hidx).
    destruct (Compare_dec.lt_dec (blockindex bentry4) kernelStructureEntriesNb); try(lia). simpl in Hcontra.
    rewrite H19 in Hcontra. unfold CBlockEntry in Hcontra.
    assert(blockindex bentry3 < kernelStructureEntriesNb) by (apply Hidx).
    destruct (Compare_dec.lt_dec (blockindex bentry3) kernelStructureEntriesNb); try(lia). simpl in Hcontra.
    rewrite H21 in Hcontra. unfold CBlockEntry in Hcontra.
    assert(blockindex bentry2 < kernelStructureEntriesNb) by (apply Hidx).
    destruct (Compare_dec.lt_dec (blockindex bentry2) kernelStructureEntriesNb); try(lia). simpl in Hcontra.
    congruence.
  - rewrite Hs2. f_equal. rewrite H83. simpl. reflexivity.
}
  intro. eapply bindRev.
{ (** writeSCNextFromBlockEntryAddr **)
  eapply weaken. apply writeSCNextFromBlockEntryAddr.
  intros s Hprops. simpl. destruct Hprops as [s3 [s2 [s1 [s0 [predCurrentNbFreeSlots [sceaddr
    [newFirstFreeSlotAddr [scentry [scentryNew [pdentryCurrs0 [pdentryInter0 [pdentryCurrs2 [bentry [bentry0
    [bentry1 [bentry2 [bentry3 [bentry4 [bentry5 [bentry6 [bentryShares0 [bentryShares2 (Hs & Hconsists &
    Hsceaddr & HblockIsNotFree & Hprops)]]]]]]]]]]]]]]]]]]]]]]. split. unfold consistency1 in *; intuition.
  split. unfold consistency1 in *; intuition. split. unfold consistency1 in *; intuition.
  split. unfold consistency1 in *; intuition.
  destruct Hprops as (HnewIsNotFree & Hconsists3 & HcurrIsPDTs3 & HnewIsBEs3 & HPDTEqs3s2 & HgetKScurrEqs3s2 &
    HnextBlocks3 & HlookupNews3 & HlookupNewSces3 & HgetPartsEqs3s2 & HgetConfEqs3s2 & HgetAccBlocksEqs3s2 &
    HgetChildrenEqs3s2 & HgetBlocksEqs3s2 & HgetPaddrEqs3s2 & HgetAccPaddrEqs3s2 & HnotEnabled & Henabled &
    Hs2 & Hconsists2 & HnewIsBEs2 & HlookupNews2 & HcurrIsPDTs2 & HlookupCurrs2 & HsceaddrIsSCEs2 & HfirstIsBEs2
    & HnbFrees2 & HAFlagBlocks2 & HPDFlagBlocks2 & HlookupBlocks2 & HMPUCurr & Hpropss2s1 & Hs1 & Hconsists1 &
    HPDFlagBlocks1 & HlookupBlocks1 & Hpropss0).
  assert(HlookupBlockSces3: exists scentryBlock,
      lookup (CPaddr (blockToShareInCurrPartAddr + scoffset)) (memory s3) beqAddr = Some (SCE scentryBlock)).
  {
    unfold scentryNext in HnextBlocks3.
    destruct (lookup (CPaddr (blockToShareInCurrPartAddr + scoffset)) (memory s3) beqAddr);
      try(exfalso; congruence). destruct v; try(exfalso; congruence). exists s4. reflexivity.
  }
  destruct HlookupBlockSces3 as [scentryBlock HlookupBlockSces3].
  exists bentryShares2. exists (blockindex bentryShares2). exists scentryBlock.
  assert(HlookupBlocks3: lookup blockToShareInCurrPartAddr (memory s3) beqAddr = Some (BE bentryShares2)).
  {
    destruct blockToShareEnabled.
    - assert(Htriv: is_true true) by (unfold is_true; reflexivity). specialize(Henabled Htriv).
      destruct Henabled as [pdentryCurrs3 (Hs3 & HlookupCurrs3 & Henabled)]. rewrite Hs3. simpl.
      destruct (beqAddr currentPart blockToShareInCurrPartAddr) eqn:HbeqCurrBlock.
      {
        rewrite <-beqAddrTrue in HbeqCurrBlock. subst currentPart. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in HbeqCurrBlock. rewrite removeDupIdentity; intuition.
    - assert(Htriv: ~ is_true false) by (unfold is_true; intro Hcontra; congruence).
      specialize(HnotEnabled Htriv). subst s3. assumption.
  }
  destruct (beqAddr idNewSubblock blockToShareInCurrPartAddr) eqn:HbeqNewBlock.
  {
    rewrite <-beqAddrTrue in HbeqNewBlock. exfalso.
    assert(HnewIsFirstFree: pdentryFirstFreeSlot currentPart idNewSubblock s0) by intuition.
    assert(HAFlagBlocks0: bentryAFlag blockToShareInCurrPartAddr true s0) by intuition.
    assert(HfirstFree: FirstFreeSlotPointerIsBEAndFreeSlot s0)
        by (unfold consistency in *; unfold consistency1 in *; intuition).
    assert(HlookupCurrs0: lookup currentPart (memory s0) beqAddr = Some (PDT pdentryCurrs0)) by intuition.
    assert(HbeqFirstNull: firstfreeslot pdentryCurrs0 <> nullAddr).
    {
      intro Hcontra. assert(Hnull: nullAddrExists s2) by (unfold consistency1 in *; intuition).
      unfold isBE in HfirstIsBEs2. unfold nullAddrExists in Hnull. unfold isPADDR in Hnull.
      rewrite Hcontra in *. destruct (lookup nullAddr (memory s2) beqAddr); try(congruence).
      destruct v; congruence.
    }
    specialize(HfirstFree currentPart pdentryCurrs0 HlookupCurrs0 HbeqFirstNull).
    destruct HfirstFree as (_ & HfirstFree). unfold isFreeSlot in HfirstFree.
    unfold pdentryFirstFreeSlot in HnewIsFirstFree. rewrite HlookupCurrs0 in HnewIsFirstFree.
    rewrite <-HnewIsFirstFree in *. rewrite HbeqNewBlock in *.
    assert(HlookupBlocks0: lookup blockToShareInCurrPartAddr (memory s0) beqAddr = Some (BE bentryShares0))
        by intuition. unfold bentryAFlag in HAFlagBlocks0. rewrite HlookupBlocks0 in *.
    destruct (lookup (CPaddr (blockToShareInCurrPartAddr + sh1offset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence).
    destruct (lookup (CPaddr (blockToShareInCurrPartAddr + scoffset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). destruct HfirstFree as (_ & _ & _ & _ & _ & Hcontra & _). congruence.
  }
  destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) (CPaddr (blockToShareInCurrPartAddr + scoffset)))
    eqn:HbeqNewSceBlockSce.
  {
    rewrite <-beqAddrTrue in HbeqNewSceBlockSce. exfalso. rewrite <-beqAddrFalse in HbeqNewBlock.
    unfold CPaddr in HbeqNewSceBlockSce. unfold CPaddr in HlookupNewSces3.
    assert(HzeroIsNull: forall n Hhyp, {| p := 0; Hp := ADT.CPaddr_obligation_2 n Hhyp |} = nullAddr).
    {
      intros. unfold nullAddr. unfold CPaddr. destruct (Compare_dec.le_dec 0 maxAddr); try(lia).
      f_equal. apply proof_irrelevance.
    }
    destruct (Compare_dec.le_dec (idNewSubblock + scoffset) maxAddr).
    - unfold CPaddr in HlookupBlockSces3.
      destruct (Compare_dec.le_dec (blockToShareInCurrPartAddr + scoffset) maxAddr).
      + injection HbeqNewSceBlockSce as Hcontra. apply PeanoNat.Nat.add_cancel_r in Hcontra.
        contradict HbeqNewBlock. destruct idNewSubblock. destruct blockToShareInCurrPartAddr. simpl in Hcontra.
        subst p0. f_equal. apply proof_irrelevance.
      + assert(Hnull: nullAddrExists s3) by (unfold consistency1 in *; intuition).
        rewrite HzeroIsNull in HlookupBlockSces3. unfold nullAddrExists in Hnull. unfold isPADDR in Hnull.
        rewrite HlookupBlockSces3 in Hnull. congruence.
    - rewrite HzeroIsNull in HlookupNewSces3.
      assert(Hnull: nullAddrExists s3) by (unfold consistency1 in *; intuition).
      unfold nullAddrExists in Hnull. unfold isPADDR in Hnull. rewrite HlookupNewSces3 in Hnull. congruence.
  }
  assert(HlookupBlocks: lookup blockToShareInCurrPartAddr (memory s) beqAddr = Some (BE bentryShares2)).
  {
    rewrite Hs. simpl.
    destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) blockToShareInCurrPartAddr) eqn:HbeqNewSceBlock.
    {
      rewrite <-beqAddrTrue in HbeqNewSceBlock. rewrite HbeqNewSceBlock in *. exfalso; congruence.
    }
    rewrite <-beqAddrFalse in HbeqNewSceBlock. rewrite removeDupIdentity; intuition.
  }
  assert(HlookupBlockSces: lookup (CPaddr (blockToShareInCurrPartAddr + scoffset)) (memory s) beqAddr
                            = Some (SCE scentryBlock)).
  {
    rewrite Hs. simpl. rewrite HbeqNewSceBlockSce. rewrite <-beqAddrFalse in HbeqNewSceBlockSce.
    rewrite removeDupIdentity; intuition.
  }
  split. assumption. split. reflexivity. split. assumption.
  instantiate(1 := fun _ s => exists s4 s3 s2 s1 s0
      predCurrentNbFreeSlots
      sceaddr newFirstFreeSlotAddr
      scentry scentryNew scentryShares4
      pdentryCurrs0 pdentryInter0 pdentryCurrs2
      bentry bentry0 bentry1 bentry2 bentry3 bentry4 bentry5 bentry6 bentryShares0 bentryShares2,
        s = {|
              currentPartition := currentPartition s4;
              memory := add (CPaddr (blockToShareInCurrPartAddr + scoffset))
                          (SCE {| origin := origin scentryShares4; next := idNewSubblock |}) (memory s4) beqAddr
            |}
        /\ consistency1 s
        /\ lookup (CPaddr (blockToShareInCurrPartAddr + scoffset)) (memory s4) beqAddr = Some (SCE scentryShares4)
        /\ lookup blockToShareInCurrPartAddr (memory s4) beqAddr = Some (BE bentryShares2)
        /\ beqAddr idNewSubblock blockToShareInCurrPartAddr = false
        /\ beqAddr (CPaddr (idNewSubblock + scoffset)) (CPaddr (blockToShareInCurrPartAddr + scoffset)) = false
        /\ sceaddr = CPaddr (idNewSubblock + scoffset)
        (* Properties in state s4 *)
        /\ s4 = {|
              currentPartition := currentPartition s3;
              memory := add (CPaddr (idNewSubblock + scoffset))
                          (SCE {| origin := origin scentryNew; next := originalNextSubblock |})
                            (memory s3) beqAddr
            |}
        /\ consistency1 s4
        /\ ~ isFreeSlot blockToShareInCurrPartAddr s4
        /\ ~ isFreeSlot idNewSubblock s4
        (* Properties in state s3 *)
        /\ consistency1 s3
        /\ isPDT currentPart s3
        /\ isBE idNewSubblock s3
        /\ (forall partition, isPDT partition s3 = isPDT partition s2)
        /\ getKSEntries currentPart s3 = getKSEntries currentPart s2
        /\ scentryNext (CPaddr (blockToShareInCurrPartAddr + scoffset)) originalNextSubblock s3
        /\ lookup idNewSubblock (memory s3) beqAddr = Some (BE bentry6)
        /\ lookup (CPaddr (idNewSubblock + scoffset)) (memory s3) beqAddr = Some (SCE scentryNew)
        /\ (forall partition, partition <> currentPart -> isPDT partition s2
                              -> getPartitions partition s3 = getPartitions partition s2)
        /\ (forall partition, partition <> currentPart -> isPDT partition s2
                              -> getConfigPaddr partition s3 = getConfigPaddr partition s2)
        /\ (forall partition, partition <> currentPart -> isPDT partition s2
                            -> getAccessibleMappedBlocks partition s3 = getAccessibleMappedBlocks partition s2)
        /\ (forall partition, partition <> currentPart -> isPDT partition s2
                              -> getChildren partition s3 = getChildren partition s2)
        /\ (forall partition, partition <> currentPart -> isPDT partition s2
                              -> getMappedBlocks partition s3 = getMappedBlocks partition s2)
        /\ (forall partition, partition <> currentPart -> isPDT partition s2
                              -> getMappedPaddr partition s3 = getMappedPaddr partition s2)
        /\ (forall partition, partition <> currentPart -> isPDT partition s2
                              -> getAccessibleMappedPaddr partition s3 = getAccessibleMappedPaddr partition s2)
        /\ ((~ is_true blockToShareEnabled) -> s3 = s2)
        /\ (is_true blockToShareEnabled ->
                exists pdentry1,
                  s3 =
                  {|
                    currentPartition := currentPartition s2;
                    memory :=
                      add currentPart
                        (PDT
                           {|
                             structure := structure pdentryCurrs2;
                             firstfreeslot := firstfreeslot pdentryCurrs2;
                             nbfreeslots := nbfreeslots pdentryCurrs2;
                             nbprepare := nbprepare pdentryCurrs2;
                             parent := parent pdentryCurrs2;
                             MPU :=
                               addElementAt blockMPURegionNb blockToShareInCurrPartAddr 
                                 (MPU pdentryCurrs2) nullAddr;
                             vidtAddr := vidtAddr pdentryCurrs2
                           |}) (memory s2) beqAddr
                  |} /\
                  lookup currentPart (memory s3) beqAddr = Some (PDT pdentry1) /\
                  pdentry1 =
                  {|
                    structure := structure pdentryCurrs2;
                    firstfreeslot := firstfreeslot pdentryCurrs2;
                    nbfreeslots := nbfreeslots pdentryCurrs2;
                    nbprepare := nbprepare pdentryCurrs2;
                    parent := parent pdentryCurrs2;
                    MPU := addElementAt blockMPURegionNb blockToShareInCurrPartAddr (MPU pdentryCurrs2) nullAddr;
                    vidtAddr := vidtAddr pdentryCurrs2
                  |} /\ pdentryNbFreeSlots currentPart (nbfreeslots pdentryCurrs2) s3)
        (* Properties in state s2 *)
        /\ s2 =
                {|
                  currentPartition := currentPartition s1;
                  memory :=
                    add blockToShareInCurrPartAddr
                      (BE
                         (CBlockEntry (read bentryShares0) (write bentryShares0) (exec bentryShares0)
                            (present bentryShares0) (accessible bentryShares0) (blockindex bentryShares0)
                            (CBlock (startAddr (blockrange bentryShares0)) cutAddr))) (memory s1) beqAddr
                |}
        /\ consistency1 s2
        /\ isBE idNewSubblock s2
        /\ lookup idNewSubblock (memory s2) beqAddr = Some (BE bentry6)
        /\ isPDT currentPart s2
        /\ lookup currentPart (memory s2) beqAddr = Some (PDT pdentryCurrs2)
        /\ isSCE sceaddr s2
        /\ isBE (firstfreeslot pdentryCurrs0) s2
        /\ pdentryNbFreeSlots currentPart predCurrentNbFreeSlots s2
        /\ bentryAFlag blockToShareInCurrPartAddr true s2
        /\ sh1entryPDflag (CPaddr (blockToShareInCurrPartAddr + sh1offset)) false s2
        /\ lookup blockToShareInCurrPartAddr (memory s2) beqAddr = Some (BE bentryShares2)
        /\ (exists MPUlist,
              pdentryMPU currentPart MPUlist s2
              /\ (blockMPURegionNb = CIndex defaultidx /\ (~ In blockToShareInCurrPartAddr MPUlist)
                    \/ nth blockMPURegionNb MPUlist nullAddr = blockToShareInCurrPartAddr))
        /\ (exists optionfreeslotslist s4 n0 n1 n2 nbleft,
                nbleft = CIndex (nbFreeSlots - 1) /\
                nbleft < maxIdx /\
                s1 =
                {|
                  currentPartition := currentPartition s0;
                  memory :=
                    add sceaddr (SCE {| origin := blockOrigin; next := next scentry |}) (memory s4) beqAddr
                |} /\
                optionfreeslotslist = getFreeSlotsListRec n1 newFirstFreeSlotAddr s4 nbleft /\
                getFreeSlotsListRec n2 newFirstFreeSlotAddr s1 nbleft = optionfreeslotslist /\
                optionfreeslotslist = getFreeSlotsListRec n0 newFirstFreeSlotAddr s0 nbleft /\
                n0 <= n1 /\
                nbleft < n0 /\
                n1 <= n2 /\
                nbleft < n2 /\
                n2 <= maxIdx + 1 /\
                (wellFormedFreeSlotsList optionfreeslotslist = False -> False) /\
                NoDup (filterOptionPaddr optionfreeslotslist) /\
                (~ In (firstfreeslot pdentryCurrs0) (filterOptionPaddr optionfreeslotslist)) /\
                (exists optionentrieslist : list optionPaddr,
                   optionentrieslist = getKSEntries currentPart s4 /\
                   getKSEntries currentPart s2 = optionentrieslist /\
                   optionentrieslist = getKSEntries currentPart s0 /\
                   In (firstfreeslot pdentryCurrs0) (filterOptionPaddr optionentrieslist)) /\
                isPDT multiplexer s2 /\
                getPartitions multiplexer s4 = getPartitions multiplexer s0 /\
                getPartitions multiplexer s1 = getPartitions multiplexer s4 /\
                getChildren currentPart s4 = getChildren currentPart s0 /\
                getChildren currentPart s1 = getChildren currentPart s4 /\
                getConfigBlocks currentPart s4 = getConfigBlocks currentPart s0 /\
                getConfigBlocks currentPart s1 = getConfigBlocks currentPart s4 /\
                getConfigPaddr currentPart s4 = getConfigPaddr currentPart s0 /\
                getConfigPaddr currentPart s1 = getConfigPaddr currentPart s4 /\
                (forall block : paddr,
                 In block (getMappedBlocks currentPart s2) <->
                 firstfreeslot pdentryCurrs0 = block \/ In block (getMappedBlocks currentPart s0)) /\
                ((forall addr : paddr,
                    In addr (getMappedPaddr currentPart s2) <-> In addr (getMappedPaddr currentPart s0))
                  /\ length (getMappedPaddr currentPart s2) = length (getMappedPaddr currentPart s0)) /\
                (forall block : paddr,
                 In block (getAccessibleMappedBlocks currentPart s2) <->
                 firstfreeslot pdentryCurrs0 = block \/ In block (getAccessibleMappedBlocks currentPart s0)) /\
                (forall addr : paddr,
                 In addr (getAccessibleMappedPaddr currentPart s2) <->
                 In addr
                   (getAllPaddrBlock (startAddr (blockrange bentry6)) (endAddr (blockrange bentry6)) ++
                    getAccessibleMappedPaddr currentPart s0)) /\
                (forall partition : paddr,
                 (partition = currentPart -> False) ->
                 isPDT partition s0 -> getKSEntries partition s2 = getKSEntries partition s0) /\
                (forall partition : paddr,
                 (partition = currentPart -> False) ->
                 isPDT partition s0 -> getMappedPaddr partition s2 = getMappedPaddr partition s0) /\
                (forall partition : paddr,
                 (partition = currentPart -> False) ->
                 isPDT partition s0 -> getConfigPaddr partition s2 = getConfigPaddr partition s0) /\
                (forall partition : paddr,
                 (partition = currentPart -> False) ->
                 isPDT partition s0 -> getPartitions partition s2 = getPartitions partition s0) /\
                (forall partition : paddr,
                 (partition = currentPart -> False) ->
                 isPDT partition s0 -> getChildren partition s2 = getChildren partition s0) /\
                (forall partition : paddr,
                 (partition = currentPart -> False) ->
                 isPDT partition s0 -> getMappedBlocks partition s2 = getMappedBlocks partition s0) /\
                (forall partition : paddr,
                 (partition = currentPart -> False) ->
                 isPDT partition s0 ->
                 getAccessibleMappedBlocks partition s2 = getAccessibleMappedBlocks partition s0) /\
                (forall partition : paddr,
                 (partition = currentPart -> False) ->
                 isPDT partition s0 ->
                 getAccessibleMappedPaddr partition s2 = getAccessibleMappedPaddr partition s0) /\
                (forall partition : paddr, isPDT partition s2 = isPDT partition s0))
        (* Properties in state s1 *)
        /\ s1 =
                {|
                  currentPartition := currentPartition s0;
                  memory :=
                    add sceaddr (SCE {| origin := blockOrigin; next := next scentry |})
                      (add idNewSubblock
                         (BE
                            (CBlockEntry (read bentry5) (write bentry5) blockX (present bentry5)
                               (accessible bentry5) (blockindex bentry5) (blockrange bentry5)))
                         (add idNewSubblock
                            (BE
                               (CBlockEntry (read bentry4) blockW (exec bentry4) (present bentry4)
                                  (accessible bentry4) (blockindex bentry4) (blockrange bentry4)))
                            (add idNewSubblock
                               (BE
                                  (CBlockEntry blockR (write bentry3) (exec bentry3) (present bentry3)
                                     (accessible bentry3) (blockindex bentry3) (blockrange bentry3)))
                               (add idNewSubblock
                                  (BE
                                     (CBlockEntry (read bentry2) (write bentry2) (exec bentry2) 
                                        (present bentry2) true (blockindex bentry2) (blockrange bentry2)))
                                  (add idNewSubblock
                                     (BE
                                        (CBlockEntry (read bentry1) (write bentry1) (exec bentry1) true
                                           (accessible bentry1) (blockindex bentry1) (blockrange bentry1)))
                                     (add idNewSubblock
                                        (BE
                                           (CBlockEntry (read bentry0) (write bentry0) 
                                              (exec bentry0) (present bentry0) (accessible bentry0)
                                              (blockindex bentry0)
                                              (CBlock (startAddr (blockrange bentry0)) blockEndAddr)))
                                        (add idNewSubblock
                                           (BE
                                              (CBlockEntry (read bentry) (write bentry) 
                                                 (exec bentry) (present bentry) (accessible bentry)
                                                 (blockindex bentry)
                                                 (CBlock cutAddr (endAddr (blockrange bentry)))))
                                           (add currentPart
                                              (PDT
                                                 {|
                                                   structure := structure pdentryInter0;
                                                   firstfreeslot := firstfreeslot pdentryInter0;
                                                   nbfreeslots := predCurrentNbFreeSlots;
                                                   nbprepare := nbprepare pdentryInter0;
                                                   parent := parent pdentryInter0;
                                                   MPU := MPU pdentryInter0;
                                                   vidtAddr := vidtAddr pdentryInter0
                                                 |})
                                              (add currentPart
                                                 (PDT
                                                    {|
                                                      structure := structure pdentryCurrs0;
                                                      firstfreeslot := newFirstFreeSlotAddr;
                                                      nbfreeslots := nbfreeslots pdentryCurrs0;
                                                      nbprepare := nbprepare pdentryCurrs0;
                                                      parent := parent pdentryCurrs0;
                                                      MPU := MPU pdentryCurrs0;
                                                      vidtAddr := vidtAddr pdentryCurrs0
                                                    |}) (memory s0) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr)
                                  beqAddr) beqAddr) beqAddr) beqAddr) beqAddr
                |}
        /\ consistency1 s1
        /\ sh1entryPDflag (CPaddr (blockToShareInCurrPartAddr + sh1offset)) false s1
        /\ lookup blockToShareInCurrPartAddr (memory s1) beqAddr = Some (BE bentryShares0)
        (* Properties in state s0 *)
        /\ kernelDataIsolation s0
        /\ verticalSharing s0
        /\ partitionsIsolation s0
        /\ consistency s0
        /\ isPDT currentPart s0
        /\ lookup currentPart (memory s0) beqAddr = Some (PDT pdentryCurrs0)
        /\ currentPart = currentPartition s0
        /\ pdentryNbFreeSlots currentPart nbFreeSlots s0
        /\ pdentryFirstFreeSlot currentPart idNewSubblock s0
        /\ isSCE sceaddr s0
        /\ lookup blockToShareInCurrPartAddr (memory s0) beqAddr = Some (BE bentryShares0)
        /\ bentryEndAddr blockToShareInCurrPartAddr blockEndAddr s0
        /\ bentryEndAddr blockToShareInCurrPartAddr blockToCutEndAddr s0
        /\ bentryStartAddr blockToShareInCurrPartAddr blockToCutStartAddr s0
        /\ bentryXFlag blockToShareInCurrPartAddr blockX s0
        /\ bentryRFlag blockToShareInCurrPartAddr blockR s0
        /\ bentryWFlag blockToShareInCurrPartAddr blockW s0
        /\ bentryPFlag blockToShareInCurrPartAddr true s0
        /\ bentryAFlag blockToShareInCurrPartAddr true s0
        /\ isBE (firstfreeslot pdentryCurrs0) s0
        /\ bentryEndAddr (firstfreeslot pdentryCurrs0) newFirstFreeSlotAddr s0
        /\ lookup idNewSubblock (memory s0) beqAddr = Some (BE bentry)
        /\ In blockToShareInCurrPartAddr (getMappedBlocks currentPart s0)
        /\ scentryOrigin (CPaddr (blockToShareInCurrPartAddr + scoffset)) blockOrigin s0
        /\ lookup sceaddr (memory s0) beqAddr = Some (SCE scentry)
        /\ (exists sh1entry sh1entryaddr,
                    lookup sh1entryaddr (memory s0) beqAddr = Some (SHE sh1entry)
                    /\ sh1entryPDchild sh1entryaddr PDChildAddr s0
                    /\ sh1entryAddr blockToShareInCurrPartAddr sh1entryaddr s0)
        /\ (forall blockInParentPartitionAddr,
             In blockInParentPartitionAddr (getMappedBlocks (parent pdentryCurrs0) s0)
             -> bentryStartAddr blockInParentPartitionAddr blockToCutStartAddr s0
             -> bentryEndAddr blockInParentPartitionAddr blockToCutEndAddr s0
             -> bentryAFlag blockInParentPartitionAddr false s0)
        (* Other properties *)
        /\ bentry6 = CBlockEntry (read bentry5) (write bentry5) blockX (present bentry5)
                          (accessible bentry5) (blockindex bentry5) (blockrange bentry5)
        /\ bentry5 = CBlockEntry (read bentry4) blockW (exec bentry4) (present bentry4)
                          (accessible bentry4) (blockindex bentry4) (blockrange bentry4)
        /\ bentry4 = CBlockEntry blockR (write bentry3) (exec bentry3) (present bentry3)
                          (accessible bentry3) (blockindex bentry3) (blockrange bentry3)
        /\ bentry3 = CBlockEntry (read bentry2) (write bentry2) (exec bentry2) (present bentry2) true
                          (blockindex bentry2) (blockrange bentry2)
        /\ bentry2 = CBlockEntry (read bentry1) (write bentry1) (exec bentry1) true (accessible bentry1)
                          (blockindex bentry1) (blockrange bentry1)
        /\ bentry1 = CBlockEntry (read bentry0) (write bentry0) (exec bentry0) (present bentry0)
                          (accessible bentry0) (blockindex bentry0)
                          (CBlock (startAddr (blockrange bentry0)) blockEndAddr)
        /\ bentry0 = CBlockEntry (read bentry) (write bentry) (exec bentry) (present bentry)
                          (accessible bentry) (blockindex bentry) (CBlock cutAddr (endAddr (blockrange bentry)))
        /\ false = StateLib.Paddr.leb cutAddr blockToCutStartAddr
        /\ false = StateLib.Paddr.leb blockToCutEndAddr cutAddr
        /\ StateLib.Paddr.subPaddr cutAddr blockToCutStartAddr = Some subblock1Size
        /\ StateLib.Paddr.subPaddr blockToCutEndAddr cutAddr = Some subblock2Size
        /\ isBlock1TooSmall = StateLib.Index.ltb subblock1Size Constants.minBlockSize
        /\ isBlock2TooSmall = StateLib.Index.ltb subblock2Size Constants.minBlockSize
        /\ pdentryInter0 = {|
                             structure := structure pdentryCurrs0;
                             firstfreeslot := newFirstFreeSlotAddr;
                             nbfreeslots := nbfreeslots pdentryCurrs0;
                             nbprepare := nbprepare pdentryCurrs0;
                             parent := parent pdentryCurrs0;
                             MPU := MPU pdentryCurrs0;
                             vidtAddr := vidtAddr pdentryCurrs0
                           |}
        /\ beqAddr nullAddr PDChildAddr = true).
  simpl. exists s. exists s3. exists s2. exists s1. exists s0. exists predCurrentNbFreeSlots. exists sceaddr.
  exists newFirstFreeSlotAddr. exists scentry. exists scentryNew. exists scentryBlock. exists pdentryCurrs0.
  exists pdentryInter0. exists pdentryCurrs2. exists bentry. exists bentry0. exists bentry1. exists bentry2.
  exists bentry3. exists bentry4. exists bentry5. exists bentry6. exists bentryShares0. exists bentryShares2.
  intuition. set(newS := {|
                           currentPartition := currentPartition s;
                           memory :=
                             add (CPaddr (blockToShareInCurrPartAddr + scoffset))
                               (SCE {| origin := origin scentryBlock; next := idNewSubblock |}) 
                               (memory s) beqAddr
                         |}).
  assert(HwellFormedShadow: wellFormedShadowCutIfBlockEntry s) by (unfold consistency1 in *; intuition).
  assert(HblockIsBEs: isBE blockToShareInCurrPartAddr s) by (unfold isBE; rewrite HlookupBlocks; trivial).
  specialize(HwellFormedShadow blockToShareInCurrPartAddr HblockIsBEs).
  destruct HwellFormedShadow as [sce (HsceIsSCE & Hsce)]. subst sce.

  assert(nullAddrExists newS).
  { (* BEGIN nullAddrExists newS *)
    assert(Hcons0: nullAddrExists s) by (unfold consistency1 in *; intuition).
    unfold nullAddrExists in *. unfold isPADDR in *. simpl.
    destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) nullAddr) eqn:HbeqBlockSceNull.
    {
      rewrite <-beqAddrTrue in HbeqBlockSceNull. rewrite HbeqBlockSceNull in *.
      unfold isSCE in HsceIsSCE. destruct (lookup nullAddr (memory s) beqAddr); try(exfalso; congruence).
      destruct v; congruence.
    }
    rewrite <-beqAddrFalse in HbeqBlockSceNull. rewrite removeDupIdentity; intuition.
    (* END nullAddrExists *)
  }

  assert(wellFormedFstShadowIfBlockEntry newS).
  { (* BEGIN wellFormedFstShadowIfBlockEntry newS *)
    assert(Hcons0: wellFormedFstShadowIfBlockEntry s) by (unfold consistency1 in *; intuition).
    intros pa HpaIsBE.
    assert(HpaIsBEs: isBE pa s).
    {
      unfold isBE in HpaIsBE. simpl in HpaIsBE.
      destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) pa) eqn:HbeqBlockScePa;
          try(exfalso; congruence).
      rewrite <-beqAddrFalse in HbeqBlockScePa. rewrite removeDupIdentity in HpaIsBE; intuition.
    }
    specialize(Hcons0 pa HpaIsBEs). unfold isSHE in *. simpl.
    destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) (CPaddr (pa + sh1offset)))
        eqn:HbeqBlockScePaSh1.
    {
      unfold isSCE in HsceIsSCE. rewrite <-beqAddrTrue in HbeqBlockScePaSh1. rewrite HbeqBlockScePaSh1 in *.
      destruct (lookup (CPaddr (pa + sh1offset)) (memory s) beqAddr); try(congruence). destruct v; congruence.
    }
    rewrite <-beqAddrFalse in HbeqBlockScePaSh1. rewrite removeDupIdentity; intuition.
    (* END wellFormedFstShadowIfBlockEntry *)
  }

  assert(PDTIfPDFlag newS).
  { (* BEGIN PDTIfPDFlag newS *)
    assert(Hcons0: PDTIfPDFlag s) by (unfold consistency1 in *; intuition).
    intros idPDchild sh1entryaddr (HcheckChild & Hsh1entry).
    assert(HcheckChilds: true = checkChild idPDchild s sh1entryaddr
                          /\ sh1entryAddr idPDchild sh1entryaddr s).
    {
      unfold checkChild in *. unfold sh1entryAddr in *. simpl in HcheckChild. simpl in Hsh1entry.
      destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) idPDchild) eqn:HbeqBlockSceId;
          try(exfalso; congruence). rewrite <-beqAddrFalse in HbeqBlockSceId.
      rewrite removeDupIdentity in Hsh1entry; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity in HcheckChild; try(apply not_eq_sym; assumption). split; try(assumption).
      destruct (lookup idPDchild (memory s) beqAddr); try(congruence). destruct v; try(congruence).
      destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) sh1entryaddr) eqn:HbeqBlockSceIdSh1;
          try(exfalso; congruence). rewrite <-beqAddrFalse in HbeqBlockSceIdSh1.
      rewrite removeDupIdentity in HcheckChild; intuition.
    }
    specialize(Hcons0 idPDchild sh1entryaddr HcheckChilds). destruct Hcons0 as (HAFlag & HPFlag & [startaddr
      (Hstart & HentryStart)]).
    assert(HlookupEq: lookup idPDchild (memory newS) beqAddr = lookup idPDchild (memory s) beqAddr).
    {
      simpl. unfold sh1entryAddr in Hsh1entry. simpl in Hsh1entry.
      destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) idPDchild) eqn:HbeqBlockSceId;
          try(exfalso; congruence). rewrite <-beqAddrFalse in HbeqBlockSceId.
      rewrite removeDupIdentity; intuition.
    }
    unfold bentryAFlag. unfold bentryPFlag. unfold bentryStartAddr. unfold entryPDT in *. rewrite HlookupEq.
    split. assumption. split. assumption. exists startaddr. split. assumption.
    destruct (lookup idPDchild (memory s) beqAddr); try(congruence). destruct v; try(congruence). simpl.
    destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) (startAddr (blockrange b)))
        eqn:HbeqBlockSceStart.
    {
      rewrite <-beqAddrTrue in HbeqBlockSceStart. unfold isSCE in HsceIsSCE. rewrite HbeqBlockSceStart in *.
      destruct (lookup (startAddr (blockrange b)) (memory s) beqAddr); try(congruence). destruct v; congruence.
    }
    rewrite <-beqAddrFalse in HbeqBlockSceStart. rewrite removeDupIdentity; intuition.
    (* END PDTIfPDFlag *)
  }

  assert(AccessibleNoPDFlag newS).
  { (* BEGIN AccessibleNoPDFlag newS *)
    assert(Hcons0: AccessibleNoPDFlag s) by (unfold consistency1 in *; intuition).
    intros block sh1entryaddr HblockIsBE Hsh1 HAFlag.
    assert(HlookupEq: lookup block (memory newS) beqAddr = lookup block (memory s) beqAddr).
    {
      unfold isBE in HblockIsBE. simpl. simpl in HblockIsBE.
      destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) block) eqn:HbeqBlockSceBlock;
          try(exfalso; congruence). rewrite <-beqAddrFalse in HbeqBlockSceBlock.
      rewrite removeDupIdentity; intuition.
    }
    unfold isBE in HblockIsBE. unfold sh1entryAddr in Hsh1. unfold bentryAFlag in HAFlag.
    rewrite HlookupEq in *. specialize(Hcons0 block sh1entryaddr HblockIsBE Hsh1 HAFlag).
    unfold sh1entryPDflag in *. simpl.
    destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) sh1entryaddr) eqn:HbeqBlockSceBlockSh1.
    {
      unfold isSCE in HsceIsSCE. rewrite <-beqAddrTrue in HbeqBlockSceBlockSh1. rewrite HbeqBlockSceBlockSh1 in *.
      destruct (lookup sh1entryaddr (memory s) beqAddr); try(congruence). destruct v; congruence.
    }
    rewrite <-beqAddrFalse in HbeqBlockSceBlockSh1. rewrite removeDupIdentity; intuition.
    (* END AccessibleNoPDFlag *)
  }

  assert(FirstFreeSlotPointerIsBEAndFreeSlot newS).
  { (* BEGIN FirstFreeSlotPointerIsBEAndFreeSlot newS *)
    assert(Hcons0: FirstFreeSlotPointerIsBEAndFreeSlot s) by (unfold consistency1 in *; intuition).
    intros pd pdentryPd HlookupPd HbeqFirstFreeNull.
    assert(HlookupPds: lookup pd (memory s) beqAddr = Some (PDT pdentryPd)).
    {
      simpl in HlookupPd.
      destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) pd) eqn:HbeqBlockScePd;
          try(exfalso; congruence).
      rewrite <-beqAddrFalse in HbeqBlockScePd. rewrite removeDupIdentity in HlookupPd; intuition.
    }
    specialize(Hcons0 pd pdentryPd HlookupPds HbeqFirstFreeNull). destruct Hcons0 as (_ & HfirstIsFree).
    destruct (beqAddr blockToShareInCurrPartAddr (firstfreeslot pdentryPd)) eqn:HbeqBlockFirst.
    {
      rewrite <-beqAddrTrue in HbeqBlockFirst. subst blockToShareInCurrPartAddr. exfalso; congruence.
    }
    unfold isBE. unfold isFreeSlot in *. simpl.
    destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) (firstfreeslot pdentryPd))
        eqn:HbeqBlockSceFirst.
    {
      unfold isSCE in HsceIsSCE. rewrite <-beqAddrTrue in HbeqBlockSceFirst. rewrite HbeqBlockSceFirst in *.
      exfalso. destruct (lookup (firstfreeslot pdentryPd) (memory s) beqAddr); try(congruence).
      destruct v; congruence.
    }
    rewrite <-beqAddrFalse in HbeqBlockSceFirst. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
    destruct (lookup (firstfreeslot pdentryPd) (memory s) beqAddr) eqn:HlookupFirst; try(exfalso; congruence).
    destruct v; try(exfalso; congruence). split. trivial.
    destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset))
                      (CPaddr (firstfreeslot pdentryPd + sh1offset))) eqn:HbeqBlockSceFirstSh1.
    {
      rewrite <-beqAddrTrue in HbeqBlockSceFirstSh1. rewrite <-HbeqBlockSceFirstSh1 in *.
      unfold isSCE in HsceIsSCE.
      destruct (lookup (CPaddr (blockToShareInCurrPartAddr + scoffset)) (memory s) beqAddr); try(congruence).
      destruct v; congruence.
    }
    rewrite <-beqAddrFalse in HbeqBlockSceFirstSh1. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
    destruct (lookup (CPaddr (firstfreeslot pdentryPd + sh1offset)) (memory s) beqAddr); try(congruence).
    destruct v; try(congruence).
    destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset))
                      (CPaddr (firstfreeslot pdentryPd + scoffset))) eqn:HbeqBlockSceFirstSce.
    {
      rewrite <-beqAddrTrue in HbeqBlockSceFirstSce. rewrite <-HbeqBlockSceFirstSce in *. exfalso.
      rewrite <-beqAddrFalse in HbeqBlockFirst. unfold CPaddr in HbeqBlockSceFirstSce.
      destruct (Compare_dec.le_dec (blockToShareInCurrPartAddr + scoffset) maxAddr) eqn:HleBlockSceMax.
      + destruct (Compare_dec.le_dec (firstfreeslot pdentryPd + scoffset) maxAddr).
        * injection HbeqBlockSceFirstSce as HsceEq. contradict HbeqBlockFirst.
          destruct blockToShareInCurrPartAddr. destruct (firstfreeslot pdentryPd).  simpl in HsceEq.
          assert(p = p0) by lia. subst p0. f_equal. apply proof_irrelevance.
        * assert(HbeqBlockSceNull: CPaddr (blockToShareInCurrPartAddr + scoffset) = nullAddr).
          {
            unfold nullAddr. injection HbeqBlockSceFirstSce as HbeqBlockSceNull. rewrite HbeqBlockSceNull.
            reflexivity.
          }
          assert(Hnull: nullAddrExists s) by (unfold consistency1 in *; intuition).
          unfold nullAddrExists in Hnull. unfold isPADDR in Hnull. rewrite HbeqBlockSceNull in *.
          rewrite HlookupBlockSces in Hnull. congruence.
      + assert(HbeqBlockScenull: CPaddr (blockToShareInCurrPartAddr + scoffset) = nullAddr).
        {
          unfold nullAddr. unfold CPaddr. rewrite HleBlockSceMax.
          destruct (Compare_dec.le_dec 0 maxAddr); try(lia). f_equal. apply proof_irrelevance.
        }
        assert(Hnull: nullAddrExists s) by (unfold consistency1 in *; intuition).
        unfold nullAddrExists in Hnull. unfold isPADDR in Hnull. rewrite HbeqBlockScenull in *.
        rewrite HlookupBlockSces in Hnull. congruence.
    }
    rewrite <-beqAddrFalse in HbeqBlockSceFirstSce. rewrite removeDupIdentity; intuition.
    (* END FirstFreeSlotPointerIsBEAndFreeSlot *)
  }

  assert(multiplexerIsPDT newS).
  { (* BEGIN multiplexerIsPDT newS *)
    assert(Hcons0: multiplexerIsPDT s) by (unfold consistency1 in *; intuition).
    unfold multiplexerIsPDT in *. unfold isPDT in *. simpl.
    destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) multiplexer) eqn:HbeqBlockSceMult.
    {
      rewrite <-beqAddrTrue in HbeqBlockSceMult. rewrite HbeqBlockSceMult in *. unfold isSCE in HsceIsSCE.
      destruct (lookup multiplexer (memory s) beqAddr); try(congruence). destruct v; congruence.
    }
    rewrite <-beqAddrFalse in HbeqBlockSceMult. rewrite removeDupIdentity; intuition.
    (* END multiplexerIsPDT *)
  }

  assert(HcurrPartEq: currentPartition newS = currentPartition s).
  { simpl. reflexivity. }

  assert(HgetPartsEq: getPartitions multiplexer newS = getPartitions multiplexer s).
  {
    apply getPartitionsEqSCE; try(assumption). unfold consistency1 in *; intuition.
    unfold consistency1 in *; intuition.
  }

  assert(currentPartitionInPartitionsList newS).
  { (* BEGIN currentPartitionInPartitionsList newS *)
    assert(Hcons0: currentPartitionInPartitionsList s) by (unfold consistency1 in *; intuition).
    unfold currentPartitionInPartitionsList. rewrite HcurrPartEq. rewrite HgetPartsEq. assumption.
    (* END currentPartitionInPartitionsList *)
  }

  assert(wellFormedShadowCutIfBlockEntry newS).
  { (* BEGIN wellFormedShadowCutIfBlockEntry newS *)
    assert(Hcons0: wellFormedShadowCutIfBlockEntry s) by (unfold consistency1 in *; intuition).
    intros block HblockIsBE. clear HblockIsBEs.
    assert(HblockIsBEs: isBE block s).
    {
      unfold isBE in HblockIsBE. simpl in HblockIsBE.
      destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) block) eqn:HbeqBlockSceBlock;
          try(exfalso; congruence).
      rewrite <-beqAddrFalse in HbeqBlockSceBlock. rewrite removeDupIdentity in HblockIsBE; intuition.
    }
    specialize(Hcons0 block HblockIsBEs). destruct Hcons0 as [sce (HsceIsSCEBis & Hsce)]. exists sce.
    split; try(assumption). unfold isSCE. simpl.
    destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) sce) eqn:HbeqBlockSceSce; try(trivial).
    rewrite <-beqAddrFalse in HbeqBlockSceSce. rewrite removeDupIdentity; intuition.
    (* END wellFormedShadowCutIfBlockEntry *)
  }

  assert(BlocksRangeFromKernelStartIsBE newS).
  { (* BEGIN BlocksRangeFromKernelStartIsBE newS *)
    assert(Hcons0: BlocksRangeFromKernelStartIsBE s) by (unfold consistency1 in *; intuition).
    intros kernel idx HkernIsKS HidxBounded.
    assert(HkernIsKSs: isKS kernel s).
    {
      unfold isKS in HkernIsKS. simpl in HkernIsKS.
      destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) kernel) eqn:HbeqBlockSceKern;
          try(exfalso; congruence). rewrite <-beqAddrFalse in HbeqBlockSceKern.
      rewrite removeDupIdentity in HkernIsKS; intuition.
    }
    specialize(Hcons0 kernel idx HkernIsKSs HidxBounded). unfold isBE in *. simpl.
    destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) (CPaddr (kernel + idx)))
        eqn:HbeqBlockSceKernIdx.
    {
      rewrite <-beqAddrTrue in HbeqBlockSceKernIdx. rewrite HbeqBlockSceKernIdx in *.
      rewrite HlookupBlockSces in Hcons0. congruence.
    }
    rewrite <-beqAddrFalse in HbeqBlockSceKernIdx. rewrite removeDupIdentity; intuition.
    (* END BlocksRangeFromKernelStartIsBE *)
  }

  assert(KernelStructureStartFromBlockEntryAddrIsKS newS).
  { (* BEGIN KernelStructureStartFromBlockEntryAddrIsKS newS *)
    assert(Hcons0: KernelStructureStartFromBlockEntryAddrIsKS s) by (unfold consistency1 in *; intuition).
    intros block idx HblockIsBE Hblockidx.
    assert(HlookupEq: lookup block (memory newS) beqAddr = lookup block (memory s) beqAddr).
    {
      unfold isBE in HblockIsBE. simpl. simpl in HblockIsBE.
      destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) block) eqn:HbeqBlockSceBlock;
          try(exfalso; congruence). rewrite <-beqAddrFalse in HbeqBlockSceBlock.
      rewrite removeDupIdentity; intuition.
    }
    unfold isBE in HblockIsBE. unfold bentryBlockIndex in Hblockidx. rewrite HlookupEq in *.
    specialize(Hcons0 block idx HblockIsBE Hblockidx). unfold isKS in *. simpl.
    destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) (CPaddr (block - idx)))
      eqn:HbeqBlockSceBlockMIdx.
    {
      rewrite <-beqAddrTrue in HbeqBlockSceBlockMIdx. rewrite HbeqBlockSceBlockMIdx in *.
      rewrite HlookupBlockSces in Hcons0; congruence.
    }
    rewrite <-beqAddrFalse in HbeqBlockSceBlockMIdx. rewrite removeDupIdentity; intuition.
    (* END KernelStructureStartFromBlockEntryAddrIsKS *)
  }

  assert(sh1InChildLocationIsBE newS).
  { (* BEGIN sh1InChildLocationIsBE newS *)
    assert(Hcons0: sh1InChildLocationIsBE s) by (unfold consistency1 in *; intuition).
    intros sh1entryaddr sh1entry HlookupSh1 HbeqChildLocNull.
    assert(HlookupSh1s: lookup sh1entryaddr (memory s) beqAddr = Some (SHE sh1entry)).
    {
      simpl in HlookupSh1. destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) sh1entryaddr)
          eqn:HbeqBlockSceSh1; try(exfalso; congruence). rewrite <-beqAddrFalse in HbeqBlockSceSh1.
      rewrite removeDupIdentity in HlookupSh1; intuition.
    }
    specialize(Hcons0 sh1entryaddr sh1entry HlookupSh1s HbeqChildLocNull).
    unfold isBE in *. simpl.
    destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) (inChildLocation sh1entry))
        eqn:HbeqBlockSceChildLoc.
    {
      rewrite <-beqAddrTrue in HbeqBlockSceChildLoc. rewrite HbeqBlockSceChildLoc in *.
      rewrite HlookupBlockSces in Hcons0; congruence.
    }
    rewrite <-beqAddrFalse in HbeqBlockSceChildLoc. rewrite removeDupIdentity; intuition.
    (* END sh1InChildLocationIsBE *)
  }

  assert(StructurePointerIsKS newS).
  { (* BEGIN StructurePointerIsKS newS *)
    assert(Hcons0: StructurePointerIsKS s) by (unfold consistency1 in *; intuition).
    intros entryaddr entry HlookupEntry HbeqStructNull.
    assert(HlookupEntrys: lookup entryaddr (memory s) beqAddr = Some (PDT entry)).
    {
      simpl in HlookupEntry. destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) entryaddr)
          eqn:HbeqBlockSceEntry; try(exfalso; congruence). rewrite <-beqAddrFalse in HbeqBlockSceEntry.
      rewrite removeDupIdentity in HlookupEntry; intuition.
    }
    specialize(Hcons0 entryaddr entry HlookupEntrys HbeqStructNull). unfold isKS in *. simpl.
    destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) (structure entry)) eqn:HbeqBlockSceStruct.
    {
      rewrite <-beqAddrTrue in HbeqBlockSceStruct. rewrite HbeqBlockSceStruct in *.
      rewrite HlookupBlockSces in Hcons0. congruence.
    }
    rewrite <-beqAddrFalse in HbeqBlockSceStruct. rewrite removeDupIdentity; intuition.
    (* END StructurePointerIsKS *)
  }

  assert(NextKSIsKS newS).
  { (* BEGIN NextKSIsKS newS *)
    assert(Hcons0: NextKSIsKS s) by (unfold consistency1 in *; intuition).
    intros kernel nextKSaddr nextKS HkernIsKS HnextAddr HnextKS HbeqNextNull.
    assert(HlookupEq: lookup kernel (memory newS) beqAddr = lookup kernel (memory s) beqAddr).
    {
      unfold isKS in HkernIsKS. simpl in HkernIsKS. simpl.
      destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) kernel) eqn:HbeqBlockSceKern;
          try(exfalso; congruence). rewrite <-beqAddrFalse in HbeqBlockSceKern.
      rewrite removeDupIdentity; intuition.
    }
    unfold isKS in HkernIsKS. unfold nextKSAddr in HnextAddr. rewrite HlookupEq in *.
    assert(HnextKSs: nextKSentry nextKSaddr nextKS s).
    {
      unfold nextKSentry in *. simpl in HnextKS.
      destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) nextKSaddr) eqn:HbeqBlockSceNextAddr;
          try(exfalso; congruence). rewrite <-beqAddrFalse in HbeqBlockSceNextAddr.
      rewrite removeDupIdentity in HnextKS; intuition.
    }
    specialize(Hcons0 kernel nextKSaddr nextKS HkernIsKS HnextAddr HnextKSs HbeqNextNull). unfold isKS in *.
    simpl. destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) nextKS) eqn:HbeqBlockSceNextKS.
    {
      rewrite <-beqAddrTrue in HbeqBlockSceNextKS. rewrite HbeqBlockSceNextKS in *.
      rewrite HlookupBlockSces in Hcons0. congruence.
    }
    rewrite <-beqAddrFalse in HbeqBlockSceNextKS. rewrite removeDupIdentity; intuition.
    (* END NextKSIsKS *)
  }

  assert(NextKSOffsetIsPADDR newS).
  { (* BEGIN NextKSOffsetIsPADDR newS *)
    assert(Hcons0: NextKSOffsetIsPADDR s) by (unfold consistency1 in *; intuition).
    intros kernel nextAddr HkernIsKS HnextAddr.
    assert(HlookupEq: lookup kernel (memory newS) beqAddr = lookup kernel (memory s) beqAddr).
    {
      unfold isKS in HkernIsKS. simpl in HkernIsKS. simpl.
      destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) kernel) eqn:HbeqBlockSceKern;
          try(exfalso; congruence). rewrite <-beqAddrFalse in HbeqBlockSceKern.
      rewrite removeDupIdentity; intuition.
    }
    unfold isKS in HkernIsKS. unfold nextKSAddr in HnextAddr. rewrite HlookupEq in *.
    specialize(Hcons0 kernel nextAddr HkernIsKS HnextAddr). destruct Hcons0 as (HnextIsPADDR & HbeqNextNull).
    split; try(assumption). unfold isPADDR in *. simpl.
    destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) nextAddr) eqn:HbeqBlockSceNextAddr.
    {
      rewrite <-beqAddrTrue in HbeqBlockSceNextAddr. rewrite HbeqBlockSceNextAddr in *.
      rewrite HlookupBlockSces in HnextIsPADDR. congruence.
    }
    rewrite <-beqAddrFalse in HbeqBlockSceNextAddr. rewrite removeDupIdentity; intuition.
    (* END NextKSOffsetIsPADDR *)
  }

  assert(NoDupInFreeSlotsList newS).
  { (* BEGIN NoDupInFreeSlotsList newS *)
    assert(Hcons0: NoDupInFreeSlotsList s) by (unfold consistency1 in *; intuition).
    intros pd pdentryPd HlookupPd.
    assert(HlookupPds: lookup pd (memory s) beqAddr = Some (PDT pdentryPd)).
    {
      simpl in HlookupPd.
      destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) pd) eqn:HbeqBlockScePd;
        try(exfalso; congruence).
      rewrite <-beqAddrFalse in HbeqBlockScePd. rewrite removeDupIdentity in HlookupPd; intuition.
    }
    specialize(Hcons0 pd pdentryPd HlookupPds).
    destruct Hcons0 as [slotsList (HslotsList & HwellFormed & HnoDup)]. exists slotsList.
    split; try(split; assumption). subst slotsList. unfold getFreeSlotsList in *. rewrite HlookupPd.
    rewrite HlookupPds. destruct (beqAddr (firstfreeslot pdentryPd) nullAddr) eqn:HbeqFirstNull;
      try(reflexivity). apply eq_sym. apply getFreeSlotsListRecEqSCE.
    - intro Hcontra. rewrite <-Hcontra in *.
      assert(HfirstFree: FirstFreeSlotPointerIsBEAndFreeSlot s) by (unfold consistency1 in *; intuition).
      assert(HfirstIsBE: isBE (firstfreeslot pdentryPd) s).
      {
        specialize(HfirstFree pd pdentryPd). apply HfirstFree. assumption. rewrite beqAddrFalse.
        assumption.
      }
      unfold isBE in HfirstIsBE. rewrite HlookupBlockSces in HfirstIsBE. congruence.
    - unfold isBE. rewrite HlookupBlockSces. intuition.
    - unfold isPADDR. rewrite HlookupBlockSces. intuition.
    (* END NoDupInFreeSlotsList *)
  }

  assert(freeSlotsListIsFreeSlot newS).
  { (* BEGIN freeSlotsListIsFreeSlot newS *)
    assert(Hcons0: freeSlotsListIsFreeSlot s) by (unfold consistency1 in *; intuition).
    intros pd freeslot optSlotsList slotsList HpdIsPDT HoptSlotsList HslotsList HbeqFreeNull.
    assert(HlookupPdEq: lookup pd (memory newS) beqAddr = lookup pd (memory s) beqAddr).
    {
      unfold isPDT in HpdIsPDT. simpl in HpdIsPDT. simpl.
      destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) pd) eqn:HbeqBlockScePd;
        try(exfalso; congruence).
      rewrite <-beqAddrFalse in HbeqBlockScePd. rewrite removeDupIdentity; intuition.
    }
    destruct HoptSlotsList as (HoptSlotsList & HwellFormed).
    assert(HoptSlotsLists: optSlotsList = getFreeSlotsList pd s
                            /\ wellFormedFreeSlotsList optSlotsList <> False).
    {
      split; try(assumption). subst optSlotsList. unfold getFreeSlotsList. rewrite HlookupPdEq.
      unfold isPDT in HpdIsPDT. destruct (lookup pd (memory s) beqAddr) eqn:HlookupPd; try(reflexivity).
      destruct v; try(reflexivity).
      destruct (beqAddr (firstfreeslot p) nullAddr) eqn:HbeqFirstNull; try(reflexivity).
      rewrite <-beqAddrFalse in HbeqFirstNull. apply getFreeSlotsListRecEqSCE.
      - intro Hcontra. rewrite <-Hcontra in *.
        assert(HfirstFree: FirstFreeSlotPointerIsBEAndFreeSlot s) by (unfold consistency1 in *; intuition).
        assert(HfirstIsBE: isBE (firstfreeslot p) s).
        {
          specialize(HfirstFree pd p). apply HfirstFree. assumption. assumption.
        }
        unfold isBE in HfirstIsBE. rewrite HlookupBlockSces in HfirstIsBE. congruence.
      - unfold isBE. rewrite HlookupBlockSces. intuition.
      - unfold isPADDR. rewrite HlookupBlockSces. intuition.
    }
    unfold isPDT in HpdIsPDT. rewrite HlookupPdEq in HpdIsPDT.
    specialize(Hcons0 pd freeslot optSlotsList slotsList HpdIsPDT HoptSlotsLists HslotsList HbeqFreeNull).
    destruct (beqAddr blockToShareInCurrPartAddr freeslot) eqn:HbeqBlockFree.
    {
      rewrite <-beqAddrTrue in HbeqBlockFree. subst freeslot. exfalso; congruence.
    }
    unfold isFreeSlot in *. simpl.
    destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) freeslot) eqn:HbeqBlockSceFree.
    {
      rewrite <-beqAddrTrue in HbeqBlockSceFree. rewrite HbeqBlockSceFree in *.
      rewrite HlookupBlockSces in Hcons0. congruence.
    }
    rewrite <-beqAddrFalse in HbeqBlockSceFree. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
    destruct (lookup freeslot (memory s) beqAddr) eqn:HlookupFree; try(congruence). destruct v; try(congruence).
    destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) (CPaddr (freeslot + sh1offset)))
        eqn:HbeqBlockSceFreeSh1.
    {
      rewrite <-beqAddrTrue in HbeqBlockSceFreeSh1. rewrite HbeqBlockSceFreeSh1 in *.
      rewrite HlookupBlockSces in Hcons0. congruence.
    }
    rewrite <-beqAddrFalse in HbeqBlockSceFreeSh1. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
    destruct (lookup (CPaddr (freeslot + sh1offset)) (memory s) beqAddr); try(congruence).
    destruct v; try(congruence).
    destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) (CPaddr (freeslot + scoffset)))
        eqn:HbeqBlockSceFreeSce.
    {
      rewrite <-beqAddrTrue in HbeqBlockSceFreeSce. rewrite <-HbeqBlockSceFreeSce in *. exfalso.
      rewrite <-beqAddrFalse in HbeqBlockFree. unfold CPaddr in HbeqBlockSceFreeSce.
      destruct (Compare_dec.le_dec (blockToShareInCurrPartAddr + scoffset) maxAddr) eqn:HleBlockSceMax.
      + destruct (Compare_dec.le_dec (freeslot + scoffset) maxAddr).
        * injection HbeqBlockSceFreeSce as HsceEq. contradict HbeqBlockFree.
          destruct blockToShareInCurrPartAddr. destruct freeslot.  simpl in HsceEq.
          assert(p = p0) by lia. subst p0. f_equal. apply proof_irrelevance.
        * assert(HbeqBlockSceNull: CPaddr (blockToShareInCurrPartAddr + scoffset) = nullAddr).
          {
            unfold nullAddr. injection HbeqBlockSceFreeSce as HbeqBlockSceNull. rewrite HbeqBlockSceNull.
            reflexivity.
          }
          assert(Hnull: nullAddrExists s) by (unfold consistency1 in *; intuition).
          unfold nullAddrExists in Hnull. unfold isPADDR in Hnull. rewrite HbeqBlockSceNull in *.
          rewrite HlookupBlockSces in Hnull. congruence.
      + assert(HbeqBlockSceNull: CPaddr (blockToShareInCurrPartAddr + scoffset) = nullAddr).
        {
          unfold nullAddr. unfold CPaddr. rewrite HleBlockSceMax.
          destruct (Compare_dec.le_dec 0 maxAddr); try(lia). f_equal. apply proof_irrelevance.
        }
        assert(Hnull: nullAddrExists s) by (unfold consistency1 in *; intuition).
        unfold nullAddrExists in Hnull. unfold isPADDR in Hnull. rewrite HbeqBlockSceNull in *.
        rewrite HlookupBlockSces in Hnull. congruence.
    }
    rewrite <-beqAddrFalse in HbeqBlockSceFreeSce. rewrite removeDupIdentity; intuition.
    (* END freeSlotsListIsFreeSlot *)
  }

  assert(DisjointFreeSlotsLists newS).
  { (* BEGIN DisjointFreeSlotsLists newS *)
    assert(Hcons0: DisjointFreeSlotsLists s) by (unfold consistency1 in *; intuition).
    intros pd1 pd2 Hpd1IsPDT Hpd2IsPDT HbeqPd1Pd2.
    assert(HlookupPd1Eq: lookup pd1 (memory newS) beqAddr = lookup pd1 (memory s) beqAddr).
    {
      unfold isPDT in Hpd1IsPDT. simpl in Hpd1IsPDT. simpl.
      destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) pd1) eqn:HbeqBlockScePd;
        try(exfalso; congruence).
      rewrite <-beqAddrFalse in HbeqBlockScePd. rewrite removeDupIdentity; intuition.
    }
    assert(HlookupPd2Eq: lookup pd2 (memory newS) beqAddr = lookup pd2 (memory s) beqAddr).
    {
      unfold isPDT in Hpd2IsPDT. simpl in Hpd2IsPDT. simpl.
      destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) pd2) eqn:HbeqBlockScePd;
        try(exfalso; congruence).
      rewrite <-beqAddrFalse in HbeqBlockScePd. rewrite removeDupIdentity; intuition.
    }
    unfold isPDT in *. rewrite HlookupPd1Eq in Hpd1IsPDT. rewrite HlookupPd2Eq in Hpd2IsPDT.
    specialize(Hcons0 pd1 pd2 Hpd1IsPDT Hpd2IsPDT HbeqPd1Pd2).
    destruct Hcons0 as [list1 [list2 (Hlist1 & HwellFormed1 & Hlist2 & HwellFormed2 & Hdisjoint)]].
    exists list1. exists list2. split.
    - subst list1. apply eq_sym. unfold getFreeSlotsList. rewrite HlookupPd1Eq.
      destruct (lookup pd1 (memory s) beqAddr) eqn:HlookupPd1; try(reflexivity). destruct v; try(reflexivity).
      destruct (beqAddr (firstfreeslot p) nullAddr) eqn:HbeqFirstNull; try(reflexivity).
      rewrite <-beqAddrFalse in HbeqFirstNull. apply getFreeSlotsListRecEqSCE.
      + intro Hcontra. rewrite <-Hcontra in *.
        assert(HfirstFree: FirstFreeSlotPointerIsBEAndFreeSlot s) by (unfold consistency1 in *; intuition).
        assert(HfirstIsBE: isBE (firstfreeslot p) s).
        {
          specialize(HfirstFree pd1 p). apply HfirstFree. assumption. assumption.
        }
        unfold isBE in HfirstIsBE. rewrite HlookupBlockSces in HfirstIsBE. congruence.
      + unfold isBE. rewrite HlookupBlockSces. intuition.
      + unfold isPADDR. rewrite HlookupBlockSces. intuition.
    - split. assumption. split; try(split; assumption). subst list2. apply eq_sym. unfold getFreeSlotsList.
      rewrite HlookupPd2Eq. destruct (lookup pd2 (memory s) beqAddr) eqn:HlookupPd2; try(reflexivity).
      destruct v; try(reflexivity).
      destruct (beqAddr (firstfreeslot p) nullAddr) eqn:HbeqFirstNull; try(reflexivity).
      rewrite <-beqAddrFalse in HbeqFirstNull. apply getFreeSlotsListRecEqSCE.
      + intro Hcontra. rewrite <-Hcontra in *.
        assert(HfirstFree: FirstFreeSlotPointerIsBEAndFreeSlot s) by (unfold consistency1 in *; intuition).
        assert(HfirstIsBE: isBE (firstfreeslot p) s).
        {
          specialize(HfirstFree pd2 p). apply HfirstFree. assumption. assumption.
        }
        unfold isBE in HfirstIsBE. rewrite HlookupBlockSces in HfirstIsBE. congruence.
      + unfold isBE. rewrite HlookupBlockSces. intuition.
      + unfold isPADDR. rewrite HlookupBlockSces. intuition.
    (* END DisjointFreeSlotsLists *)
  }

  assert(inclFreeSlotsBlockEntries newS).
  { (* BEGIN inclFreeSlotsBlockEntries newS *)
    assert(Hcons0: inclFreeSlotsBlockEntries s) by (unfold consistency1 in *; intuition).
    intros pd HpdIsPDT.
    assert(HlookupPdEq: lookup pd (memory newS) beqAddr = lookup pd (memory s) beqAddr).
    {
      unfold isPDT in HpdIsPDT. simpl in HpdIsPDT. simpl.
      destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) pd) eqn:HbeqBlockScePd;
        try(exfalso; congruence).
      rewrite <-beqAddrFalse in HbeqBlockScePd. rewrite removeDupIdentity; intuition.
    }
    unfold isPDT in HpdIsPDT. rewrite HlookupPdEq in HpdIsPDT. specialize(Hcons0 pd HpdIsPDT).
    assert(HgetFreeEq: getFreeSlotsList pd newS = getFreeSlotsList pd s).
    {
      unfold getFreeSlotsList. rewrite HlookupPdEq.
      destruct (lookup pd (memory s) beqAddr) eqn:HlookupPd; try(reflexivity). destruct v; try(reflexivity).
      destruct (beqAddr (firstfreeslot p) nullAddr) eqn:HbeqFirstNull; try(reflexivity).
      rewrite <-beqAddrFalse in HbeqFirstNull. apply getFreeSlotsListRecEqSCE.
      + intro Hcontra. rewrite <-Hcontra in *.
        assert(HfirstFree: FirstFreeSlotPointerIsBEAndFreeSlot s) by (unfold consistency1 in *; intuition).
        assert(HfirstIsBE: isBE (firstfreeslot p) s).
        {
          specialize(HfirstFree pd p). apply HfirstFree. assumption. assumption.
        }
        unfold isBE in HfirstIsBE. rewrite HlookupBlockSces in HfirstIsBE. congruence.
      + unfold isBE. rewrite HlookupBlockSces. intuition.
      + unfold isPADDR. rewrite HlookupBlockSces. intuition.
    }
    assert(HgetKSEq: getKSEntries pd newS = getKSEntries pd s).
    {
      destruct (lookup pd (memory s) beqAddr) eqn:HlookupPd; try(exfalso; congruence).
      destruct v; try(exfalso; congruence). apply getKSEntriesEqSCE with p; assumption.
    }
    rewrite HgetFreeEq. rewrite HgetKSEq. assumption.
    (* END inclFreeSlotsBlockEntries *)
  }

  assert(DisjointKSEntries newS).
  { (* BEGIN DisjointKSEntries newS *)
    assert(Hcons0: DisjointKSEntries s) by (unfold consistency1 in *; intuition).
    intros pd1 pd2 Hpd1IsPDT Hpd2IsPDT HbeqPd1Pd2.
    assert(HlookupPd1Eq: lookup pd1 (memory newS) beqAddr = lookup pd1 (memory s) beqAddr).
    {
      unfold isPDT in Hpd1IsPDT. simpl in Hpd1IsPDT. simpl.
      destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) pd1) eqn:HbeqBlockScePd;
        try(exfalso; congruence).
      rewrite <-beqAddrFalse in HbeqBlockScePd. rewrite removeDupIdentity; intuition.
    }
    assert(HlookupPd2Eq: lookup pd2 (memory newS) beqAddr = lookup pd2 (memory s) beqAddr).
    {
      unfold isPDT in Hpd2IsPDT. simpl in Hpd2IsPDT. simpl.
      destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) pd2) eqn:HbeqBlockScePd;
        try(exfalso; congruence).
      rewrite <-beqAddrFalse in HbeqBlockScePd. rewrite removeDupIdentity; intuition.
    }
    unfold isPDT in *. rewrite HlookupPd1Eq in Hpd1IsPDT. rewrite HlookupPd2Eq in Hpd2IsPDT.
    specialize(Hcons0 pd1 pd2 Hpd1IsPDT Hpd2IsPDT HbeqPd1Pd2).
    destruct Hcons0 as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. exists list1. exists list2. split.
    - subst list1. apply eq_sym.
      destruct (lookup pd1 (memory s) beqAddr) eqn:HlookupPd; try(exfalso; congruence).
      destruct v; try(exfalso; congruence). apply getKSEntriesEqSCE with p; assumption.
    - split; try(assumption). subst list2. apply eq_sym.
      destruct (lookup pd2 (memory s) beqAddr) eqn:HlookupPd; try(exfalso; congruence).
      destruct v; try(exfalso; congruence). apply getKSEntriesEqSCE with p; assumption.
    (* END DisjointKSEntries *)
  }

  assert(noDupPartitionTree newS).
  { (* BEGIN noDupPartitionTree newS *)
    assert(Hcons0: noDupPartitionTree s) by (unfold consistency1 in *; intuition).
    unfold noDupPartitionTree in *. rewrite HgetPartsEq. assumption.
    (* END noDupPartitionTree *)
  }

  assert(isParent newS).
  { (* BEGIN isParent newS *)
    assert(Hcons0: isParent s) by (unfold consistency1 in *; intuition).
    intros partition pdparent HparentIsPart HpartIsChild. rewrite HgetPartsEq in HparentIsPart.
    assert(HgetChildrenEq: getChildren pdparent newS = getChildren pdparent s).
    {
      apply getChildrenEqSCE; try(assumption). apply partitionsArePDT; try(assumption).
      unfold consistency1 in *; intuition. unfold consistency1 in *; intuition.
    }
    rewrite HgetChildrenEq in HpartIsChild. specialize(Hcons0 partition pdparent HparentIsPart HpartIsChild).
    unfold pdentryParent in *. simpl.
    destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) partition) eqn:HbeqBlockScePart.
    {
      rewrite <-beqAddrTrue in HbeqBlockScePart. rewrite HbeqBlockScePart in *.
      rewrite HlookupBlockSces in Hcons0. congruence.
    }
    rewrite <-beqAddrFalse in HbeqBlockScePart. rewrite removeDupIdentity; intuition.
    (* END isParent *)
  }

  assert(isChild newS).
  { (* BEGIN isChild newS *)
    assert(Hcons0: isChild s) by (unfold consistency1 in *; intuition).
    intros partition pdparent HpartIsPart HparentIsParent. rewrite HgetPartsEq in HpartIsPart.
    assert(HparentIsParents: pdentryParent partition pdparent s).
    {
      unfold pdentryParent in *. simpl in HparentIsParent.
      destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) partition) eqn:HbeqBlockScePart;
        try(exfalso; congruence). rewrite <-beqAddrFalse in HbeqBlockScePart.
      rewrite removeDupIdentity in HparentIsParent; intuition.
    }
    specialize(Hcons0 partition pdparent HpartIsPart HparentIsParents).
    assert(HgetChildrenEq: getChildren pdparent newS = getChildren pdparent s).
    {
      apply getChildrenEqSCE; try(assumption). unfold pdentryParent in HparentIsParents.
      destruct (lookup partition (memory s) beqAddr) eqn:HlookupPart; try(exfalso; congruence).
      destruct v; try(exfalso; congruence).
      assert(HparentOfPart: parentOfPartitionIsPartition s) by (unfold consistency1 in *; intuition).
      specialize(HparentOfPart partition p HlookupPart).
      destruct HparentOfPart as (HparentIsPart & HparentOfRoot & _).
      destruct (beqAddr partition constantRootPartM) eqn:HbeqPartRoot.
      {
        rewrite <-beqAddrTrue in HbeqPartRoot. specialize(HparentOfRoot HbeqPartRoot).
        rewrite HparentOfRoot in *. rewrite HparentIsParents in *.
        assert(Hnull: nullAddrExists s) by (unfold consistency1 in *; intuition).
        unfold nullAddrExists in Hnull. unfold isPADDR in Hnull. unfold getChildren in Hcons0.
        destruct (lookup nullAddr (memory s) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence). simpl in Hcons0. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in HbeqPartRoot. specialize(HparentIsPart HbeqPartRoot).
      destruct HparentIsPart as ([parentEntry HlookupParent] & _). unfold isPDT. rewrite HparentIsParents.
      rewrite HlookupParent. trivial.
    }
    rewrite HgetChildrenEq. assumption.
    (* END isChild *)
  }

  assert(noDupKSEntriesList newS).
  { (* BEGIN noDupKSEntriesList newS *)
    assert(Hcons0: noDupKSEntriesList s) by (unfold consistency1 in *; intuition).
    intros partition HpartIsPDT.
    assert(HpartIsPDTs: isPDT partition s).
    {
      unfold isPDT in *. simpl in HpartIsPDT.
      destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) partition) eqn:HbeqBlockScePart;
          try(exfalso; congruence).
      rewrite <-beqAddrFalse in HbeqBlockScePart. rewrite removeDupIdentity in HpartIsPDT; intuition.
    }
    specialize(Hcons0 partition HpartIsPDTs).
    assert(HgetKSEq: getKSEntries partition newS = getKSEntries partition s).
    {
      unfold isPDT in HpartIsPDTs.
      destruct (lookup partition (memory s) beqAddr) eqn:HlookupPart; try(exfalso; congruence).
      destruct v; try(exfalso; congruence). apply getKSEntriesEqSCE with p; assumption.
    }
    rewrite HgetKSEq. assumption.
    (* END noDupKSEntriesList *)
  }

  assert(noDupMappedBlocksList newS).
  { (* BEGIN noDupMappedBlocksList newS *)
    assert(Hcons0: noDupMappedBlocksList s) by (unfold consistency1 in *; intuition).
    intros partition HpartIsPDT.
    assert(HpartIsPDTs: isPDT partition s).
    {
      unfold isPDT in *. simpl in HpartIsPDT.
      destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) partition) eqn:HbeqBlockScePart;
          try(exfalso; congruence).
      rewrite <-beqAddrFalse in HbeqBlockScePart. rewrite removeDupIdentity in HpartIsPDT; intuition.
    }
    specialize(Hcons0 partition HpartIsPDTs).
    assert(HgetMappedBlocksEq: getMappedBlocks partition newS = getMappedBlocks partition s).
    {
      apply getMappedBlocksEqSCE; assumption.
    }
    rewrite HgetMappedBlocksEq. assumption.
    (* END noDupMappedBlocksList *)
  }

  assert(wellFormedBlock newS).
  { (* BEGIN wellFormedBlock newS *)
    assert(Hcons0: wellFormedBlock s) by (unfold consistency1 in *; intuition).
    intros block startaddr endaddr HPFlag Hstart Hend.
    assert(HlookupEq: lookup block (memory newS) beqAddr = lookup block (memory s) beqAddr).
    {
      unfold bentryPFlag in HPFlag. simpl. simpl in HPFlag.
      destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) block) eqn:HbeqBlockSceBlock;
          try(exfalso; congruence). rewrite <-beqAddrFalse in HbeqBlockSceBlock.
      rewrite removeDupIdentity; intuition.
    }
    unfold bentryPFlag in HPFlag. unfold bentryStartAddr in Hstart. unfold bentryEndAddr in Hend.
    rewrite HlookupEq in *. specialize(Hcons0 block startaddr endaddr HPFlag Hstart Hend).
    assumption.
    (* END wellFormedBlock *)
  }

  assert(parentOfPartitionIsPartition newS).
  { (* BEGIN parentOfPartitionIsPartition newS *)
    assert(Hcons0: parentOfPartitionIsPartition s) by (unfold consistency1 in *; intuition).
    intros partition entry HlookupPart.
    assert(HlookupParts: lookup partition (memory s) beqAddr = Some (PDT entry)).
    {
      simpl in HlookupPart. destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) partition)
        eqn:HbeqBlockScePart.
      {
        rewrite <-beqAddrTrue in HbeqBlockScePart. rewrite HbeqBlockScePart in *. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in HbeqBlockScePart. rewrite removeDupIdentity in HlookupPart; intuition.
    }
    specialize(Hcons0 partition entry HlookupParts).
    destruct Hcons0 as (HparentIsPart & HparentOfRoot & HbeqParentPart). split.
    - intro HbeqPartRoot. specialize(HparentIsPart HbeqPartRoot).
      destruct HparentIsPart as ([parentEntry HlookupParent] & HparentIsPart). rewrite HgetPartsEq.
      split; try(assumption). exists parentEntry. simpl.
      destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) (parent entry)) eqn:HbeqBlockSceParent.
      {
        rewrite <-beqAddrTrue in HbeqBlockSceParent. rewrite HbeqBlockSceParent in *. congruence.
      }
      rewrite <-beqAddrFalse in HbeqBlockSceParent. rewrite removeDupIdentity; intuition.
    - split; assumption.
    (* END parentOfPartitionIsPartition *)
  }

  assert(NbFreeSlotsISNbFreeSlotsInList newS).
  { (* BEGIN NbFreeSlotsISNbFreeSlotsInList newS *)
    assert(Hcons0: NbFreeSlotsISNbFreeSlotsInList s) by (unfold consistency1 in *; intuition).
    intros partition nbfreeslots HpartIsPDT HnbFree.
    assert(HlookupEq: lookup partition (memory newS) beqAddr = lookup partition (memory s) beqAddr).
    {
      unfold isPDT in HpartIsPDT. simpl in HpartIsPDT. simpl.
      destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) partition) eqn:HbeqBlockScePart;
          try(exfalso; congruence).
      rewrite <-beqAddrFalse in HbeqBlockScePart. rewrite removeDupIdentity; intuition.
    }
    unfold isPDT in HpartIsPDT. unfold pdentryNbFreeSlots in HnbFree. rewrite HlookupEq in *.
    specialize(Hcons0 partition nbfreeslots HpartIsPDT HnbFree).
    destruct Hcons0 as [slotsList (HslotsList & HwellFormed & HnbFreeLen)]. exists slotsList.
    split; try(split; assumption). subst slotsList. apply eq_sym. unfold getFreeSlotsList. rewrite HlookupEq.
    destruct (lookup partition (memory s) beqAddr) eqn:HlookupPart; try(reflexivity).
    destruct v; try(reflexivity).
    destruct (beqAddr (firstfreeslot p) nullAddr) eqn:HbeqFirstNull; try(reflexivity).
    rewrite <-beqAddrFalse in HbeqFirstNull. apply getFreeSlotsListRecEqSCE.
    - intro Hcontra. rewrite <-Hcontra in *.
      assert(HfirstFree: FirstFreeSlotPointerIsBEAndFreeSlot s) by (unfold consistency1 in *; intuition).
      assert(HfirstIsBE: isBE (firstfreeslot p) s).
      {
        specialize(HfirstFree partition p). apply HfirstFree. assumption. assumption.
      }
      unfold isBE in HfirstIsBE. rewrite HlookupBlockSces in HfirstIsBE. congruence.
    - unfold isBE. rewrite HlookupBlockSces. intuition.
    - unfold isPADDR. rewrite HlookupBlockSces. intuition.
    (* END NbFreeSlotsISNbFreeSlotsInList *)
  }

  assert(maxNbPrepareIsMaxNbKernels newS).
  { (* BEGIN maxNbPrepareIsMaxNbKernels newS *)
    assert(Hcons0: maxNbPrepareIsMaxNbKernels s) by (unfold consistency1 in *; intuition).
    intros partition kernList HkernList.
    assert(HkernLists: isListOfKernels kernList partition s).
    {
      revert HkernList. apply isListOfKernelsEqSCE.
    }
    specialize(Hcons0 partition kernList HkernLists). assumption.
    (* END maxNbPrepareIsMaxNbKernels *)
  }

  assert(blockInChildHasAtLeastEquivalentBlockInParent newS).
  { (* BEGIN blockInChildHasAtLeastEquivalentBlockInParent newS *)
    assert(Hcons0: blockInChildHasAtLeastEquivalentBlockInParent s) by (unfold consistency1 in *; intuition).
    intros pdparent child block startChild endChild HparentIsPart HchildIsChild HblockMappedChild Hstart Hend
      HPFlag. rewrite HgetPartsEq in HparentIsPart.
    assert(HgetChildrenEq: getChildren pdparent newS = getChildren pdparent s).
    {
      apply getChildrenEqSCE; try(assumption). apply partitionsArePDT; try(assumption).
      unfold consistency1 in *; intuition. unfold consistency1 in *; intuition.
    }
    rewrite HgetChildrenEq in HchildIsChild.
    assert(HgetMappedBlocksChildEq: getMappedBlocks child newS = getMappedBlocks child s).
    {
      apply getMappedBlocksEqSCE; try(assumption). apply childrenArePDT with pdparent.
      unfold consistency1 in *; intuition. assumption.
    }
    assert(HlookupEq: lookup block (memory newS) beqAddr = lookup block (memory s) beqAddr).
    {
      unfold bentryPFlag in HPFlag. simpl. simpl in HPFlag.
      destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) block) eqn:HbeqBlockSceBlock;
          try(exfalso; congruence). rewrite <-beqAddrFalse in HbeqBlockSceBlock.
      rewrite removeDupIdentity; intuition.
    }
    rewrite HgetMappedBlocksChildEq in HblockMappedChild. unfold bentryPFlag in HPFlag.
    unfold bentryStartAddr in Hstart. unfold bentryEndAddr in Hend. rewrite HlookupEq in *.
    specialize(Hcons0 pdparent child block startChild endChild HparentIsPart HchildIsChild HblockMappedChild
      Hstart Hend HPFlag). destruct Hcons0 as [blockParent [startParent [endParent (HblockParentMapped &
      HstartParent & HendParent & Hbounds)]]]. exists blockParent. exists startParent. exists endParent.
    assert(HgetMappedBlocksParentEq: getMappedBlocks pdparent newS = getMappedBlocks pdparent s).
    {
      apply getMappedBlocksEqSCE; try(assumption). apply partitionsArePDT; try(assumption).
      unfold consistency1 in *; intuition. unfold consistency1 in *; intuition.
    }
    assert(HlookupBlockParentEq: lookup blockParent (memory newS) beqAddr
                                  = lookup blockParent (memory s) beqAddr).
    {
      simpl. destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) blockParent)
        eqn:HbeqBlockSceBlockParent.
      {
        rewrite <-beqAddrTrue in HbeqBlockSceBlockParent. unfold bentryStartAddr in HstartParent.
        rewrite HbeqBlockSceBlockParent in *. rewrite HlookupBlockSces in HstartParent. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in HbeqBlockSceBlockParent. rewrite removeDupIdentity; intuition.
    }
    rewrite HgetMappedBlocksParentEq. unfold bentryStartAddr. unfold bentryEndAddr.
    rewrite HlookupBlockParentEq. intuition.
    (* END blockInChildHasAtLeastEquivalentBlockInParent *)
  }

  assert(partitionTreeIsTree newS).
  { (* BEGIN partitionTreeIsTree newS *)
    assert(Hcons0: partitionTreeIsTree s) by (unfold consistency1 in *; intuition).
    intros child pdparent parentsList HbeqChildRoot HchildIsPart HparentIsParent HparentsList.
    rewrite HgetPartsEq in HchildIsPart.
    assert(HparentIsParents: pdentryParent child pdparent s).
    {
      unfold pdentryParent in *. simpl in HparentIsParent.
      destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) child) eqn:HbeqBlockSceChild;
        try(exfalso; congruence). rewrite <-beqAddrFalse in HbeqBlockSceChild.
      rewrite removeDupIdentity in HparentIsParent; intuition.
    }
    assert(HparentsLists: isParentsList s parentsList pdparent).
    {
      revert HparentsList. apply isParentsListEqSCERev with scentryBlock; try(assumption).
      - unfold pdentryParent in HparentIsParents.
        destruct (lookup child (memory s) beqAddr) eqn:HlookupChild; try(exfalso; congruence).
        destruct v; try(exfalso; congruence).
        assert(HparentOfPart: parentOfPartitionIsPartition s) by (unfold consistency1 in *; intuition).
        specialize(HparentOfPart child p HlookupChild).
        destruct HparentOfPart as (HparentIsPart & _ & _). specialize(HparentIsPart HbeqChildRoot).
        destruct HparentIsPart. rewrite HparentIsParents. assumption.
      - unfold consistency1 in *; intuition.
    }
    specialize(Hcons0 child pdparent parentsList HbeqChildRoot HchildIsPart HparentIsParents HparentsLists).
    assumption.
    (* END partitionTreeIsTree *)
  }

  assert(kernelEntriesAreValid newS).
  { (* BEGIN kernelEntriesAreValid newS *)
    assert(Hcons0: kernelEntriesAreValid s) by (unfold consistency1 in *; intuition).
    intros kernel idx HkernIsKS HidxBounded.
    assert(HkernIsKSs: isKS kernel s).
    {
      unfold isKS in HkernIsKS. simpl in HkernIsKS.
      destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) kernel) eqn:HbeqBlockSceKern;
          try(exfalso; congruence). rewrite <-beqAddrFalse in HbeqBlockSceKern.
      rewrite removeDupIdentity in HkernIsKS; intuition.
    }
    specialize(Hcons0 kernel idx HkernIsKSs HidxBounded). unfold isBE in *. simpl.
    destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) (CPaddr (kernel + idx)))
      eqn:HbeqBlockSceKernIdx.
    {
      rewrite <-beqAddrTrue in HbeqBlockSceKernIdx. rewrite HbeqBlockSceKernIdx in *.
      rewrite HlookupBlockSces in Hcons0. congruence.
    }
    rewrite <-beqAddrFalse in HbeqBlockSceKernIdx. rewrite removeDupIdentity; intuition.
    (* END kernelEntriesAreValid *)
  }

  assert(nextKernelIsValid newS).
  { (* BEGIN nextKernelIsValid newS *)
    assert(Hcons0: nextKernelIsValid s) by (unfold consistency1 in *; intuition).
    intros kernel HkernIsKS.
    assert(HkernIsKSs: isKS kernel s).
    {
      unfold isKS in HkernIsKS. simpl in HkernIsKS.
      destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) kernel) eqn:HbeqBlockSceKern;
          try(exfalso; congruence). rewrite <-beqAddrFalse in HbeqBlockSceKern.
      rewrite removeDupIdentity in HkernIsKS; intuition.
    }
    specialize(Hcons0 kernel HkernIsKSs). destruct Hcons0 as (HnextValid & [nextAddr (HlookupNext & HnextOr)]).
    split. assumption. exists nextAddr. split.
    - intro Hp. specialize(HlookupNext Hp). simpl.
      destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) {| p := kernel + nextoffset; Hp := Hp |})
        eqn:HbeqBlockSceNext.
      {
        rewrite <-beqAddrTrue in HbeqBlockSceNext. rewrite HbeqBlockSceNext in *. congruence.
      }
      rewrite <-beqAddrFalse in HbeqBlockSceNext. rewrite removeDupIdentity; intuition.
    - destruct HnextOr as [HnextIsKS | HnextIsNull]; try(right; assumption). left. unfold isKS in *. simpl.
      destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) nextAddr) eqn:HbeqBlockSceNext.
      {
        rewrite <-beqAddrTrue in HbeqBlockSceNext. rewrite HbeqBlockSceNext in *.
        rewrite HlookupBlockSces in HnextIsKS. congruence.
      }
      rewrite <-beqAddrFalse in HbeqBlockSceNext. rewrite removeDupIdentity; intuition.
    (* END nextKernelIsValid *)
  }

  assert(noDupListOfKerns newS).
  { (* BEGIN noDupListOfKerns newS *)
    assert(Hcons0: noDupListOfKerns s) by (unfold consistency1 in *; intuition).
    intros partition kernList HkernList.
    assert(HkernLists: isListOfKernels kernList partition s).
    {
      revert HkernList. apply isListOfKernelsEqSCE.
    }
    specialize(Hcons0 partition kernList HkernLists). assumption.
    (* END noDupListOfKerns *)
  }

  assert(MPUsizeIsBelowMax newS).
  { (* BEGIN MPUsizeIsBelowMax newS *)
    assert(Hcons0: MPUsizeIsBelowMax s) by (unfold consistency1 in *; intuition).
    intros partition MPUlist HMPUlist.
    assert(HMPUlists: pdentryMPU partition MPUlist s).
    {
      unfold pdentryMPU in HMPUlist. simpl in HMPUlist.
      destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) partition) eqn:HbeqBlockScePart;
          try(exfalso; congruence).
      rewrite <-beqAddrFalse in HbeqBlockScePart. rewrite removeDupIdentity in HMPUlist; intuition.
    }
    specialize(Hcons0 partition MPUlist HMPUlists). assumption.
    (* END MPUsizeIsBelowMax *)
  }

  assert(originIsParentBlocksStart newS).
  { (* BEGIN originIsParentBlocksStart newS *)
    assert(Hcons0: originIsParentBlocksStart s) by (unfold consistency1 in *; intuition).
    intros part pdentryPart block scentryaddr scorigin HpartIsPart HlookupPart HblockMapped Hsce Horigin.
    rewrite HgetPartsEq in HpartIsPart.
    assert(HlookupParts: lookup part (memory s) beqAddr = Some (PDT pdentryPart)).
    {
      simpl in HlookupPart.
      destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) part) eqn:HbeqBlockScePart;
          try(exfalso; congruence). rewrite <-beqAddrFalse in HbeqBlockScePart.
      rewrite removeDupIdentity in HlookupPart; try(apply not_eq_sym; assumption). assumption.
    }
    assert(HgetMappedBlocksPartEq: getMappedBlocks part newS = getMappedBlocks part s).
    {
      apply getMappedBlocksEqSCE; try(assumption). apply partitionsArePDT; try(assumption).
      unfold consistency1 in *; intuition.
      unfold consistency1 in *; intuition.
    }
    assert(HparentOfPart: parentOfPartitionIsPartition s) by (unfold consistency1 in *; intuition).
    rewrite HgetMappedBlocksPartEq in HblockMapped. specialize(HparentOfPart part pdentryPart HlookupParts).
    assert(Horigins: scentryOrigin scentryaddr scorigin s).
    {
      unfold scentryOrigin in *. simpl in Horigin.
      destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) scentryaddr) eqn:HbeqSceSce.
      - rewrite <-beqAddrTrue in HbeqSceSce. rewrite HbeqSceSce in *. rewrite HlookupBlockSces.
        simpl in Horigin. assumption.
      - rewrite <-beqAddrFalse in HbeqSceSce.
        rewrite removeDupIdentity in Horigin; try(apply not_eq_sym; assumption). assumption.
    }
    specialize(Hcons0 part pdentryPart block scentryaddr scorigin HpartIsPart HlookupParts HblockMapped Hsce
      Horigins). destruct Hcons0 as (Hcons0 & HstartAbove). split.
    - intro HbeqPartRoot. specialize(Hcons0 HbeqPartRoot).
      destruct HparentOfPart as (HparentIsPart & _ & HbeqParentPart). specialize(HparentIsPart HbeqPartRoot).
      destruct HparentIsPart as ([parentEntry HlookupParent] & HparentIsPart).
      assert(HgetBlocksParentEq: getMappedBlocks (parent pdentryPart) newS
                                  = getMappedBlocks (parent pdentryPart) s).
      { apply getMappedBlocksEqSCE; try(assumption). unfold isPDT. rewrite HlookupParent. trivial. }
      rewrite HgetBlocksParentEq.
      destruct Hcons0 as [blockParent (HblockParentMapped & HstartParent & Hincl)].
      exists blockParent.
      assert(HlookupBlockEq: lookup block (memory newS) beqAddr = lookup block (memory s) beqAddr).
      {
        simpl. destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) block) eqn:HbeqBlockSceBlock.
        {
          exfalso. rewrite <-beqAddrTrue in HbeqBlockSceBlock. subst block.
          apply mappedBlockIsBE in HblockMapped. destruct HblockMapped as [bentryBlock (HlookupBlock & _)].
          unfold isSCE in HsceIsSCE. rewrite HlookupBlock in HsceIsSCE. congruence.
        }
        rewrite <-beqAddrFalse in HbeqBlockSceBlock. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
        reflexivity.
      }
      assert(HlookupBlockParentEq: lookup blockParent (memory newS) beqAddr
                                    = lookup blockParent (memory s) beqAddr).
      {
        simpl. destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) blockParent)
          eqn:HbeqBlockSceBlockParent.
        {
          exfalso. rewrite <-beqAddrTrue in HbeqBlockSceBlockParent. subst blockParent.
          apply mappedBlockIsBE in HblockParentMapped.
          destruct HblockParentMapped as [bentryBlock (HlookupBlock & _)].
          unfold isSCE in HsceIsSCE. rewrite HlookupBlock in HsceIsSCE. congruence.
        }
        rewrite <-beqAddrFalse in HbeqBlockSceBlockParent.
        rewrite removeDupIdentity; try(apply not_eq_sym; assumption). reflexivity.
      }
      split. assumption. split. unfold bentryStartAddr. rewrite HlookupBlockParentEq. assumption.
      cbn -[newS]. simpl in Hincl. rewrite HlookupBlockEq. rewrite HlookupBlockParentEq. assumption.
    - intros startBlock HstartBlock. apply HstartAbove. unfold bentryStartAddr in *. simpl in HstartBlock.
      destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) block) eqn:HbeqBlockSceBlock;
        try(exfalso; congruence). rewrite <-beqAddrFalse in HbeqBlockSceBlock.
      rewrite removeDupIdentity in HstartBlock; try(apply not_eq_sym); assumption.
    (* END originIsParentBlocksStart *)
  }

  assert(nextImpliesBlockWasCut newS).
  { (* BEGIN nextImpliesBlockWasCut newS *)
    assert(Hcons0: nextImpliesBlockWasCut s) by (unfold consistency1 in *; intuition).
    intros part pdentryPart block scentryaddr scnext endaddr HpartIsPart HlookupPart HblockMapped HendBlock
      Hsce HbeqSceNull Hnext HbeqPartRoot. rewrite HgetPartsEq in HpartIsPart.
    assert(HlookupParts: lookup part (memory s) beqAddr = Some (PDT pdentryPart)).
    {
      simpl in HlookupPart.
      destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) part) eqn:HbeqBlockScePart;
        try(exfalso; congruence).
      rewrite <-beqAddrFalse in HbeqBlockScePart.
      rewrite removeDupIdentity in HlookupPart; try(apply not_eq_sym; assumption). assumption.
    }
    assert(HgetMappedBlocksPartEq: getMappedBlocks part newS = getMappedBlocks part s).
    {
      apply getMappedBlocksEqSCE; try(assumption). apply partitionsArePDT; try(assumption).
      unfold consistency1 in *; intuition.
      unfold consistency1 in *; intuition.
    }
    assert(HparentOfPart: parentOfPartitionIsPartition s) by (unfold consistency1 in *; intuition).
    specialize(HparentOfPart part pdentryPart HlookupParts).
    destruct HparentOfPart as (HparentIsPart & _ & HbeqParentPart). specialize(HparentIsPart HbeqPartRoot).
    destruct HparentIsPart as ([parentEntry HlookupParent] & HparentIsPart).
    assert(HgetBlocksParentEq: getMappedBlocks (parent pdentryPart) newS
                                = getMappedBlocks (parent pdentryPart) s).
    { apply getMappedBlocksEqSCE; try(assumption). unfold isPDT. rewrite HlookupParent. trivial. }
    rewrite HgetMappedBlocksPartEq in HblockMapped. rewrite HgetBlocksParentEq.
    destruct (beqAddr blockToShareInCurrPartAddr block) eqn:HbeqBlocks.
    - rewrite <-beqAddrTrue in HbeqBlocks. subst block.
      assert(HblockEquivInParent: blockInChildHasAtLeastEquivalentBlockInParent s1)
          by (unfold consistency1 in *; intuition).
      assert(HgetPartsEqss1: getPartitions multiplexer s = getPartitions multiplexer s1).
      {
        assert(Hss3: getPartitions multiplexer s = getPartitions multiplexer s3).
        {
          rewrite Hs. apply getPartitionsEqSCE. unfold consistency1 in *; intuition.
          unfold isSCE. rewrite HlookupNewSces3. trivial.
          unfold consistency1 in *; intuition.
        }
        assert(Hs3s2: getPartitions multiplexer s3 = getPartitions multiplexer s2).
        {
          destruct blockToShareEnabled.
          - assert(HtrivTrue: is_true true) by (unfold is_true; reflexivity). specialize(Henabled HtrivTrue).
            destruct Henabled as [pdentryCurrs (Hs3 & Henabled)]. rewrite Hs3.
            apply getPartitionsEqPDT with pdentryCurrs2; try(assumption). simpl. reflexivity.
            unfold consistency1 in *; intuition. unfold consistency1 in *; intuition.
          - assert(HtrivFalse: ~is_true false) by (unfold is_true; intro Hcontra; congruence).
            specialize(HnotEnabled HtrivFalse). subst s3. reflexivity.
        }
        rewrite Hss3. rewrite Hs3s2. rewrite Hs2.
        apply getPartitionsEqBEPDflagNoChangePresentNoChangeStartNoChange with bentryShares0
            (CPaddr (blockToShareInCurrPartAddr + sh1offset)); try(assumption).
        unfold consistency1 in *; intuition. unfold consistency1 in *; intuition.
        apply lookupSh1EntryAddr with bentryShares0. assumption.
        unfold sh1entryPDflag in *. rewrite Hs2 in *. simpl in *.
        destruct (beqAddr blockToShareInCurrPartAddr (CPaddr (blockToShareInCurrPartAddr + sh1offset)))
          eqn:HbeqBlockBlockSce; try(exfalso; congruence). rewrite <-beqAddrFalse in HbeqBlockBlockSce.
        rewrite removeDupIdentity; try(apply not_eq_sym; assumption). reflexivity.
        unfold CBlockEntry. assert(blockindex bentryShares0 < kernelStructureEntriesNb) by (apply Hidx).
        destruct (Compare_dec.lt_dec (blockindex bentryShares0) kernelStructureEntriesNb); try(lia).
        simpl. reflexivity.
        unfold CBlockEntry. assert(blockindex bentryShares0 < kernelStructureEntriesNb) by (apply Hidx).
        destruct (Compare_dec.lt_dec (blockindex bentryShares0) kernelStructureEntriesNb); try(lia).
        simpl. unfold CBlock. assert(cutAddr <= maxIdx) by (rewrite maxIdxEqualMaxAddr; apply Hp).
        destruct (Compare_dec.le_dec (cutAddr - startAddr (blockrange bentryShares0)) maxIdx); try(lia).
        simpl. reflexivity.
        unfold consistency1 in *; intuition.
      }
      assert(HpartIsChild: In part (getChildren (parent pdentryPart) s1)).
      {
        assert(Hchild: isChild s1) by (unfold consistency1 in *; intuition).
        rewrite HgetPartsEqss1 in HpartIsPart.
        specialize(Hchild part (parent pdentryPart) HpartIsPart). apply Hchild. unfold pdentryParent.
        rewrite Hs in HlookupParts. simpl in HlookupParts.
        destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) part) eqn:HbeqNewScePart; try(exfalso; congruence).
        rewrite <-beqAddrFalse in HbeqNewScePart.
        rewrite removeDupIdentity in HlookupParts; try(apply not_eq_sym; assumption).
        assert(Hs3s2: exists pdentryParts2, lookup part (memory s2) beqAddr = Some(PDT pdentryParts2)
                                            /\ parent pdentryPart = parent pdentryParts2).
        {
          destruct blockToShareEnabled.
          - assert(HtrivTrue: is_true true) by (unfold is_true; reflexivity). specialize(Henabled HtrivTrue).
            destruct Henabled as [pdentryCurrs (Hs3 & Henabled)]. rewrite Hs3 in HlookupParts.
            simpl in HlookupParts. destruct (beqAddr currentPart part) eqn:HbeqCurrPart.
            + exists pdentryCurrs2. rewrite <-beqAddrTrue in HbeqCurrPart. subst part. split. assumption. simpl.
              injection HlookupParts as HpdentriesEq. rewrite <-HpdentriesEq. simpl. reflexivity.
            + rewrite <-beqAddrFalse in HbeqCurrPart.
              rewrite removeDupIdentity in HlookupParts; try(apply not_eq_sym; assumption). exists pdentryPart.
              split. assumption. reflexivity.
          - assert(HtrivFalse: ~is_true false) by (unfold is_true; intro Hcontra; congruence).
            specialize(HnotEnabled HtrivFalse). subst s3. exists pdentryPart. split. assumption. reflexivity.
        }
        destruct Hs3s2 as [pdentryParts2 (Hlookups2 & HparentsEq)]. rewrite Hs2 in Hlookups2. simpl in Hlookups2.
        destruct (beqAddr blockToShareInCurrPartAddr part) eqn:HbeqBlockPart; try(exfalso; congruence).
        rewrite <-beqAddrFalse in HbeqBlockPart.
        rewrite removeDupIdentity in Hlookups2; try(apply not_eq_sym; assumption). rewrite Hlookups2.
        assumption.
      }
      assert(HstartBlock: bentryStartAddr blockToShareInCurrPartAddr blockToCutStartAddr s1).
      {
        assert(Hstarts0: bentryStartAddr blockToShareInCurrPartAddr blockToCutStartAddr s0) by intuition.
        unfold bentryStartAddr in *. rewrite HlookupBlocks1. rewrite H17 in Hstarts0. assumption.
      }
      assert(HlookupBlockEq: lookup blockToShareInCurrPartAddr (memory newS) beqAddr
                              = lookup blockToShareInCurrPartAddr (memory s) beqAddr).
      {
        unfold bentryEndAddr in HendBlock. simpl. simpl in HendBlock.
        destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) blockToShareInCurrPartAddr)
          eqn:HbeqBlockSceBlock; try(exfalso; congruence). rewrite <-beqAddrFalse in HbeqBlockSceBlock.
        rewrite removeDupIdentity; try(apply not_eq_sym; assumption). reflexivity.
      }
      unfold bentryEndAddr in HendBlock. rewrite HlookupBlockEq in HendBlock.
      assert(HendBlocks1: bentryEndAddr blockToShareInCurrPartAddr blockToCutEndAddr s1).
      {
        assert(Hends0: bentryEndAddr blockToShareInCurrPartAddr blockToCutEndAddr s0) by intuition.
        unfold bentryEndAddr in *. rewrite HlookupBlocks1. rewrite H17 in Hends0. assumption.
      }
      assert(HPFlag: bentryPFlag blockToShareInCurrPartAddr true s1).
      {
        assert(HPFlag0: bentryPFlag blockToShareInCurrPartAddr true s0) by assumption. unfold bentryPFlag.
        unfold bentryPFlag in HPFlag0. rewrite HlookupBlocks1. rewrite H17 in HPFlag0. assumption.
      }
      rewrite HgetPartsEqss1 in HparentIsPart.
      assert(HgetBlocksPartEq: getMappedBlocks part s = getMappedBlocks part s1).
      {
        assert(Hss3: getMappedBlocks part s = getMappedBlocks part s3).
        {
          rewrite Hs. apply getMappedBlocksEqSCE. unfold isPDT. rewrite Hs in HlookupParts. simpl in HlookupParts.
          destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) part) eqn:HbeqNewScePart;
            try(exfalso; congruence). rewrite <-beqAddrFalse in HbeqNewScePart.
          rewrite removeDupIdentity in HlookupParts; try(apply not_eq_sym; assumption). rewrite HlookupParts.
          trivial.
          unfold isSCE. rewrite HlookupNewSces3. trivial.
        }
        assert(Hs3s2: getMappedBlocks part s3 = getMappedBlocks part s2).
        {
          destruct blockToShareEnabled.
          - assert(HtrivTrue: is_true true) by (unfold is_true; reflexivity). specialize(Henabled HtrivTrue).
            destruct Henabled as [pdentryCurrs (Hs3 & Henabled)]. rewrite Hs3.
            apply getMappedBlocksEqPDT with pdentryCurrs2; try(assumption).
            unfold consistency1 in *; intuition. simpl. reflexivity.
          - assert(HtrivFalse: ~is_true false) by (unfold is_true; intro Hcontra; congruence).
            specialize(HnotEnabled HtrivFalse). subst s3. reflexivity.
        }
        rewrite Hss3. rewrite Hs3s2. rewrite Hs2. apply getMappedBlocksEqBENoChange with bentryShares0;
          try(assumption). unfold CBlockEntry.
        assert(blockindex bentryShares0 < kernelStructureEntriesNb) by (apply Hidx).
        destruct (Compare_dec.lt_dec (blockindex bentryShares0) kernelStructureEntriesNb); try(lia).
        simpl. reflexivity.
      }
      rewrite HgetBlocksPartEq in HblockMapped.
      specialize(HblockEquivInParent (parent pdentryPart) part blockToShareInCurrPartAddr blockToCutStartAddr
        blockToCutEndAddr HparentIsPart HpartIsChild HblockMapped HstartBlock HendBlocks1 HPFlag).
      destruct HblockEquivInParent as [blockParent [startParent [endParent (HblockParentMapped & HstartParent &
        HendParent & HlebStarts & HlebEnds)]]]. exists blockParent. exists endParent.
      assert(HgetBlocksParentEqss1: getMappedBlocks (parent pdentryPart) s
                                    = getMappedBlocks (parent pdentryPart) s1).
      {
        assert(Hss3: getMappedBlocks (parent pdentryPart) s = getMappedBlocks (parent pdentryPart) s3).
        {
          rewrite Hs. apply getMappedBlocksEqSCE. unfold isPDT. rewrite Hs in HlookupParent.
          simpl in HlookupParent. destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) (parent pdentryPart))
            eqn:HbeqNewScePart; try(exfalso; congruence). rewrite <-beqAddrFalse in HbeqNewScePart.
          rewrite removeDupIdentity in HlookupParent; try(apply not_eq_sym; assumption). rewrite HlookupParent.
          trivial.
          unfold isSCE. rewrite HlookupNewSces3. trivial.
        }
        assert(Hs3s2: getMappedBlocks (parent pdentryPart) s3 = getMappedBlocks (parent pdentryPart) s2).
        {
          destruct blockToShareEnabled.
          - assert(HtrivTrue: is_true true) by (unfold is_true; reflexivity). specialize(Henabled HtrivTrue).
            destruct Henabled as [pdentryCurrs (Hs3 & Henabled)]. rewrite Hs3.
            apply getMappedBlocksEqPDT with pdentryCurrs2; try(assumption).
            unfold consistency1 in *; intuition. simpl. reflexivity.
          - assert(HtrivFalse: ~is_true false) by (unfold is_true; intro Hcontra; congruence).
            specialize(HnotEnabled HtrivFalse). subst s3. reflexivity.
        }
        rewrite Hss3. rewrite Hs3s2. rewrite Hs2. apply getMappedBlocksEqBENoChange with bentryShares0;
          try(assumption). unfold CBlockEntry.
        assert(blockindex bentryShares0 < kernelStructureEntriesNb) by (apply Hidx).
        destruct (Compare_dec.lt_dec (blockindex bentryShares0) kernelStructureEntriesNb); try(lia).
        simpl. reflexivity.
      }
      rewrite HgetBlocksParentEqss1. split. assumption.
      assert(HlookupBlockSces2: lookup (CPaddr (blockToShareInCurrPartAddr + scoffset)) (memory s2) beqAddr
                                = Some (SCE scentryBlock)).
      {
        destruct blockToShareEnabled.
        - assert(HtrivTrue: is_true true) by (unfold is_true; reflexivity). specialize(Henabled HtrivTrue).
          destruct Henabled as [pdentryCurrs (Hs3 & Henabled)]. rewrite Hs3 in HlookupBlockSces3.
          simpl in HlookupBlockSces3.
          destruct (beqAddr currentPart (CPaddr (blockToShareInCurrPartAddr + scoffset))) eqn:HbeqCurrBlockSce;
            try(exfalso; congruence). rewrite <-beqAddrFalse in HbeqCurrBlockSce.
          rewrite removeDupIdentity in HlookupBlockSces3; try(apply not_eq_sym; assumption). assumption.
        - assert(HtrivFalse: ~is_true false) by (unfold is_true; intro Hcontra; congruence).
          specialize(HnotEnabled HtrivFalse). subst s3. assumption.
      }
      assert(HlookupBlockSces1: lookup (CPaddr (blockToShareInCurrPartAddr + scoffset)) (memory s1) beqAddr
                                = Some (SCE scentryBlock)).
      {
        rewrite Hs2 in HlookupBlockSces2. simpl in HlookupBlockSces2.
        destruct (beqAddr blockToShareInCurrPartAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)))
          eqn:HbeqBlockBlockSce; try(exfalso; congruence). rewrite <-beqAddrFalse in HbeqBlockBlockSce.
        rewrite removeDupIdentity in HlookupBlockSces2; try(apply not_eq_sym; assumption). assumption.
      }
      assert(HlookupNewSces2: lookup (CPaddr (idNewSubblock + scoffset)) (memory s2) beqAddr
                                = Some (SCE scentryNew)).
      {
        destruct blockToShareEnabled.
        - assert(HtrivTrue: is_true true) by (unfold is_true; reflexivity). specialize(Henabled HtrivTrue).
          destruct Henabled as [pdentryCurrs (Hs3 & Henabled)]. rewrite Hs3 in HlookupNewSces3.
          simpl in HlookupNewSces3.
          destruct (beqAddr currentPart (CPaddr (idNewSubblock + scoffset))) eqn:HbeqCurrBlockSce;
            try(exfalso; congruence). rewrite <-beqAddrFalse in HbeqCurrBlockSce.
          rewrite removeDupIdentity in HlookupNewSces3; try(apply not_eq_sym; assumption). assumption.
        - assert(HtrivFalse: ~is_true false) by (unfold is_true; intro Hcontra; congruence).
          specialize(HnotEnabled HtrivFalse). subst s3. assumption.
      }
      assert(HlookupNewSces1: lookup (CPaddr (idNewSubblock + scoffset)) (memory s1) beqAddr
                                = Some (SCE scentryNew)).
      {
        rewrite Hs2 in HlookupNewSces2. simpl in HlookupNewSces2.
        destruct (beqAddr blockToShareInCurrPartAddr (CPaddr (idNewSubblock + scoffset)))
          eqn:HbeqBlockBlockSce; try(exfalso; congruence). rewrite <-beqAddrFalse in HbeqBlockBlockSce.
        rewrite removeDupIdentity in HlookupNewSces2; try(apply not_eq_sym; assumption). assumption.
      }
      assert(HlookupBlockParentEq: lookup blockParent (memory newS) beqAddr
                                    = lookup blockParent (memory s1) beqAddr).
      {
        unfold bentryStartAddr in HstartParent. simpl.
        destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) blockParent) eqn:HbeqBlockSceBlockP.
        {
          rewrite <-beqAddrTrue in HbeqBlockSceBlockP. subst blockParent.
          rewrite HlookupBlockSces1 in HstartParent. exfalso; congruence.
        }
        rewrite <-beqAddrFalse in HbeqBlockSceBlockP.
        rewrite removeDupIdentity; try(apply not_eq_sym; assumption). rewrite Hs. simpl.
        destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) blockParent) eqn:HbeqNewSceBlockP.
        {
          rewrite <-beqAddrTrue in HbeqNewSceBlockP. subst blockParent.
          rewrite HlookupNewSces1 in HstartParent. exfalso; congruence.
        }
        rewrite <-beqAddrFalse in HbeqNewSceBlockP.
        rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
        assert(Hs3s2: lookup blockParent (memory s3) beqAddr = lookup blockParent (memory s2) beqAddr).
        {
          destruct blockToShareEnabled.
          - assert(HtrivTrue: is_true true) by (unfold is_true; reflexivity). specialize(Henabled HtrivTrue).
            destruct Henabled as [pdentryCurrs (Hs3 & Henabled)]. rewrite Hs3. simpl.
            destruct (beqAddr currentPart blockParent) eqn:HbeqCurrBlockP.
            {
              rewrite <-beqAddrTrue in HbeqCurrBlockP. subst blockParent. rewrite Hs2 in HlookupCurrs2.
              simpl in HlookupCurrs2. destruct (beqAddr blockToShareInCurrPartAddr currentPart) eqn:HbeqBlockCurr;
                try(exfalso; congruence). rewrite <-beqAddrFalse in HbeqBlockCurr.
              rewrite removeDupIdentity in HlookupCurrs2; try(apply not_eq_sym; assumption).
              rewrite HlookupCurrs2 in HstartParent. exfalso; congruence.
            }
            rewrite <-beqAddrFalse in HbeqCurrBlockP.
            rewrite removeDupIdentity; try(apply not_eq_sym; assumption). reflexivity.
          - assert(HtrivFalse: ~is_true false) by (unfold is_true; intro Hcontra; congruence).
            specialize(HnotEnabled HtrivFalse). subst s3. reflexivity.
        }
        rewrite Hs3s2. rewrite Hs2. simpl.
        destruct (beqAddr blockToShareInCurrPartAddr blockParent) eqn:HbeqBlocks.
        {
          exfalso. rewrite <-beqAddrTrue in HbeqBlocks. subst blockParent.
          assert(Hdisjoint: DisjointKSEntries s1) by (unfold consistency1 in *; intuition).
          assert(HparentIsPDT: isPDT (parent pdentryPart) s1).
          {
            apply partitionsArePDT; try(assumption). unfold consistency1 in *; intuition.
            unfold consistency1 in *; intuition.
          }
          assert(HpartIsPDT: isPDT part s1).
          {
            apply childrenArePDT with (parent pdentryPart); try(assumption). unfold consistency1 in *; intuition.
          }
          specialize(Hdisjoint (parent pdentryPart) part HparentIsPDT HpartIsPDT HbeqParentPart).
          destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
          unfold getMappedBlocks in HblockMapped. unfold getMappedBlocks in HblockParentMapped.
          apply InFilterPresentInList in HblockMapped. apply InFilterPresentInList in HblockParentMapped.
          specialize(Hdisjoint blockToShareInCurrPartAddr HblockParentMapped). congruence.
        }
        rewrite <-beqAddrFalse in HbeqBlocks. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
        reflexivity.
      }
      split. unfold bentryEndAddr. rewrite HlookupBlockParentEq. assumption. rewrite HlookupBlocks in HendBlock.
      rewrite Hs2 in HlookupBlocks2. simpl in HlookupBlocks2.
      rewrite InternalLemmas.beqAddrTrue in HlookupBlocks2. unfold CBlockEntry in HlookupBlocks2.
      assert(blockindex bentryShares0 < kernelStructureEntriesNb) by (apply Hidx).
      destruct (Compare_dec.lt_dec (blockindex bentryShares0) kernelStructureEntriesNb); try(lia).
      injection HlookupBlocks2 as HbentriesEq. rewrite <-HbentriesEq in HendBlock. simpl in HendBlock.
      unfold CBlock in HendBlock. assert(cutAddr <= maxIdx) by (rewrite maxIdxEqualMaxAddr; apply Hp).
      destruct (Compare_dec.le_dec (cutAddr - startAddr (blockrange bentryShares0)) maxIdx); try(lia).
      simpl in HendBlock. subst endaddr.
      assert(HleEndCut: false = StateLib.Paddr.leb blockToCutEndAddr cutAddr) by assumption.
      apply eq_sym in HleEndCut. unfold StateLib.Paddr.leb in HleEndCut. apply PeanoNat.Nat.leb_gt in HleEndCut.
      split. lia.
      intros addr HaddrInBlock. cbn -[newS]. rewrite HlookupBlockParentEq. unfold bentryStartAddr in HstartParent.
      unfold bentryEndAddr in HendParent.
      destruct (lookup blockParent (memory s1) beqAddr); try(simpl; congruence).
      destruct v; try(simpl; congruence). rewrite <-HstartParent. rewrite <-HendParent. rewrite app_nil_r.
      cbn -[newS] in HaddrInBlock. rewrite HlookupBlockEq in HaddrInBlock. rewrite HlookupBlocks in HaddrInBlock.
      unfold bentryStartAddr in HstartBlock. unfold bentryEndAddr in HendBlocks1. rewrite HlookupBlocks1 in *.
      rewrite <-HbentriesEq in HaddrInBlock. simpl in HaddrInBlock. rewrite app_nil_r in HaddrInBlock.
      unfold CBlock in HaddrInBlock.
      destruct (Compare_dec.le_dec (cutAddr - startAddr (blockrange bentryShares0)) maxIdx); try(lia).
      simpl in HaddrInBlock. rewrite <-HstartBlock in HaddrInBlock. apply getAllPaddrBlockInclRev in HaddrInBlock.
      destruct HaddrInBlock as (HlebStartAddr & HltAddrCut & _). apply getAllPaddrBlockIncl; lia.
    - assert(HlookupBlockEq: lookup block (memory newS) beqAddr = lookup block (memory s) beqAddr).
      {
        simpl. unfold bentryEndAddr in HendBlock. simpl in HendBlock.
        destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) block) eqn:HbeqBlockSceBlock;
          try(exfalso; congruence). rewrite <-beqAddrFalse in HbeqBlockSceBlock.
        rewrite removeDupIdentity; try(apply not_eq_sym; assumption). reflexivity.
      }
      unfold bentryEndAddr in HendBlock. rewrite HlookupBlockEq in HendBlock.
      assert(Hnexts: scentryNext scentryaddr scnext s).
      {
        unfold scentryNext in *. simpl in Hnext.
        destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) scentryaddr) eqn:HbeqBlockSceBlockSce.
        {
          rewrite <-beqAddrTrue in HbeqBlockSceBlockSce. rewrite Hsce in HbeqBlockSceBlockSce.
          unfold CPaddr in HbeqBlockSceBlockSce. exfalso.
          destruct (Compare_dec.le_dec (blockToShareInCurrPartAddr + scoffset) maxAddr) eqn:HleBlockSceMax.
          - destruct (Compare_dec.le_dec (block + scoffset) maxAddr).
            + injection HbeqBlockSceBlockSce as HscesEq. apply PeanoNat.Nat.add_cancel_r in HscesEq.
              rewrite <-beqAddrFalse in HbeqBlocks. contradict HbeqBlocks. destruct blockToShareInCurrPartAddr.
              destruct block. simpl in HscesEq. subst p0. f_equal. apply proof_irrelevance.
            + assert(Hcontra: CPaddr (blockToShareInCurrPartAddr + scoffset) = nullAddr).
              {
                unfold nullAddr. unfold CPaddr. rewrite HleBlockSceMax. rewrite HbeqBlockSceBlockSce.
                destruct (Compare_dec.le_dec 0 maxAddr); try(lia). f_equal. apply proof_irrelevance.
              }
              assert(Hnull: nullAddrExists s) by (unfold consistency1 in *; intuition). rewrite Hcontra in *.
              unfold nullAddrExists in Hnull. unfold isPADDR in Hnull. rewrite HlookupBlockSces in Hnull.
              congruence.
          - assert(Hcontra: CPaddr (blockToShareInCurrPartAddr + scoffset) = nullAddr).
            {
              unfold nullAddr. unfold CPaddr. rewrite HleBlockSceMax.
              destruct (Compare_dec.le_dec 0 maxAddr); try(lia). f_equal. apply proof_irrelevance.
            }
            assert(Hnull: nullAddrExists s) by (unfold consistency1 in *; intuition). rewrite Hcontra in *.
            unfold nullAddrExists in Hnull. unfold isPADDR in Hnull. rewrite HlookupBlockSces in Hnull.
            congruence.
        }
        rewrite <-beqAddrFalse in HbeqBlockSceBlockSce.
        rewrite removeDupIdentity in Hnext; try(apply not_eq_sym); assumption.
      }
      specialize(Hcons0 part pdentryPart block scentryaddr scnext endaddr HpartIsPart HlookupParts HblockMapped
          HendBlock Hsce HbeqSceNull Hnexts HbeqPartRoot).
      destruct Hcons0 as [blockParent [endParent (HblockParentMapped & HendParent & Hends & Hincl)]].
      exists blockParent. exists endParent.
      assert(HlookupBlockParentEq: lookup blockParent (memory newS) beqAddr
                                    = lookup blockParent (memory s) beqAddr).
      {
        simpl. destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) blockParent)
            eqn:HbeqBlockSceBlockP.
        {
          rewrite <-beqAddrTrue in HbeqBlockSceBlockP. subst blockParent. unfold bentryEndAddr in HendParent.
          rewrite HlookupBlockSces in HendParent. exfalso; congruence.
        }
        rewrite <-beqAddrFalse in HbeqBlockSceBlockP.
        rewrite removeDupIdentity; try(apply not_eq_sym; assumption). reflexivity.
      }
      split. assumption. split. unfold bentryEndAddr. rewrite HlookupBlockParentEq. assumption. split.
      assumption. cbn -[newS]. simpl in Hincl. rewrite HlookupBlockEq. rewrite HlookupBlockParentEq.
      assumption.
    (* END nextImpliesBlockWasCut *)
  }

  unfold consistency1. intuition.
}
  intro. eapply bindRev.
{ (** Internal.enableBlockInMPU **)
  eapply weaken. apply enableBlockInMPUconsist1.
  intros s Hprops. simpl. split. eapply Hprops.
  destruct Hprops as [s4 [s3 [s2 [s1 [s0 [predCurrentNbFreeSlots [sceaddr [newFirstFreeSlotAddr
    [scentry [scentryNew [scentryShares4 [pdentryCurrs0 [pdentryInter0 [pdentryCurrs2 [bentry [bentry0
    [bentry1 [bentry2 [bentry3 [bentry4 [bentry5 [bentry6 [bentryShares0 [bentryShares2 (Hs & Hconsists &
    HlookupBlockSces4 & HlookupBlocks4 & HbeqNewBlock & HbeqNewSceBlockSce & Hsceaddr & Hs4 & Hconsists4 &
    HblockIsNotFree & Hprops)]]]]]]]]]]]]]]]]]]]]]]]]. split. assumption.
  destruct Hprops as (HnewIsNotFree & Hconsists3 & HcurrIsPDTs3 & HnewIsBEs3 & HPDTEqs3s2 & HgetKScurrEqs3s2 &
    HnextBlocks3 & HlookupNews3 & HlookupNewSces3 & HgetPartsEqs3s2 & HgetConfEqs3s2 & HgetAccBlocksEqs3s2 &
    HgetChildrenEqs3s2 & HgetBlocksEqs3s2 & HgetPaddrEqs3s2 & HgetAccPaddrEqs3s2 & HnotEnabled & Henabled &
    Hs2 & Hconsists2 & HnewIsBEs2 & HlookupNews2 & HcurrIsPDTs2 & HlookupCurrs2 & HsceaddrIsSCEs2 & HfirstIsBEs2
    & HnbFrees2 & HAFlagBlocks2 & HPDFlagBlocks2 & HlookupBlocks2 & HMPUCurr & Hpropss2s1 & Hs1 & Hconsists1 &
    HPDFlagBlocks1 & Hpropss0). split.
  {
    intro Hcontra. assert(Hnull: nullAddrExists s3) by (unfold consistency1 in *; intuition).
    unfold nullAddrExists in Hnull. unfold isPADDR in Hnull. unfold isPDT in HcurrIsPDTs3. rewrite Hcontra in *.
    destruct (lookup nullAddr (memory s3) beqAddr); try(congruence). destruct v; congruence.
  }
  split.
  {
    unfold isPDT. rewrite Hs. simpl.
    destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) currentPart) eqn:HbeqBlockSceCurr.
    {
      rewrite <-beqAddrTrue in HbeqBlockSceCurr. rewrite HbeqBlockSceCurr in *.
      unfold scentryNext in HnextBlocks3. unfold isPDT in HcurrIsPDTs3.
      destruct (lookup currentPart (memory s3) beqAddr); try(congruence). destruct v; congruence.
    }
    rewrite <-beqAddrFalse in HbeqBlockSceCurr. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
    rewrite Hs4. simpl. destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) currentPart) eqn:HbeqNewSceCurr.
    {
      rewrite <-beqAddrTrue in HbeqNewSceCurr. rewrite HbeqNewSceCurr in *. unfold isPDT in HcurrIsPDTs3.
      rewrite HlookupNewSces3 in HcurrIsPDTs3. congruence.
    }
    rewrite <-beqAddrFalse in HbeqNewSceCurr. rewrite removeDupIdentity; intuition.
  }
  intro HbeqNewNull. (*assert(HnbFrees0: pdentryNbFreeSlots currentPart nbFreeSlots s0) by intuition.*)
  assert(HfirstFree: pdentryFirstFreeSlot currentPart idNewSubblock s0) by intuition.
  assert(HlookupCurrs0: lookup currentPart (memory s0) beqAddr = Some (PDT pdentryCurrs0)) by intuition.
  assert(HcurrIsPDTs0: isPDT currentPart s0) by (unfold isPDT; rewrite HlookupCurrs0; trivial).
  unfold pdentryFirstFreeSlot in HfirstFree. rewrite HlookupCurrs0 in HfirstFree. rewrite <-HfirstFree in *.
  assert(Hbentry6: exists l, bentry6 = {|
                                         read := blockR;
                                         write := blockW;
                                         exec := blockX;
                                         present := true;
                                         accessible := true;
                                         blockindex := blockindex bentry1;
                                         blockrange := blockrange bentry1;
                                         Hidx := l
                                       |}).
  {
    assert(Hbentry6: bentry6 = CBlockEntry (read bentry5) (write bentry5) blockX (present bentry5)
             (accessible bentry5) (blockindex bentry5) (blockrange bentry5)) by intuition.
    assert(Hbentry5: bentry5 = CBlockEntry (read bentry4) blockW (exec bentry4) (present bentry4)
             (accessible bentry4) (blockindex bentry4) (blockrange bentry4)) by intuition.
    assert(Hbentry4: bentry4 = CBlockEntry blockR (write bentry3) (exec bentry3) (present bentry3)
             (accessible bentry3) (blockindex bentry3) (blockrange bentry3)) by intuition.
    assert(Hbentry3: bentry3 = CBlockEntry (read bentry2) (write bentry2) (exec bentry2) (present bentry2) true
             (blockindex bentry2) (blockrange bentry2)) by intuition.
    assert(Hbentry2: bentry2 = CBlockEntry (read bentry1) (write bentry1) (exec bentry1) true
             (accessible bentry1) (blockindex bentry1) (blockrange bentry1)) by intuition.
    assert(blockindex bentry5 < kernelStructureEntriesNb) by (apply Hidx).
    assert(blockindex bentry4 < kernelStructureEntriesNb) by (apply Hidx).
    assert(blockindex bentry3 < kernelStructureEntriesNb) by (apply Hidx).
    assert(blockindex bentry2 < kernelStructureEntriesNb) by (apply Hidx).
    assert(blockindex bentry1 < kernelStructureEntriesNb) by (apply Hidx).
    unfold CBlockEntry in *.
    destruct (Compare_dec.lt_dec (blockindex bentry5) kernelStructureEntriesNb); try(lia).
    destruct (Compare_dec.lt_dec (blockindex bentry4) kernelStructureEntriesNb); try(lia).
    destruct (Compare_dec.lt_dec (blockindex bentry3) kernelStructureEntriesNb); try(lia).
    destruct (Compare_dec.lt_dec (blockindex bentry2) kernelStructureEntriesNb); try(lia).
    destruct (Compare_dec.lt_dec (blockindex bentry1) kernelStructureEntriesNb); try(lia).
    subst bentry6. subst bentry5. simpl in *. subst bentry4. simpl in *. subst bentry3. simpl in *.
    subst bentry2. simpl in *. exists (ADT.CBlockEntry_obligation_1 (blockindex bentry1) l). reflexivity.
  }
  destruct Hbentry6 as [l Hbentry6].
  assert(HaccMappeds1: In idNewSubblock (getAccessibleMappedBlocks currentPart s2)).
  {
    apply accessibleBlockIsAccessibleMapped.
    - destruct Hpropss2s1 as [slotsList [sInter [_ [_ [_ [_ (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
        _ & HgetKSEq & _)]]]]]]. destruct HgetKSEq as [KSlist (_ & HgetKSs2 & _ & Hres)]. subst KSlist.
      unfold getMappedBlocks. apply presentIsInFilterPresent with bentry6; try(assumption). rewrite Hbentry6.
      simpl. reflexivity.
    - unfold bentryAFlag. rewrite HlookupNews2. rewrite Hbentry6. simpl. reflexivity.
  }
  assert(HgetAccBlockEqss2: getAccessibleMappedBlocks currentPart s = getAccessibleMappedBlocks currentPart s2).
  {
    assert(HgetAccBlockEqs3s2: getAccessibleMappedBlocks currentPart s3
                                = getAccessibleMappedBlocks currentPart s2).
    {
      destruct blockToShareEnabled.
      - assert(Htriv: is_true true) by (unfold is_true; reflexivity). specialize(Henabled Htriv).
        destruct Henabled as [pdentryCurrs3 (Hs3 & Henabled)]. rewrite Hs3.
        apply getAccessibleMappedBlocksEqPDT with pdentryCurrs2. assumption.
        unfold consistency1 in *; intuition. simpl. reflexivity.
      - assert(Htriv: ~ is_true false) by (unfold is_true; intro Hcontra; congruence). specialize(HnotEnabled Htriv).
        subst s3. reflexivity.
    }
    assert(HgetAccBlockEqs4s3: getAccessibleMappedBlocks currentPart s4
                                = getAccessibleMappedBlocks currentPart s3).
    {
      rewrite Hs4. apply getAccessibleMappedBlocksEqSCE. assumption. unfold isSCE. rewrite HlookupNewSces3.
      trivial.
    }
    rewrite <-HgetAccBlockEqs3s2. rewrite <-HgetAccBlockEqs4s3. rewrite Hs. apply getAccessibleMappedBlocksEqSCE.
    - unfold isPDT. rewrite Hs4. simpl.
      destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) currentPart) eqn:HbeqNewSceCurr.
      {
        rewrite <-beqAddrTrue in HbeqNewSceCurr. rewrite HbeqNewSceCurr in *. unfold isPDT in HcurrIsPDTs3.
        rewrite HlookupNewSces3 in HcurrIsPDTs3. congruence.
      }
      rewrite <-beqAddrFalse in HbeqNewSceCurr. rewrite removeDupIdentity; intuition.
    - unfold isSCE. rewrite HlookupBlockSces4. trivial.
  }
  rewrite HgetAccBlockEqss2. assumption.
}
  intro newSubEnabled. eapply weaken. apply WP.ret.
  intros s Hprops. simpl. destruct Hprops as [s5 (Hprops & Hconsists5 & HcurrIsPDTs5 & Hconsist1s & HbeqCurrNull
    & _ & HcurrIsPDTs & [pdentryCurrs5 (HlookupCurrs5 & HgetKScurrEqss5 & (HmultIsPDTs & HgetKSEqss5 &
    HgetPaddrEqss5 & HgetConfigEqss5 & HgetPartsEqss5 & HgetChildrenEqss5 & HgetBlocksEqss5 & HgetAccBlocksEqss5
    & HgetAccPaddrEqss5) & HPDTEqss5 & HnewEnabled & HnewNotEnabled)])].
  destruct Hprops as [s4 [s3 [s2 [s1 [s0 [predCurrentNbFreeSlots [sceaddr [newFirstFreeSlotAddr [scentry
    [scentryNew [scentryShares4 [pdentryCurrs0 [pdentryInter0 [pdentryCurrs2 [bentry [bentry0 [bentry1 [bentry2
    [bentry3 [bentry4 [bentry5 [bentry6 [bentryShares0 [bentryShares2 (Hs5 & _ & HlookupBlockSces4 &
    HlookupBlocks4 & HbeqNewBlock & HbeqNewSceBlockSce & Hsceaddr & Hs4 & Hconsists4 & HblockNotFree &
    HnewNotFree & Hconsists3 & HcurrIsPDTs3 & HnewIsBEs3 & HPDTEqs3s2 & HgetKSEqCurrs3s2 & HnextBlocks3 &
    HlookupNews3 & HlookupNewSces3 & HgetPartsEqs3s2 & HgetConfigEqs3s2 & HgetAccBlocksEqs3s2 &
    HgetChildrenEqs3s2 & HgetBlocksEqs3s2 & HgetPaddrEqs3s2 & HgetAccPaddrEqs3s2 & HblockNotEnabled &
    HblockEnabled & Hs2 & Hconsists2 & HnewIsBEs2 & HlookupNews2 & HcurrIsPDTs2 & HlookupCurrs2 & HsceaddrIsSCEs2
    & HfirstFreeIsBEs2 & HnbFreeCurrs2 & HAFlagBlocks2 & HPDFlagBlocks2 & HlookupBlocks2 & HMPUCurrs2 & Hprops &
    Hs1 & Hconsists1 & HPDFlagBlocks1 & HlookupBlocks1 & HKDIs0 & HVSs0 & HPIs0 & Hconsists0 & HcurrIsPDTs0 &
    HlookupCurrs0 & HcurrPart & HnbFreeCurrs0 & HfirstFreeCurrs0 & HsceaddrIsSCEs0 & HlookupBlocks0 & HendBlocks0
    & HendBlockBiss0 & HstartBlocks0 & HXFlagBlocks0 & HRFlagBlocks0 & HWFlagBlocks0 & HPFlagBlocks0 &
    HAFlagBlocks0 & HfirstFreeIsBEs0 & HendNews0 & HlookupNews0 & HblockMappedCurrs0 & HoriginBlocks0 &
    HlookupSceaddr & HPDChildBlocks0 & HparentBlockNotAcc & Hbentry6 & Hbentry5 & Hbentry4 & Hbentry3 & Hbentry2 &
    Hbentry1 & Hbentry0 & HlebCutStart & HlebEndCut & HsubCutStart & HsubEndCut & Hblock1Size &
    Hblock2Size & HpdentryInter0 & HbeqPDChildNull)]]]]]]]]]]]]]]]]]]]]]]]].
  destruct Hprops as [optionSlotsList [sInter [n0 [n1 [n2 [nbleft (Hnbleft & HltnbleftMax & Hs1Inter &
    HgetFreeSlotsListsInter & HgetFreeSlotsLists1 & HgetFreeSlotsLists0 & Hlebn0n1 & Hltnbleftn0 & Hlebn1n2 &
    Hltnbleftn2 & Hlebn2MaxPlus & HwellFormedList & HnoDupList & HnewNotInList & HgetKSCurrEqs2s0 & HmultIsPDTs2
    & HgetPartsEqsInters0 & HgetPartsEqs1sInter & HgetChildrenCurrEqsInters0 & HgetChildrenCurrEqs1sInter &
    HgetConfigBCurrEqsInters0 & HgetConfigBCurrEqs1sInter & HgetConfigCurrEqsInters0 & HgetConfigCurrEqs1sInter &
    HgetBlocksCurrEqs2s0 & HgetPaddrCurrEqs2s0 & HgetAccBlocksCurrEqs2s0 & HgetAccPaddrCurrEqs2s0 & HgetKSEqs2s0
    & HgetPaddrEqs2s0 & HgetConfigEqs2s0 & HgetPartsEqs2s0 & HgetChildrenEqs2s0 & HgetBlocksEqs2s0 &
    HgetAccBlocksEqs2s0 & HgetAccPaddrEqs2s0 & HPDTEqs2s0)]]]]]].
  assert(HtrivTrue: is_true true) by (unfold is_true; reflexivity).
  assert(HtrivFalse: ~ is_true false) by (unfold is_true; intro Hcontra; congruence).

  (*assert(HgetCurrPartEqs1s0: currentPartition s1 = currentPartition s0).
  {
    rewrite Hs1. simpl. reflexivity.
  }
  assert(HgetCurrPartEqs2s1: currentPartition s2 = currentPartition s1).
  {
    rewrite Hs2. simpl. reflexivity.
  }
  assert(HgetCurrPartEqs3s2: currentPartition s3 = currentPartition s2).
  {
    destruct blockToShareEnabled.
    - specialize(HblockEnabled HtrivTrue). destruct HblockEnabled as [pdentryCurrs3 (Hs3 & HblockEnabled)].
      rewrite Hs3. simpl. reflexivity.
    - specialize(HblockNotEnabled HtrivFalse). subst s3. reflexivity.
  }
  assert(HgetCurrPartEqs4s3: currentPartition s4 = currentPartition s3).
  {
    rewrite Hs4. simpl. reflexivity.
  }
  assert(HgetCurrPartEqs5s4: currentPartition s5 = currentPartition s4).
  {
    rewrite Hs5. simpl. reflexivity.
  }
  assert(HgetCurrPartEqss5: currentPartition s = currentPartition s5).
  {
    destruct newSubEnabled.
    - specialize(HnewEnabled HtrivTrue). destruct HnewEnabled as [pdentryCurrs3 (Hs & HnewEnabled)].
      rewrite Hs. simpl. reflexivity.
    - specialize(HnewNotEnabled HtrivFalse). subst s. reflexivity.
  }*)

  assert(HgetPartsEqss0: getPartitions multiplexer s = getPartitions multiplexer s0).
  {
    rewrite <-HgetPartsEqsInters0. rewrite <-HgetPartsEqs1sInter.
    assert(HgetPartsCurrEqs2s1: getPartitions multiplexer s2 = getPartitions multiplexer s1).
    {
      rewrite Hs2. apply getPartitionsEqBEPDflagFalse with bentryShares0
          (CPaddr (blockToShareInCurrPartAddr + sh1offset)); try(assumption).
      unfold consistency1 in *; intuition.
      unfold consistency1 in *; intuition.
      apply lookupSh1EntryAddr with bentryShares0. assumption.
    }
    assert(HgetPartsCurrEqs3s2: getPartitions multiplexer s3 = getPartitions multiplexer s2).
    {
      destruct blockToShareEnabled.
      - specialize(HblockEnabled HtrivTrue). destruct HblockEnabled as [pdentryCurrs3 (Hs3 & HblockEnabled)].
        rewrite Hs3. apply getPartitionsEqPDT with pdentryCurrs2; try(assumption).
        simpl. reflexivity.
        unfold consistency1 in *; intuition.
        unfold consistency1 in *; intuition.
      - specialize(HblockNotEnabled HtrivFalse). subst s3. reflexivity.
    }
    assert(HgetPartsCurrEqs4s3: getPartitions multiplexer s4 = getPartitions multiplexer s3).
    {
      rewrite Hs4. apply getPartitionsEqSCE.
      unfold consistency1 in *; intuition.
      unfold isSCE. rewrite HlookupNewSces3. trivial.
      unfold consistency1 in *; intuition.
    }
    assert(HgetPartsCurrEqs5s4: getPartitions multiplexer s5 = getPartitions multiplexer s4).
    {
      rewrite Hs5. apply getPartitionsEqSCE.
      unfold consistency1 in *; intuition.
      unfold isSCE. rewrite HlookupBlockSces4. trivial.
      unfold consistency1 in *; intuition.
    }
    rewrite <-HgetPartsCurrEqs2s1. rewrite <-HgetPartsCurrEqs3s2. rewrite <-HgetPartsCurrEqs4s3.
    rewrite <-HgetPartsCurrEqs5s4. destruct newSubEnabled.
    - specialize(HnewEnabled HtrivTrue). destruct HnewEnabled as [pdentryCurrs (Hs & HnewEnabled)].
      rewrite Hs. apply getPartitionsEqPDT with pdentryCurrs5; try(assumption).
      simpl. reflexivity.
      unfold consistency1 in *; intuition.
      unfold consistency1 in *; intuition.
    - specialize(HnewNotEnabled HtrivFalse). subst s. reflexivity.
  }

  assert(HPDTEqs4s3: forall partition, isPDT partition s4 = isPDT partition s3).
  {
    intro part. unfold isPDT at 1. rewrite Hs4. simpl.
    destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) part) eqn:HbeqNewScePart.
    {
      rewrite <-beqAddrTrue in HbeqNewScePart. subst part. unfold isPDT. rewrite HlookupNewSces3. reflexivity.
    }
    rewrite <-beqAddrFalse in HbeqNewScePart. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
    reflexivity.
  }

  assert(HPDTEqs5s4: forall partition, isPDT partition s5 = isPDT partition s4).
  {
    intro part. unfold isPDT at 1. rewrite Hs5. simpl.
    destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) part) eqn:HbeqBlockScePart.
    {
      rewrite <-beqAddrTrue in HbeqBlockScePart. subst part. unfold isPDT. rewrite HlookupBlockSces4. reflexivity.
    }
    rewrite <-beqAddrFalse in HbeqBlockScePart. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
    reflexivity.
  }

  assert(HgetChildrenEqss0: forall part, isPDT part s0 -> getChildren part s = getChildren part s0).
  {
    intros part HpartIsPDT.
    assert(HgetChildrenPartEqs2s0: getChildren part s2 = getChildren part s0).
    {
      destruct (beqAddr part currentPart) eqn:HbeqPartCurr.
      - rewrite <-beqAddrTrue in HbeqPartCurr. subst part. rewrite <-HgetChildrenCurrEqsInters0.
        rewrite <-HgetChildrenCurrEqs1sInter. rewrite Hs2. apply getChildrenEqBEPDflagFalse with bentryShares0
          (CPaddr (blockToShareInCurrPartAddr + sh1offset)); try(assumption).
        unfold isPDT in HcurrIsPDTs2. rewrite Hs2 in HcurrIsPDTs2. simpl in HcurrIsPDTs2.
        destruct (beqAddr blockToShareInCurrPartAddr currentPart) eqn:HbeqBlockCurr; try(exfalso; congruence).
        rewrite <-beqAddrFalse in HbeqBlockCurr. rewrite removeDupIdentity in HcurrIsPDTs2; intuition.
        apply lookupSh1EntryAddr with bentryShares0. assumption.
      - rewrite <-beqAddrFalse in HbeqPartCurr. apply HgetChildrenEqs2s0; assumption.
    }
    assert(HgetChildrenPartEqs3s2: getChildren part s3 = getChildren part s2).
    {
      destruct blockToShareEnabled.
      - specialize(HblockEnabled HtrivTrue). destruct HblockEnabled as [pdentryCurrs3 (Hs3 & HblockEnabled)].
        rewrite Hs3. apply getChildrenEqPDT with pdentryCurrs2; try(assumption).
        simpl. reflexivity.
        unfold consistency1 in *; intuition.
      - specialize(HblockNotEnabled HtrivFalse). subst s3. reflexivity.
    }
    assert(HgetChildrenPartEqs4s3: getChildren part s4 = getChildren part s3).
    {
      rewrite Hs4. apply getChildrenEqSCE.
      - rewrite HPDTEqs3s2. rewrite HPDTEqs2s0. assumption.
      - unfold isSCE. rewrite HlookupNewSces3. trivial.
    }
    assert(HgetChildrenPartEqs5s4: getChildren part s5 = getChildren part s4).
    {
      rewrite Hs5. apply getChildrenEqSCE.
      - rewrite <-HPDTEqs2s0 in HpartIsPDT. rewrite <-HPDTEqs3s2 in HpartIsPDT.
        rewrite <-HPDTEqs4s3 in HpartIsPDT. assumption.
      - unfold isSCE. rewrite HlookupBlockSces4. trivial.
    }
    rewrite <-HgetChildrenPartEqs2s0. rewrite <-HgetChildrenPartEqs3s2. rewrite <-HgetChildrenPartEqs4s3.
    rewrite <-HgetChildrenPartEqs5s4. destruct newSubEnabled.
    - specialize(HnewEnabled HtrivTrue). destruct HnewEnabled as [pdentryCurrs (Hs & HnewEnabled)].
      rewrite Hs. apply getChildrenEqPDT with pdentryCurrs5; try(assumption).
      simpl. reflexivity.
      unfold consistency1 in *; intuition.
    - specialize(HnewNotEnabled HtrivFalse). subst s. reflexivity.
  }

  assert(HgetPaddrCurrEqss2: forall part, isPDT part s0 -> getMappedPaddr part s = getMappedPaddr part s2).
  {
    intros part HpartIsPDT.
    assert(HgetPaddrCurrEqs3s2: getMappedPaddr part s3 = getMappedPaddr part s2).
    {
      destruct blockToShareEnabled.
      - specialize(HblockEnabled HtrivTrue). destruct HblockEnabled as [pdentryCurrs3 (Hs3 & HblockEnabled)].
        rewrite Hs3. apply getMappedPaddrEqPDT with pdentryCurrs2; try(assumption).
        simpl. reflexivity.
        unfold consistency1 in *; intuition.
      - specialize(HblockNotEnabled HtrivFalse). subst s3. reflexivity.
    }
    assert(HgetPaddrCurrEqs4s3: getMappedPaddr part s4 = getMappedPaddr part s3).
    {
      rewrite Hs4. apply getMappedPaddrEqSCE. rewrite HPDTEqs3s2. rewrite HPDTEqs2s0. assumption.
      unfold isSCE. rewrite HlookupNewSces3. trivial.
    }
    assert(HgetPaddrCurrEqs5s4: getMappedPaddr part s5 = getMappedPaddr part s4).
    {
      rewrite Hs5. apply getMappedPaddrEqSCE. rewrite HPDTEqs4s3. rewrite HPDTEqs3s2. rewrite HPDTEqs2s0.
      assumption. unfold isSCE. rewrite HlookupBlockSces4. trivial.
    }
    assert(HgetPaddrCurrEqss5: getMappedPaddr part s = getMappedPaddr part s5).
    {
      destruct newSubEnabled.
      - specialize(HnewEnabled HtrivTrue). destruct HnewEnabled as [pdentryCurrs (Hs & HnewEnabled)].
        rewrite Hs. apply getMappedPaddrEqPDT with pdentryCurrs5; try(assumption).
        simpl. reflexivity.
        unfold consistency1 in *; intuition.
      - specialize(HnewNotEnabled HtrivFalse). subst s. reflexivity.
    }
    rewrite HgetPaddrCurrEqss5. rewrite HgetPaddrCurrEqs5s4. rewrite HgetPaddrCurrEqs4s3. assumption.
  }

  assert(HgetPaddrEqss0: forall part,
                              isPDT part s0 ->
                              forall addr, In addr (getMappedPaddr part s) <-> In addr (getMappedPaddr part s0)).
  {
    intros part HpartIsPDT addr.
    rewrite HgetPaddrCurrEqss2; try(assumption). destruct (beqAddr part currentPart) eqn:HbeqPartCurr.
    - rewrite <-beqAddrTrue in HbeqPartCurr. subst part. apply HgetPaddrCurrEqs2s0.
    - rewrite <-beqAddrFalse in HbeqPartCurr. rewrite HgetPaddrEqs2s0; try(assumption).
      split; intro Hres; assumption.
  }

  assert(HgetConfigEqss0: forall part, isPDT part s0 -> getConfigPaddr part s = getConfigPaddr part s0).
  {
    intros part HpartIsPDT.
    assert(HgetConfigEqs2s0Bis: getConfigPaddr part s2 = getConfigPaddr part s0).
    {
      destruct (beqAddr part currentPart) eqn:HbeqPartCurr.
      - rewrite <-beqAddrTrue in HbeqPartCurr. subst part. rewrite <-HgetConfigCurrEqsInters0.
        rewrite <-HgetConfigCurrEqs1sInter. rewrite Hs2. apply getConfigPaddrEqBE.
        rewrite <-HPDTEqs2s0 in HpartIsPDT. unfold isPDT in HpartIsPDT. rewrite Hs2 in HpartIsPDT.
        simpl in HpartIsPDT.
        destruct (beqAddr blockToShareInCurrPartAddr currentPart) eqn:HbeqBlockCurr; try(exfalso; congruence).
        rewrite <-beqAddrFalse in HbeqBlockCurr. rewrite removeDupIdentity in HpartIsPDT; try(apply not_eq_sym);
          assumption.
        unfold isBE. rewrite HlookupBlocks1. trivial.
      - rewrite <-beqAddrFalse in HbeqPartCurr. apply HgetConfigEqs2s0; assumption.
    }
    assert(HgetConfigEqs3s2Bis: getConfigPaddr part s3 = getConfigPaddr part s2).
    {
      destruct blockToShareEnabled.
      - specialize(HblockEnabled HtrivTrue). destruct HblockEnabled as [pdentryCurrs3 (Hs3 & HblockEnabled)].
        rewrite Hs3. apply getConfigPaddrEqPDT with pdentryCurrs2; try(assumption).
        rewrite HPDTEqs2s0. assumption.
        simpl. reflexivity.
      - specialize(HblockNotEnabled HtrivFalse). subst s3. reflexivity.
    }
    assert(HgetConfigEqs4s3: getConfigPaddr part s4 = getConfigPaddr part s3).
    {
      rewrite Hs4. apply getConfigPaddrEqSCE.
      rewrite HPDTEqs3s2. rewrite HPDTEqs2s0. assumption.
      unfold isSCE. rewrite HlookupNewSces3. trivial.
    }
    assert(HgetConfigEqs5s4: getConfigPaddr part s5 = getConfigPaddr part s4).
    {
      rewrite Hs5. apply getConfigPaddrEqSCE.
      rewrite HPDTEqs4s3. rewrite HPDTEqs3s2. rewrite HPDTEqs2s0. assumption.
      unfold isSCE. rewrite HlookupBlockSces4. trivial.
    }
    rewrite <-HgetConfigEqs2s0Bis. rewrite <-HgetConfigEqs3s2Bis. rewrite <-HgetConfigEqs4s3.
    rewrite <-HgetConfigEqs5s4. destruct newSubEnabled.
    - specialize(HnewEnabled HtrivTrue). destruct HnewEnabled as [pdentryCurrs (Hs & HnewEnabled)].
      rewrite Hs. apply getConfigPaddrEqPDT with pdentryCurrs5; try(assumption).
      rewrite HPDTEqs5s4. rewrite HPDTEqs4s3. rewrite HPDTEqs3s2. rewrite HPDTEqs2s0. assumption.
      simpl. reflexivity.
    - specialize(HnewNotEnabled HtrivFalse). subst s. reflexivity.
  }

  assert(HgetUsedEqss0: forall part,
                          isPDT part s0
                          -> forall addr, In addr (getUsedPaddr part s) <-> In addr (getUsedPaddr part s0)).
  {
    intros part HpartIsPDT addr. unfold getUsedPaddr. rewrite HgetConfigEqss0; try(assumption).
    specialize(HgetPaddrEqss0 part HpartIsPDT addr).
    destruct HgetPaddrEqss0 as (HgetPaddrEqss0Left & HgetPaddrEqss0Right). split; intro HaddrMapped.
    - apply in_or_app. apply in_app_or in HaddrMapped.
      destruct HaddrMapped as [Hconfig | Hmapped]; try(left; assumption). right. apply HgetPaddrEqss0Left.
      assumption.
    - apply in_or_app. apply in_app_or in HaddrMapped.
      destruct HaddrMapped as [Hconfig | Hmapped]; try(left; assumption). right. apply HgetPaddrEqss0Right.
      assumption.
  }

  assert(HgetAccAux: forall part,
                        isPDT part s3
                        -> getAccessibleMappedPaddr part s = getAccessibleMappedPaddr part s3).
  {
    intros part HpartIsPDT.
    assert(Hs4s3: getAccessibleMappedPaddr part s4 = getAccessibleMappedPaddr part s3).
    {
      rewrite Hs4. apply getAccessibleMappedPaddrEqSCE. assumption.
      unfold isSCE. rewrite HlookupNewSces3. trivial.
    }
    assert(Hs5s4: getAccessibleMappedPaddr part s5 = getAccessibleMappedPaddr part s4).
    {
      rewrite Hs5. apply getAccessibleMappedPaddrEqSCE. rewrite HPDTEqs4s3. assumption.
      unfold isSCE. rewrite HlookupBlockSces4. trivial.
    }
    rewrite <-Hs4s3. rewrite <-Hs5s4. destruct newSubEnabled.
    - specialize(HnewEnabled HtrivTrue). destruct HnewEnabled as [pdentryCurrs (Hs & HnewEnabled)].
      rewrite Hs. apply getAccessibleMappedPaddrEqPDT with pdentryCurrs5; try(assumption).
      simpl. reflexivity.
      unfold consistency1 in *; intuition.
    - specialize(HnewNotEnabled HtrivFalse). subst s. reflexivity.
  }

  assert(HgetAccPaddrEqss0: forall partition,
                              partition <> currentPart
                              -> isPDT partition s0
                              -> getAccessibleMappedPaddr partition s = getAccessibleMappedPaddr partition s0).
  {
    intros part HbeqPartCurr HpartIsPDT. rewrite <-HgetAccPaddrEqs2s0; try(assumption).
    rewrite <-HgetAccPaddrEqs3s2; try(assumption). apply HgetAccAux. rewrite HPDTEqs3s2. rewrite HPDTEqs2s0.
    assumption.
    rewrite HPDTEqs2s0. assumption.
  }

  assert(HgetAccPaddrCurrEqss0tmp: forall addr,
            In addr (getAccessibleMappedPaddr currentPart s) <->
            In addr (getAllPaddrBlock (startAddr (blockrange bentry6)) (endAddr (blockrange bentry6))
                      ++ getAccessibleMappedPaddr currentPart s0)).
  {
    assert(Hs3s2: getAccessibleMappedPaddr currentPart s3 = getAccessibleMappedPaddr currentPart s2).
    {
      destruct blockToShareEnabled.
      - specialize(HblockEnabled HtrivTrue). destruct HblockEnabled as [pdentryCurrs3 (Hs3 & HblockEnabled)].
        rewrite Hs3. apply getAccessibleMappedPaddrEqPDT with pdentryCurrs2; try(assumption).
        simpl. reflexivity.
        unfold consistency1 in *; intuition.
      - specialize(HblockNotEnabled HtrivFalse). subst s3. reflexivity.
    }
    assert(Hs4s3: getAccessibleMappedPaddr currentPart s4 = getAccessibleMappedPaddr currentPart s3).
    {
      rewrite Hs4. apply getAccessibleMappedPaddrEqSCE.
      rewrite HPDTEqs3s2. rewrite HPDTEqs2s0. assumption.
      unfold isSCE. rewrite HlookupNewSces3. trivial.
    }
    assert(Hs5s4: getAccessibleMappedPaddr currentPart s5 = getAccessibleMappedPaddr currentPart s4).
    {
      rewrite Hs5. apply getAccessibleMappedPaddrEqSCE.
      rewrite HPDTEqs4s3. rewrite HPDTEqs3s2. rewrite HPDTEqs2s0. assumption.
      unfold isSCE. rewrite HlookupBlockSces4. trivial.
    }
    assert(Hss5: getAccessibleMappedPaddr currentPart s = getAccessibleMappedPaddr currentPart s5).
    {
      destruct newSubEnabled.
      - specialize(HnewEnabled HtrivTrue). destruct HnewEnabled as [pdentryCurrs (Hs & HnewEnabled)].
        rewrite Hs. apply getAccessibleMappedPaddrEqPDT with pdentryCurrs5; try(assumption).
        simpl. reflexivity.
        unfold consistency1 in *; intuition.
      - specialize(HnewNotEnabled HtrivFalse). subst s. reflexivity.
    }
    rewrite Hss5. rewrite Hs5s4. rewrite Hs4s3. rewrite Hs3s2. assumption.
  }

  assert(HgetBlocksEqss0: forall part,
                            isPDT part s0
                            -> part <> currentPart
                            -> getMappedBlocks part s = getMappedBlocks part s0).
  {
    intros part HpartIsPDT HbeqPartCurr. rewrite <-HgetBlocksEqs2s0; try(assumption).
    rewrite <-HgetBlocksEqs3s2; try(assumption). rewrite HgetBlocksEqss5; try(assumption).
    assert(Hs4s3: getMappedBlocks part s4 = getMappedBlocks part s3).
    {
      rewrite Hs4. apply getMappedBlocksEqSCE. rewrite HPDTEqs3s2. rewrite HPDTEqs2s0. assumption.
      unfold isSCE. rewrite HlookupNewSces3. trivial.
    }
    rewrite <-Hs4s3. rewrite Hs5. apply getMappedBlocksEqSCE.
    rewrite HPDTEqs4s3. rewrite HPDTEqs3s2. rewrite HPDTEqs2s0. assumption.
    unfold isSCE. rewrite HlookupBlockSces4. trivial.

    rewrite HPDTEqs5s4. rewrite HPDTEqs4s3. rewrite HPDTEqs3s2. rewrite HPDTEqs2s0. assumption.
    rewrite HPDTEqs2s0. assumption.
  }

  assert(HnewIsFirstFree: idNewSubblock = firstfreeslot pdentryCurrs0).
  {
    unfold pdentryFirstFreeSlot in HfirstFreeCurrs0. rewrite HlookupCurrs0 in HfirstFreeCurrs0. assumption.
  }
  rewrite <-HnewIsFirstFree in *.

  assert(HgetBlocksCurrEqss0: forall block,
            In block (getMappedBlocks currentPart s)
            <-> idNewSubblock = block \/ In block (getMappedBlocks currentPart s0)).
  {
    assert(Hs3s2: getMappedBlocks currentPart s3 = getMappedBlocks currentPart s2).
    {
      destruct blockToShareEnabled.
      - specialize(HblockEnabled HtrivTrue). destruct HblockEnabled as [pdentryCurrs3 (Hs3 & HblockEnabled)].
        rewrite Hs3. apply getMappedBlocksEqPDT with pdentryCurrs2; try(assumption).
        unfold consistency1 in *; intuition.
        simpl. reflexivity.
      - specialize(HblockNotEnabled HtrivFalse). subst s3. reflexivity.
    }
    assert(Hs4s3: getMappedBlocks currentPart s4 = getMappedBlocks currentPart s3).
    {
      rewrite Hs4. apply getMappedBlocksEqSCE. rewrite HPDTEqs3s2. rewrite HPDTEqs2s0. assumption.
      unfold isSCE. rewrite HlookupNewSces3. trivial.
    }
    assert(Hs5s4: getMappedBlocks currentPart s5 = getMappedBlocks currentPart s4).
    {
      rewrite Hs5. apply getMappedBlocksEqSCE.
      rewrite HPDTEqs4s3. rewrite HPDTEqs3s2. rewrite HPDTEqs2s0. assumption.
      unfold isSCE. rewrite HlookupBlockSces4. trivial.
    }
    assert(Hss5: getMappedBlocks currentPart s = getMappedBlocks currentPart s5).
    {
      destruct newSubEnabled.
      - specialize(HnewEnabled HtrivTrue). destruct HnewEnabled as [pdentryCurrs (Hs & HnewEnabled)].
        rewrite Hs. apply getMappedBlocksEqPDT with pdentryCurrs5; try(assumption).
        unfold consistency1 in *; intuition.
        simpl. reflexivity.
      - specialize(HnewNotEnabled HtrivFalse). subst s. reflexivity.
    }
    rewrite Hss5. rewrite Hs5s4. rewrite Hs4s3. rewrite Hs3s2. assumption.
  }

  assert(Hbentry6simpl: exists l, bentry6 = {|
                                              read := blockR;
                                              write := blockW;
                                              exec := blockX;
                                              present := true;
                                              accessible := true;
                                              blockindex := blockindex bentry;
                                              blockrange := (CBlock cutAddr blockEndAddr);
                                              Hidx := l
                                            |}).
  {
    assert(blockindex bentry5 < kernelStructureEntriesNb) by (apply Hidx).
    assert(blockindex bentry4 < kernelStructureEntriesNb) by (apply Hidx).
    assert(blockindex bentry3 < kernelStructureEntriesNb) by (apply Hidx).
    assert(blockindex bentry2 < kernelStructureEntriesNb) by (apply Hidx).
    assert(blockindex bentry1 < kernelStructureEntriesNb) by (apply Hidx).
    assert(blockindex bentry0 < kernelStructureEntriesNb) by (apply Hidx).
    assert(blockindex bentry < kernelStructureEntriesNb) by (apply Hidx).
    unfold CBlockEntry in *.
    destruct (Compare_dec.lt_dec (blockindex bentry5) kernelStructureEntriesNb); try(lia).
    destruct (Compare_dec.lt_dec (blockindex bentry4) kernelStructureEntriesNb); try(lia).
    destruct (Compare_dec.lt_dec (blockindex bentry3) kernelStructureEntriesNb); try(lia).
    destruct (Compare_dec.lt_dec (blockindex bentry2) kernelStructureEntriesNb); try(lia).
    destruct (Compare_dec.lt_dec (blockindex bentry1) kernelStructureEntriesNb); try(lia).
    destruct (Compare_dec.lt_dec (blockindex bentry0) kernelStructureEntriesNb); try(lia).
    destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
    subst bentry6. subst bentry5. simpl in *. subst bentry4. simpl in *. subst bentry3. simpl in *.
    subst bentry2. simpl in *. subst bentry1. simpl in *. subst bentry0. simpl in *.
    exists (ADT.CBlockEntry_obligation_1 (blockindex bentry) l). f_equal.
    assert(HnewStartIsCut: startAddr (CBlock cutAddr (endAddr (blockrange bentry))) = cutAddr).
    {
      unfold CBlock. assert(HendBounded: endAddr (blockrange bentry) <= maxAddr) by (apply Hp).
      rewrite <-maxIdxEqualMaxAddr in HendBounded.
      destruct (Compare_dec.le_dec (endAddr (blockrange bentry) - cutAddr) maxIdx); try(lia). simpl. reflexivity.
    }
    rewrite HnewStartIsCut. reflexivity.
  }
  destruct Hbentry6simpl as [l6 Hbentry6simpl]. unfold CBlock in Hbentry6simpl.
  assert(HendBounded: blockEndAddr <= maxAddr) by (apply Hp). rewrite <-maxIdxEqualMaxAddr in HendBounded.
  destruct (Compare_dec.le_dec (blockEndAddr - cutAddr) maxIdx); try(lia).

  destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) idNewSubblock) eqn:HbeqNewSceNew.
  {
    rewrite <-beqAddrTrue in HbeqNewSceNew. exfalso; congruence.
  }
  destruct (beqAddr currentPart idNewSubblock) eqn:HbeqCurrNew.
  {
    rewrite <-beqAddrTrue in *. exfalso; congruence.
  }
  assert(HlookupNews4: lookup idNewSubblock (memory s4) beqAddr = Some (BE bentry6)).
  {
    rewrite Hs4. simpl. rewrite HbeqNewSceNew. rewrite <-beqAddrFalse in HbeqNewSceNew.
    rewrite removeDupIdentity; intuition.
  }
  destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) idNewSubblock) eqn:HbeqBlockSceNew.
  {
    rewrite <-beqAddrTrue in HbeqBlockSceNew. exfalso; congruence.
  }
  assert(HlookupNews5: lookup idNewSubblock (memory s5) beqAddr = Some (BE bentry6)).
  {
    rewrite Hs5. simpl. rewrite HbeqBlockSceNew. rewrite <-beqAddrFalse in HbeqBlockSceNew.
    rewrite removeDupIdentity; intuition.
  }
  assert(HlookupNews: lookup idNewSubblock (memory s) beqAddr = Some (BE bentry6)).
  {
    destruct newSubEnabled.
    - specialize(HnewEnabled HtrivTrue). destruct HnewEnabled as [pdentryCurrs (Hs & HnewEnabled)]. rewrite Hs.
      simpl. rewrite HbeqCurrNew. rewrite <-beqAddrFalse in HbeqCurrNew. rewrite removeDupIdentity; intuition.
    - specialize(HnewNotEnabled HtrivFalse). subst s. assumption.
  }
  destruct (beqAddr idNewSubblock sceaddr) eqn:HbeqNewSce.
  {
    rewrite <-beqAddrTrue in HbeqNewSce. rewrite HbeqNewSce in *. unfold isSCE in HsceaddrIsSCEs0.
    rewrite HlookupNews0 in HsceaddrIsSCEs0. exfalso; congruence.
  }
  destruct (beqAddr currentPart sceaddr) eqn:HbeqCurrSce.
  {
    rewrite <-beqAddrTrue in HbeqCurrSce. rewrite HbeqCurrSce in *. exfalso. unfold isSCE in HsceaddrIsSCEs0.
    rewrite HlookupCurrs0 in HsceaddrIsSCEs0. congruence.
  }

  assert(HnewInclBlocs0: forall addr, In addr (getAllPaddrAux [idNewSubblock] s)
                                      -> In addr (getAllPaddrAux [blockToShareInCurrPartAddr] s0)).
  {
    intros addr HaddrInNew. simpl in HaddrInNew. rewrite HlookupNews in HaddrInNew.
    rewrite app_nil_r in HaddrInNew. rewrite Hbentry6simpl in HaddrInNew. simpl in HaddrInNew. simpl.
    unfold bentryStartAddr in HstartBlocks0. unfold bentryEndAddr in HendBlocks0.
    unfold bentryEndAddr in HendBlockBiss0. rewrite HlookupBlocks0 in *. rewrite app_nil_r.
    rewrite <-HendBlocks0. rewrite <-HstartBlocks0. apply getAllPaddrBlockInclRev in HaddrInNew.
    destruct HaddrInNew as (HlebCutAddr & HltAddrEnd & _). unfold StateLib.Paddr.leb in HlebCutStart.
    apply eq_sym in HlebCutStart. apply PeanoNat.Nat.leb_gt in HlebCutStart.
    apply getAllPaddrBlockIncl; lia.
  }

  assert(HnewBlocksAddrNotNew: forall addr, In addr (getAllPaddrBlock (startAddr (blockrange bentry6))
                                                                      (endAddr (blockrange bentry6)))
                                            -> In addr (getAccessibleMappedPaddr currentPart s0)).
  {
    intros addr HaddrInNew.
    assert(HaddrInNewBis: In addr (getAllPaddrAux [idNewSubblock] s)).
    {
      simpl. rewrite HlookupNews. rewrite app_nil_r. assumption.
    }
    assert(HaddrInBlock: In addr (getAllPaddrAux [blockToShareInCurrPartAddr] s0)).
    {
      apply HnewInclBlocs0. assumption.
    }
    apply addrInAccessibleBlockIsAccessibleMapped with blockToShareInCurrPartAddr; assumption.
  }

  assert(HgetAccPaddrCurrEqss0: forall addr,
            In addr (getAccessibleMappedPaddr currentPart s)
            <-> In addr (getAccessibleMappedPaddr currentPart s0)).
  {
    intro addr. specialize(HgetAccPaddrCurrEqss0tmp addr).
    destruct HgetAccPaddrCurrEqss0tmp as (HgetAccPaddrCurrEqss0Left & HgetAccPaddrCurrEqss0Right).
    split; intro Hmapped.
    - apply HgetAccPaddrCurrEqss0Left in Hmapped. apply in_app_or in Hmapped.
      destruct Hmapped as [HaddrInNew | Hres]; try(assumption). apply HnewBlocksAddrNotNew. assumption.
    - apply HgetAccPaddrCurrEqss0Right. apply in_or_app. right. assumption.
  }
  clear HgetAccPaddrCurrEqss0tmp. clear HnewBlocksAddrNotNew.

  split.
  {
    intros pdparent child1 child2 HparentIsPart Hchild1IsChild Hchild2IsChild HbeqChild1Child2.
    rewrite HgetPartsEqss0 in HparentIsPart.
    assert(HparentIsPDT: isPDT pdparent s0).
    {
      apply partitionsArePDT.
      unfold consistency in *; unfold consistency1 in *; intuition.
      unfold consistency in *; unfold consistency1 in *; intuition.
      assumption.
    }
    rewrite HgetChildrenEqss0 in Hchild1IsChild; try(assumption).
    rewrite HgetChildrenEqss0 in Hchild2IsChild; try(assumption).
    specialize(HPIs0 pdparent child1 child2 HparentIsPart Hchild1IsChild Hchild2IsChild HbeqChild1Child2).
    intros addr HaddrInChild1.
    assert(Hchild1Eq: In addr (getUsedPaddr child1 s) <-> In addr (getUsedPaddr child1 s0)).
    {
      assert(Hchild1IsPDT: isPDT child1 s0).
      {
        apply childrenArePDT with pdparent.
        unfold consistency in *; unfold consistency1 in *; intuition.
        assumption.
      }
      specialize(HgetUsedEqss0 child1 Hchild1IsPDT addr). assumption.
    }
    assert(Hchild2Eq: In addr (getUsedPaddr child2 s) <-> In addr (getUsedPaddr child2 s0)).
    {
      assert(Hchild2IsPDT: isPDT child2 s0).
      {
        apply childrenArePDT with pdparent.
        unfold consistency in *; unfold consistency1 in *; intuition.
        assumption.
      }
      specialize(HgetUsedEqss0 child2 Hchild2IsPDT addr). assumption.
    }
    destruct Hchild1Eq as (Hchild1Eq & _). specialize(Hchild1Eq HaddrInChild1). specialize(HPIs0 addr Hchild1Eq).
    contradict HPIs0. destruct Hchild2Eq as (Hchild2Eq & _). apply Hchild2Eq. assumption.
  }

  assert(HKDIs: kernelDataIsolation s).
  {
    intros part1 part2 Hpart1IsPart Hpart2IsPart addr HaddrAccMapped. rewrite HgetPartsEqss0 in Hpart1IsPart.
    rewrite HgetPartsEqss0 in Hpart2IsPart. specialize(HKDIs0 part1 part2 Hpart1IsPart Hpart2IsPart addr).
    assert(Hpart1IsPDT: isPDT part1 s0).
    {
      apply partitionsArePDT; try(assumption).
      unfold consistency in *; unfold consistency1 in *; intuition.
      unfold consistency in *; unfold consistency1 in *; intuition.
    }
    assert(Hpart2IsPDT: isPDT part2 s0).
    {
      apply partitionsArePDT; try(assumption).
      unfold consistency in *; unfold consistency1 in *; intuition.
      unfold consistency in *; unfold consistency1 in *; intuition.
    }
    rewrite HgetConfigEqss0; try(assumption).
    destruct (beqAddr part1 currentPart) eqn:HbeqPart1Curr.
    - rewrite <-beqAddrTrue in HbeqPart1Curr. subst part1. specialize(HgetAccPaddrCurrEqss0 addr).
      destruct HgetAccPaddrCurrEqss0 as (HgetAccPaddrCurrEqss0 & _).
      apply HgetAccPaddrCurrEqss0 in HaddrAccMapped. specialize(HKDIs0 HaddrAccMapped). assumption.
    - rewrite <-beqAddrFalse in HbeqPart1Curr. specialize(HgetAccPaddrEqss0 part1 HbeqPart1Curr Hpart1IsPDT).
      rewrite HgetAccPaddrEqss0 in HaddrAccMapped. specialize(HKDIs0 HaddrAccMapped). assumption.
  }

  split. assumption. split.
  {
    intros pdparent child HparentIsPart HchildIsChild addr HaddrIsUsed. rewrite HgetPartsEqss0 in HparentIsPart.
    assert(HparentIsPDT: isPDT pdparent s0).
    {
      apply partitionsArePDT; try(assumption).
      unfold consistency in *; unfold consistency1 in *; intuition.
      unfold consistency in *; unfold consistency1 in *; intuition.
    }
    rewrite HgetChildrenEqss0 in HchildIsChild; try(assumption).
    assert(HchildIsPDT: isPDT child s0).
    {
      apply childrenArePDT with pdparent; try(assumption).
      unfold consistency in *; unfold consistency1 in *; intuition.
    }
    specialize(HgetUsedEqss0 child HchildIsPDT addr). destruct HgetUsedEqss0 as (HgetUsedEqss0 & _).
    apply HgetUsedEqss0 in HaddrIsUsed.
    specialize(HVSs0 pdparent child HparentIsPart HchildIsChild addr HaddrIsUsed).
    specialize(HgetPaddrEqss0 pdparent HparentIsPDT addr). destruct HgetPaddrEqss0 as (_ & HgetPaddrEqss0).
    apply HgetPaddrEqss0. assumption.
  }

  assert(HPDTlookupEqss0: forall part, isPDT part s0
                              -> beqAddr part currentPart = false
                              -> lookup part (memory s) beqAddr = lookup part (memory s0) beqAddr).
  {
    intros part HpartIsPDT HbeqPartCurr. unfold isPDT in HpartIsPDT. rewrite beqAddrSym in HbeqPartCurr.
    destruct (beqAddr idNewSubblock part) eqn:HbeqNewPart.
    {
      rewrite <-beqAddrTrue in HbeqNewPart. subst part. rewrite HlookupNews0 in HpartIsPDT. exfalso; congruence.
    }
    destruct (beqAddr blockToShareInCurrPartAddr part) eqn:HbeqBlockPart.
    {
      rewrite <-beqAddrTrue in HbeqBlockPart. subst part. rewrite HlookupBlocks0 in HpartIsPDT.
      exfalso; congruence.
    }
    assert(HlookupEqs1: lookup part (memory s1) beqAddr = lookup part (memory s0) beqAddr).
    {
      rewrite Hs1. simpl.
      destruct (beqAddr sceaddr part) eqn:HbeqScePart.
      {
        rewrite <-beqAddrTrue in HbeqScePart. subst part. exfalso. unfold isSCE in HsceaddrIsSCEs0.
        destruct (lookup sceaddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
      }
      rewrite HbeqNewSce. simpl. rewrite HbeqNewPart.
      rewrite InternalLemmas.beqAddrTrue. rewrite HbeqCurrNew. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption). simpl. rewrite beqAddrFalse in HbeqPartCurr.
      rewrite HbeqPartCurr. rewrite InternalLemmas.beqAddrTrue. rewrite <-beqAddrFalse in HbeqPartCurr.
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption). reflexivity.
    }
    assert(HlookupEqs2: lookup part (memory s2) beqAddr = lookup part (memory s0) beqAddr).
    {
      rewrite <-HlookupEqs1. rewrite Hs2. simpl. rewrite HbeqBlockPart. rewrite <-beqAddrFalse in HbeqBlockPart.
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption). reflexivity.
    }
    assert(HlookupEqs3: lookup part (memory s3) beqAddr = lookup part (memory s0) beqAddr).
    {
      rewrite <-HlookupEqs2. destruct blockToShareEnabled.
      - specialize(HblockEnabled HtrivTrue). destruct HblockEnabled as [pdentryCurrs3 (Hs3 & HblockEnabled)].
        rewrite Hs3. simpl. rewrite HbeqPartCurr. rewrite <-beqAddrFalse in HbeqPartCurr.
        rewrite removeDupIdentity; try(apply not_eq_sym; assumption). reflexivity.
      - specialize(HblockNotEnabled HtrivFalse). subst s3. reflexivity.
    }
    assert(HlookupEqs4: lookup part (memory s4) beqAddr = lookup part (memory s0) beqAddr).
    {
      rewrite <-HlookupEqs3. rewrite Hs4. simpl.
      destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) part) eqn:HbeqNewScePart.
      {
        rewrite <-beqAddrTrue in HbeqNewScePart. subst part. rewrite HlookupNewSces3 in HlookupEqs3.
        rewrite <-HlookupEqs3 in HpartIsPDT. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in HbeqNewScePart. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      reflexivity.
    }
    assert(HlookupEqs5: lookup part (memory s5) beqAddr = lookup part (memory s0) beqAddr).
    {
      rewrite <-HlookupEqs4. rewrite Hs5. simpl.
      destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) part) eqn:HbeqBlockScePart.
      {
        rewrite <-beqAddrTrue in HbeqBlockScePart. subst part. rewrite HlookupBlockSces4 in HlookupEqs4.
        rewrite <-HlookupEqs4 in HpartIsPDT. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in HbeqBlockScePart. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      reflexivity.
    }
    rewrite <-HlookupEqs5. destruct newSubEnabled.
    - specialize(HnewEnabled HtrivTrue). destruct HnewEnabled as [pdentryCurrs (Hs & HnewEnabled)].
      rewrite Hs. simpl. rewrite HbeqPartCurr. rewrite <-beqAddrFalse in HbeqPartCurr.
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption). reflexivity.
    - specialize(HnewNotEnabled HtrivFalse). subst s. reflexivity.
  }
  destruct (beqAddr currentPart (CPaddr (blockToShareInCurrPartAddr + scoffset))) eqn:HbeqCurrBlockSce.
  {
    rewrite <-beqAddrTrue in HbeqCurrBlockSce. rewrite <-HbeqCurrBlockSce in *.
    rewrite HPDTEqs5s4 in HcurrIsPDTs5. unfold isPDT in HcurrIsPDTs5. rewrite HlookupBlockSces4 in HcurrIsPDTs5.
    exfalso; congruence.
  }
  assert(HlookupBlockSceEqss5: lookup (CPaddr (blockToShareInCurrPartAddr + scoffset)) (memory s) beqAddr
                            = lookup (CPaddr (blockToShareInCurrPartAddr + scoffset)) (memory s5) beqAddr).
  {
    destruct newSubEnabled.
    - specialize(HnewEnabled HtrivTrue). destruct HnewEnabled as [pdentryCurrs (Hs & HnewEnabled)]. rewrite Hs.
      simpl. rewrite HbeqCurrBlockSce. rewrite <-beqAddrFalse in HbeqCurrBlockSce.
      rewrite removeDupIdentity; intuition.
    - specialize(HnewNotEnabled HtrivFalse). subst s. reflexivity.
  }
  destruct (beqAddr nullAddr idNewSubblock) eqn:HbeqNullNew.
  {
    rewrite <-beqAddrTrue in HbeqNullNew. rewrite <-HbeqNullNew in *.
    assert(Hnull: nullAddrExists s) by (unfold consistency1 in *; intuition). unfold nullAddrExists in Hnull.
    unfold isPADDR in Hnull. rewrite HlookupNews in Hnull. exfalso; congruence.
  }
  assert(HBElookupEqss0: forall block, isBE block s0
                                      -> beqAddr idNewSubblock block = false
                                      -> beqAddr blockToShareInCurrPartAddr block = false
                                      -> lookup block (memory s) beqAddr = lookup block (memory s0) beqAddr).
  {
    intros block HblockIsBE HbeqNewBlockBis HbeqBlockBlock. unfold isBE in HblockIsBE.
    destruct (beqAddr currentPart block) eqn:HbeqCurrBlock.
    {
      rewrite <-beqAddrTrue in HbeqCurrBlock. subst block. rewrite HlookupCurrs0 in HblockIsBE.
      exfalso; congruence.
    }
    assert(HlookupEqs1: lookup block (memory s1) beqAddr = lookup block (memory s0) beqAddr).
    {
      rewrite Hs1. simpl.
      destruct (beqAddr sceaddr block) eqn:HbeqSceBlock.
      {
        rewrite <-beqAddrTrue in HbeqSceBlock. subst block. exfalso. unfold isSCE in HsceaddrIsSCEs0.
        destruct (lookup sceaddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
      }
      rewrite HbeqNewSce. simpl. rewrite HbeqNewBlockBis. rewrite InternalLemmas.beqAddrTrue.
      rewrite HbeqCurrNew. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption). simpl. rewrite beqAddrFalse in HbeqCurrBlock.
      rewrite HbeqCurrBlock. rewrite InternalLemmas.beqAddrTrue. rewrite <-beqAddrFalse in HbeqCurrBlock.
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption). reflexivity.
    }
    assert(HlookupEqs2: lookup block (memory s2) beqAddr = lookup block (memory s0) beqAddr).
    {
      rewrite <-HlookupEqs1. rewrite Hs2. simpl. rewrite HbeqBlockBlock. rewrite <-beqAddrFalse in HbeqBlockBlock.
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption). reflexivity.
    }
    assert(HlookupEqs3: lookup block (memory s3) beqAddr = lookup block (memory s0) beqAddr).
    {
      rewrite <-HlookupEqs2. destruct blockToShareEnabled.
      - specialize(HblockEnabled HtrivTrue). destruct HblockEnabled as [pdentryCurrs3 (Hs3 & HblockEnabled)].
        rewrite Hs3. simpl. rewrite HbeqCurrBlock. rewrite <-beqAddrFalse in HbeqCurrBlock.
        rewrite removeDupIdentity; try(apply not_eq_sym; assumption). reflexivity.
      - specialize(HblockNotEnabled HtrivFalse). subst s3. reflexivity.
    }
    assert(HlookupEqs4: lookup block (memory s4) beqAddr = lookup block (memory s0) beqAddr).
    {
      rewrite <-HlookupEqs3. rewrite Hs4. simpl.
      destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) block) eqn:HbeqNewSceBlock.
      {
        rewrite <-beqAddrTrue in HbeqNewSceBlock. subst block. rewrite HlookupNewSces3 in HlookupEqs3.
        rewrite <-HlookupEqs3 in HblockIsBE. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in HbeqNewSceBlock. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      reflexivity.
    }
    assert(HlookupEqs5: lookup block (memory s5) beqAddr = lookup block (memory s0) beqAddr).
    {
      rewrite <-HlookupEqs4. rewrite Hs5. simpl.
      destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) block) eqn:HbeqBlockSceBlock.
      {
        rewrite <-beqAddrTrue in HbeqBlockSceBlock. subst block. rewrite HlookupBlockSces4 in HlookupEqs4.
        rewrite <-HlookupEqs4 in HblockIsBE. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in HbeqBlockSceBlock. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      reflexivity.
    }
    rewrite <-HlookupEqs5. destruct newSubEnabled.
    - specialize(HnewEnabled HtrivTrue). destruct HnewEnabled as [pdentryCurrs (Hs & HnewEnabled)].
      rewrite Hs. simpl. rewrite HbeqCurrBlock. rewrite <-beqAddrFalse in HbeqCurrBlock.
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption). reflexivity.
    - specialize(HnewNotEnabled HtrivFalse). subst s. reflexivity.
  }
  assert(HnewIsFreeSlots0: isFreeSlot idNewSubblock s0).
  {
    assert(HfirstFreeIsFree: FirstFreeSlotPointerIsBEAndFreeSlot s0)
        by (unfold consistency in *; unfold consistency1 in *; intuition).
    unfold pdentryFirstFreeSlot in HfirstFreeCurrs0. rewrite HlookupCurrs0 in HfirstFreeCurrs0.
    rewrite HfirstFreeCurrs0 in *. rewrite beqAddrSym in HbeqNullNew. rewrite <-beqAddrFalse in HbeqNullNew.
    specialize(HfirstFreeIsFree currentPart pdentryCurrs0 HlookupCurrs0 HbeqNullNew).
    apply HfirstFreeIsFree.
  }
  assert(HnewIsNew: ~In idNewSubblock (getMappedBlocks currentPart s0)).
  {
    intro Hcontra. apply mappedBlockIsBE in Hcontra. unfold isFreeSlot in HnewIsFreeSlots0.
    destruct Hcontra as [bentryNew (HlookupNews0Bis & Hcontra)]. rewrite HlookupNews0Bis in HnewIsFreeSlots0.
    destruct (lookup (CPaddr (idNewSubblock + sh1offset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence).
    destruct (lookup (CPaddr (idNewSubblock + scoffset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence).
    destruct HnewIsFreeSlots0 as (_ & _ & _ & _ & Hpresent & _). congruence.
  }

  unfold consistency. split. assumption. unfold consistency2.
  assert(noDupUsedPaddrList s).
  { (* BEGIN noDupUsedPaddrList s *)
    assert(Hcons0: noDupUsedPaddrList s0) by (unfold consistency in *; unfold consistency2 in *; intuition).
    intros part HpartIsPDT. rewrite HPDTEqss5 in HpartIsPDT. rewrite HPDTEqs5s4 in HpartIsPDT.
    rewrite HPDTEqs4s3 in HpartIsPDT. rewrite HPDTEqs3s2 in HpartIsPDT. rewrite HPDTEqs2s0 in HpartIsPDT.
    specialize(Hcons0 part HpartIsPDT). unfold getUsedPaddr in *. apply Lib.NoDupSplitInclIff.
    apply Lib.NoDupSplitInclIff in Hcons0. rewrite HgetConfigEqss0; try(assumption).
    destruct Hcons0 as ((HnoDupConfig & HnoDupMapped) & Hdisjoint). split; try(split; try(assumption)).
    - destruct (beqAddr part currentPart) eqn:HbeqPartCurr.
      + rewrite <-beqAddrTrue in HbeqPartCurr. subst part.
        assert(HgetBlocksCurrEqss0Left: forall block, In block (getMappedBlocks currentPart s)
                                        -> idNewSubblock = block \/ In block (getMappedBlocks currentPart s0)).
        { intro block. apply HgetBlocksCurrEqss0. }
        clear HgetBlocksCurrEqss0. (*unfold getMappedPaddr in HnoDupMapped.*)
        assert(HnoDupBlocks: NoDup (getMappedBlocks currentPart s)).
        {
          assert(HnoDup: noDupMappedBlocksList s) by (unfold consistency1 in *; intuition).
          specialize(HnoDup currentPart HcurrIsPDTs). assumption.
        }
        assert(Hinclss0: incl (getMappedPaddr currentPart s0) (getMappedPaddr currentPart s)).
        {
          intro addr. specialize(HgetPaddrEqss0 currentPart HcurrIsPDTs0 addr). apply HgetPaddrEqss0.
        }
        assert(HlengthEq: length (getMappedPaddr currentPart s) <= length (getMappedPaddr currentPart s0)).
        {
          rewrite HgetPaddrCurrEqss2; try(assumption). destruct HgetPaddrCurrEqs2s0 as (_ & Heq). lia.
        }
        apply NoDup_incl_NoDup with (getMappedPaddr currentPart s0); assumption.
      + rewrite <-beqAddrFalse in HbeqPartCurr. unfold getMappedPaddr. rewrite HgetBlocksEqss0; try(assumption).
        assert(HdisjointBlocks: Lib.disjoint (getMappedBlocks part s0) (getMappedBlocks currentPart s0)).
        {
          assert(HdisjointKS: DisjointKSEntries s0)
              by (unfold consistency in *; unfold consistency1 in *; intuition).
          specialize(HdisjointKS part currentPart HpartIsPDT HcurrIsPDTs0 HbeqPartCurr).
          destruct HdisjointKS as [list1 [list2 (Hlist1 & Hlist2 & HdisjointKS)]]. subst list1. subst list2.
          intros block HblockInPart. unfold getMappedBlocks in HblockInPart. unfold getMappedBlocks.
          apply NotInListNotInFilterPresent. apply InFilterPresentInList in HblockInPart.
          specialize(HdisjointKS block HblockInPart). assumption.
        }
        unfold getMappedPaddr in HnoDupMapped.
        assert(HmappedBlocksAreBE: forall block, In block (getMappedBlocks part s0) -> isBE block s0).
        {
          intros block HblockMapped. apply mappedBlockIsBE in HblockMapped.
          destruct HblockMapped as [bentryBlock (Hlookup & _)]. unfold isBE. rewrite Hlookup. trivial.
        }
        assert(HblockNotEdgeCase: forall block, In block (getMappedBlocks part s0)
                                    -> beqAddr blockToShareInCurrPartAddr block = false
                                        /\ beqAddr idNewSubblock block = false).
        {
          assert(HnewMappedCurrs: In idNewSubblock (getMappedBlocks currentPart s)).
          {
            apply HgetBlocksCurrEqss0. left. reflexivity.
          }
          unfold getMappedBlocks in HblockMappedCurrs0. apply InFilterPresentInList in HblockMappedCurrs0.
          unfold getMappedBlocks in HnewMappedCurrs. apply InFilterPresentInList in HnewMappedCurrs.
          intros block HblockMappedPart.
          destruct (beqAddr blockToShareInCurrPartAddr block) eqn:HbeqBlockBlock.
          {
            unfold getMappedBlocks in HblockMappedPart. apply InFilterPresentInList in HblockMappedPart.
            assert(HdisjointKS: DisjointKSEntries s0)
                by (unfold consistency in *; unfold consistency1 in *; intuition).
            specialize(HdisjointKS part currentPart HpartIsPDT HcurrIsPDTs0 HbeqPartCurr).
            destruct HdisjointKS as [list1 [list2 (Hlist1 & Hlist2 & HdisjointKS)]]. subst list1. subst list2.
            specialize(HdisjointKS block HblockMappedPart). rewrite <-beqAddrTrue in HbeqBlockBlock.
            rewrite HbeqBlockBlock in *. exfalso; congruence.
          }
          destruct (beqAddr idNewSubblock block) eqn:HbeqNewBlockBis.
          {
            rewrite <-HgetBlocksEqss0 in HblockMappedPart; try(assumption).
            unfold getMappedBlocks in HblockMappedPart. apply InFilterPresentInList in HblockMappedPart.
            rewrite <-HPDTEqs2s0 in HpartIsPDT. rewrite <-HPDTEqs3s2 in HpartIsPDT.
            rewrite <-HPDTEqs4s3 in HpartIsPDT. rewrite <-HPDTEqs5s4 in HpartIsPDT.
            rewrite <-HPDTEqss5 in HpartIsPDT.
            assert(HdisjointKS: DisjointKSEntries s)
                by (unfold consistency in *; unfold consistency1 in *; intuition).
            specialize(HdisjointKS part currentPart HpartIsPDT HcurrIsPDTs HbeqPartCurr).
            destruct HdisjointKS as [list1 [list2 (Hlist1 & Hlist2 & HdisjointKS)]]. subst list1. subst list2.
            specialize(HdisjointKS block HblockMappedPart). rewrite <-beqAddrTrue in HbeqNewBlockBis.
            rewrite HbeqNewBlockBis in *. exfalso; congruence.
          }
          split; reflexivity.
        }
        assert(HgetAllEq: getAllPaddrAux (getMappedBlocks part s0) s
                          = getAllPaddrAux (getMappedBlocks part s0) s0).
        {
          induction (getMappedBlocks part s0); try(simpl; reflexivity).
          assert(HaInAL: In a2 (a2::l0)) by (simpl; left; reflexivity).
          assert(forall block, In block l0 -> isBE block s0).
          {
            intros block HblockMapped. assert(HblockInAL: In block (a2::l0)).
            { simpl. right. assumption. }
            specialize(HmappedBlocksAreBE block HblockInAL). assumption.
          }
          specialize(HmappedBlocksAreBE a2 HaInAL).
          simpl. simpl in HnoDupMapped.
          assert(Lib.disjoint l0 (getMappedBlocks currentPart s0)).
          {
            intros block HblockInL. assert(HblockInAL: In block (a2::l0)).
            { simpl. right. assumption. }
            specialize(HdisjointBlocks block HblockInAL). assumption.
          }
          assert(forall block, In block l0
                                -> beqAddr blockToShareInCurrPartAddr block = false
                                    /\ beqAddr idNewSubblock block = false).
          {
            intros block HblockMapped. assert(HblockInAL: In block (a2::l0)).
            { simpl. right. assumption. }
            specialize(HblockNotEdgeCase block HblockInAL). assumption.
          }
          specialize(HblockNotEdgeCase a2 HaInAL). destruct HblockNotEdgeCase as (HbeqABlock & HbeqANew).
          assert(HlookupAEq: lookup a2 (memory s) beqAddr = lookup a2 (memory s0) beqAddr).
          { apply HBElookupEqss0; assumption. }
          rewrite HlookupAEq. destruct (lookup a2 (memory s0) beqAddr) eqn:HlookupA; try(apply IHl0 ; assumption).
          destruct v; try(apply IHl0 ; assumption). apply Lib.NoDupSplitInclIff in HnoDupMapped.
          destruct HnoDupMapped as ((HnoDupA & HnoDupMappedRec) & HdisjointARec).
          apply app_inv_head_iff. apply IHl0; assumption.
        }
        rewrite HgetAllEq. assumption.
    - intros addr HaddrInConfig. specialize(Hdisjoint addr HaddrInConfig). contradict Hdisjoint.
      specialize(HgetPaddrEqss0 part HpartIsPDT addr). apply HgetPaddrEqss0. assumption.
    (* END noDupUsedPaddrList *)
  }
  split. assumption.

  assert(HnewMappedCurrs: In idNewSubblock (getMappedBlocks currentPart s)).
  {
    apply HgetBlocksCurrEqss0. left. reflexivity.
  }

  split.
  { (* BEGIN accessibleParentPaddrIsAccessibleIntoChild s *)
    assert(Hcons0: accessibleParentPaddrIsAccessibleIntoChild s0)
        by (unfold consistency in *; unfold consistency2 in *; intuition).
    intros pdparent child addr HparentIsPart HchildIsChild HaddrAccParent HaddrMappedChild.
    rewrite HgetPartsEqss0 in HparentIsPart.
    assert(HparentIsPDT: isPDT pdparent s0).
    {
      apply partitionsArePDT.
      unfold consistency in *; unfold consistency1 in *; intuition.
      unfold consistency in *; unfold consistency1 in *; intuition.
      assumption.
    }
    rewrite HgetChildrenEqss0 in HchildIsChild; try(assumption).
    assert(HchildIsPDT: isPDT child s0).
    {
      apply childrenArePDT with pdparent; try(assumption).
      unfold consistency in *; unfold consistency1 in *; intuition.
    }
    assert(HaddrAccParents0: In addr (getAccessibleMappedPaddr pdparent s0)).
    {
      destruct (beqAddr pdparent currentPart) eqn:HbeqParentCurr.
      - rewrite <-beqAddrTrue in HbeqParentCurr. subst pdparent. apply HgetAccPaddrCurrEqss0 in HaddrAccParent.
        assumption.
      - rewrite <-beqAddrFalse in HbeqParentCurr. rewrite HgetAccPaddrEqss0 in HaddrAccParent; assumption.
    }
    apply HgetPaddrEqss0 in HaddrMappedChild; try(assumption).
    specialize(Hcons0 pdparent child addr HparentIsPart HchildIsChild HaddrAccParents0 HaddrMappedChild).
    destruct (beqAddr child currentPart) eqn:HbeqChildCurr.
    - rewrite <-beqAddrTrue in HbeqChildCurr. subst child. apply HgetAccPaddrCurrEqss0. assumption.
    - rewrite <-beqAddrFalse in HbeqChildCurr. rewrite HgetAccPaddrEqss0; assumption.
    (* END accessibleParentPaddrIsAccessibleIntoChild *)
  }

  assert(HBEEqs1s0: forall block, isBE block s1 = isBE block s0).
  {
    intro block. unfold isBE. rewrite Hs1. simpl. destruct (beqAddr sceaddr block) eqn:HbeqSceBlock.
    {
      rewrite <-beqAddrTrue in HbeqSceBlock. subst block. unfold isSCE in HsceaddrIsSCEs0.
      destruct (lookup sceaddr (memory s0) beqAddr); try(reflexivity). destruct v; try(reflexivity).
      exfalso; congruence.
    }
    rewrite HbeqNewSce. rewrite InternalLemmas.beqAddrTrue. simpl.
    destruct (beqAddr idNewSubblock block) eqn:HbeqNewBlockBis.
    - rewrite <-beqAddrTrue in HbeqNewBlockBis. subst block. rewrite HlookupNews0. reflexivity.
    - rewrite HbeqCurrNew. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption). simpl.
      destruct (beqAddr currentPart block) eqn:HbeqCurrBlock.
      + rewrite <-beqAddrTrue in HbeqCurrBlock. subst block. rewrite HlookupCurrs0. reflexivity.
      + rewrite <-beqAddrFalse in HbeqCurrBlock. rewrite InternalLemmas.beqAddrTrue.
        rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity; try(apply not_eq_sym; assumption). reflexivity.
  }
  assert(HBEEqs2s0: forall block, isBE block s2 = isBE block s0).
  {
    intro block. rewrite <-HBEEqs1s0. unfold isBE. rewrite Hs2. simpl.
    destruct (beqAddr blockToShareInCurrPartAddr block) eqn:HbeqBlockBlock.
    - rewrite <-beqAddrTrue in HbeqBlockBlock. subst block. rewrite HlookupBlocks1. reflexivity.
    - rewrite <-beqAddrFalse in HbeqBlockBlock. rewrite removeDupIdentity; intuition.
  }
  assert(HBEEqs3s0: forall block, isBE block s3 = isBE block s0).
  {
    intro block. rewrite <-HBEEqs2s0. destruct blockToShareEnabled.
    - specialize(HblockEnabled HtrivTrue). destruct HblockEnabled as [pdentryCurrs3 (Hs3 & HblockEnabled)].
      rewrite Hs3. unfold isBE. simpl. destruct (beqAddr currentPart block) eqn:HbeqCurrBlock.
      + rewrite <-beqAddrTrue in HbeqCurrBlock. subst block. rewrite HlookupCurrs2. reflexivity.
      + rewrite <-beqAddrFalse in HbeqCurrBlock. rewrite removeDupIdentity; intuition.
    - specialize(HblockNotEnabled HtrivFalse). subst s3. reflexivity.
  }
  assert(HBEEqs4s0: forall block, isBE block s4 = isBE block s0).
  {
    intro block. rewrite <-HBEEqs3s0. unfold isBE. rewrite Hs4. simpl.
    destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) block) eqn:HbeqNewSceBlock.
    - rewrite <-beqAddrTrue in HbeqNewSceBlock. subst block. rewrite HlookupNewSces3. reflexivity.
    - rewrite <-beqAddrFalse in HbeqNewSceBlock. rewrite removeDupIdentity; intuition.
  }
  assert(HBEEqs5s0: forall block, isBE block s5 = isBE block s0).
  {
    intro block. rewrite <-HBEEqs4s0. unfold isBE. rewrite Hs5. simpl.
    destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) block) eqn:HbeqBlockSceBlock.
    - rewrite <-beqAddrTrue in HbeqBlockSceBlock. subst block. rewrite HlookupBlockSces4. reflexivity.
    - rewrite <-beqAddrFalse in HbeqBlockSceBlock. rewrite removeDupIdentity; intuition.
  }
  assert(HBEEqss0: forall block, isBE block s = isBE block s0).
  {
    intro block. rewrite <-HBEEqs5s0. destruct newSubEnabled.
    - specialize(HnewEnabled HtrivTrue). destruct HnewEnabled as [pdentryCurrs (Hs & HnewEnabled)].
      rewrite Hs. unfold isBE. simpl. destruct (beqAddr currentPart block) eqn:HbeqCurrBlock.
      + rewrite <-beqAddrTrue in HbeqCurrBlock. subst block. rewrite HlookupCurrs5. reflexivity.
      + rewrite <-beqAddrFalse in HbeqCurrBlock. rewrite removeDupIdentity; intuition.
    - specialize(HnewNotEnabled HtrivFalse). subst s. reflexivity.
  }
  destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) blockToShareInCurrPartAddr)
      eqn:HbeqBlockSceBlock.
  {
    rewrite <- beqAddrTrue in HbeqBlockSceBlock. rewrite HbeqBlockSceBlock in *. exfalso; congruence.
  }
  assert(HlookupBlocks5: lookup blockToShareInCurrPartAddr (memory s5) beqAddr = Some (BE bentryShares2)).
  {
    rewrite Hs5. simpl. rewrite HbeqBlockSceBlock. rewrite <-beqAddrFalse in HbeqBlockSceBlock.
    rewrite removeDupIdentity; intuition.
  }
  destruct (beqAddr currentPart blockToShareInCurrPartAddr) eqn:HbeqCurrBlock.
  {
    rewrite <-beqAddrTrue in HbeqCurrBlock. rewrite HbeqCurrBlock in *. exfalso; congruence.
  }
  assert(HlookupBlocks: lookup blockToShareInCurrPartAddr (memory s) beqAddr = Some (BE bentryShares2)).
  {
    destruct newSubEnabled.
    - specialize(HnewEnabled HtrivTrue). destruct HnewEnabled as [pdentryCurrs (Hs & HnewEnabled)].
      rewrite Hs. simpl. rewrite HbeqCurrBlock. rewrite <-beqAddrFalse in HbeqCurrBlock.
      rewrite removeDupIdentity; intuition.
    - specialize(HnewNotEnabled HtrivFalse). subst s. assumption.
  }
  assert(HbentryShares2: exists lShare, bentryShares2 =
                                          {|
                                            read := read bentryShares0;
                                            write := write bentryShares0;
                                            exec := exec bentryShares0;
                                            present := present bentryShares0;
                                            accessible := accessible bentryShares0;
                                            blockrange := CBlock (startAddr (blockrange bentryShares0)) cutAddr;
                                            blockindex := blockindex bentryShares0;
                                            Hidx := lShare
                                          |}).
  {
    rewrite Hs2 in HlookupBlocks2. simpl in HlookupBlocks2. rewrite InternalLemmas.beqAddrTrue in HlookupBlocks2.
    injection HlookupBlocks2 as Hres. rewrite <-Hres. unfold CBlockEntry.
    assert(blockindex bentryShares0 < kernelStructureEntriesNb) by (apply Hidx).
    destruct (Compare_dec.lt_dec (blockindex bentryShares0) kernelStructureEntriesNb); try(lia).
    exists (ADT.CBlockEntry_obligation_1 (blockindex bentryShares0) l0). reflexivity.
  }
  destruct HbentryShares2 as [lShare HbentryShares2]. unfold CBlock in HbentryShares2.
  assert(HlebCutMax: cutAddr <= maxAddr) by (apply Hp). rewrite <-maxIdxEqualMaxAddr in HlebCutMax.
  destruct (Compare_dec.le_dec (cutAddr - startAddr (blockrange bentryShares0)) maxIdx); try(lia).
  assert(HblockInclBlocks0: forall addr, In addr (getAllPaddrAux [blockToShareInCurrPartAddr] s)
                                          -> In addr (getAllPaddrAux [blockToShareInCurrPartAddr] s0)).
  {
    simpl. intros addr HaddrInBlocks. rewrite HlookupBlocks0. rewrite HlookupBlocks in HaddrInBlocks.
    rewrite app_nil_r in *. rewrite HbentryShares2 in HaddrInBlocks. simpl in HaddrInBlocks.
    unfold StateLib.Paddr.leb in HlebEndCut. apply eq_sym in HlebEndCut. apply PeanoNat.Nat.leb_gt in HlebEndCut.
    unfold bentryEndAddr in HendBlockBiss0. rewrite HlookupBlocks0 in HendBlockBiss0. rewrite <-HendBlockBiss0.
    apply getAllPaddrBlockInclRev in HaddrInBlocks. destruct HaddrInBlocks as (HlebStartAddr & HltAddrCut & _).
    apply getAllPaddrBlockIncl; lia.
  }
  assert(HSHElookupEqss0: forall sh1entryaddr, isSHE sh1entryaddr s0
                          -> lookup sh1entryaddr (memory s) beqAddr = lookup sh1entryaddr (memory s0) beqAddr).
  {
    intros sh1entryaddr Hsh1IsSHE. unfold isSHE in Hsh1IsSHE.
    destruct (beqAddr currentPart sh1entryaddr) eqn:HbeqCurrSh1.
    {
      rewrite <-beqAddrTrue in HbeqCurrSh1. subst sh1entryaddr. rewrite HlookupCurrs0 in Hsh1IsSHE.
      exfalso; congruence.
    }
    destruct (beqAddr idNewSubblock sh1entryaddr) eqn:HbeqNewSh1.
    {
      rewrite <-beqAddrTrue in HbeqNewSh1. subst sh1entryaddr. rewrite HlookupNews0 in Hsh1IsSHE.
      exfalso; congruence.
    }
    destruct (beqAddr blockToShareInCurrPartAddr sh1entryaddr) eqn:HbeqBlockSh1.
    {
      rewrite <-beqAddrTrue in HbeqBlockSh1. subst sh1entryaddr. rewrite HlookupBlocks0 in Hsh1IsSHE.
      exfalso; congruence.
    }
    assert(HlookupEqs1: lookup sh1entryaddr (memory s1) beqAddr = lookup sh1entryaddr (memory s0) beqAddr).
    {
      rewrite Hs1. simpl.
      destruct (beqAddr sceaddr sh1entryaddr) eqn:HbeqSceSh1.
      {
        rewrite <-beqAddrTrue in HbeqSceSh1. subst sh1entryaddr. exfalso. unfold isSCE in HsceaddrIsSCEs0.
        destruct (lookup sceaddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
      }
      rewrite HbeqNewSce. simpl. rewrite HbeqNewSh1. rewrite InternalLemmas.beqAddrTrue.
      rewrite HbeqCurrNew. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption). simpl. rewrite beqAddrFalse in HbeqCurrSh1.
      rewrite HbeqCurrSh1. rewrite InternalLemmas.beqAddrTrue. rewrite <-beqAddrFalse in HbeqCurrSh1.
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption). reflexivity.
    }
    assert(HlookupEqs2: lookup sh1entryaddr (memory s2) beqAddr = lookup sh1entryaddr (memory s0) beqAddr).
    {
      rewrite <-HlookupEqs1. rewrite Hs2. simpl. rewrite HbeqBlockSh1. rewrite <-beqAddrFalse in HbeqBlockSh1.
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption). reflexivity.
    }
    assert(HlookupEqs3: lookup sh1entryaddr (memory s3) beqAddr = lookup sh1entryaddr (memory s0) beqAddr).
    {
      rewrite <-HlookupEqs2. destruct blockToShareEnabled.
      - specialize(HblockEnabled HtrivTrue). destruct HblockEnabled as [pdentryCurrs3 (Hs3 & HblockEnabled)].
        rewrite Hs3. simpl. rewrite HbeqCurrSh1. rewrite <-beqAddrFalse in HbeqCurrSh1.
        rewrite removeDupIdentity; try(apply not_eq_sym; assumption). reflexivity.
      - specialize(HblockNotEnabled HtrivFalse). subst s3. reflexivity.
    }
    assert(HlookupEqs4: lookup sh1entryaddr (memory s4) beqAddr = lookup sh1entryaddr (memory s0) beqAddr).
    {
      rewrite <-HlookupEqs3. rewrite Hs4. simpl.
      destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) sh1entryaddr) eqn:HbeqNewSceSh1.
      {
        rewrite <-beqAddrTrue in HbeqNewSceSh1. subst sh1entryaddr. rewrite HlookupNewSces3 in HlookupEqs3.
        rewrite <-HlookupEqs3 in Hsh1IsSHE. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in HbeqNewSceSh1. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      reflexivity.
    }
    assert(HlookupEqs5: lookup sh1entryaddr (memory s5) beqAddr = lookup sh1entryaddr (memory s0) beqAddr).
    {
      rewrite <-HlookupEqs4. rewrite Hs5. simpl.
      destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) sh1entryaddr) eqn:HbeqBlockSceSh1.
      {
        rewrite <-beqAddrTrue in HbeqBlockSceSh1. subst sh1entryaddr. rewrite HlookupBlockSces4 in HlookupEqs4.
        rewrite <-HlookupEqs4 in Hsh1IsSHE. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in HbeqBlockSceSh1. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      reflexivity.
    }
    rewrite <-HlookupEqs5. destruct newSubEnabled.
    - specialize(HnewEnabled HtrivTrue). destruct HnewEnabled as [pdentryCurrs (Hs & HnewEnabled)].
      rewrite Hs. simpl. rewrite HbeqCurrSh1. rewrite <-beqAddrFalse in HbeqCurrSh1.
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption). reflexivity.
    - specialize(HnewNotEnabled HtrivFalse). subst s. reflexivity.
  }
  assert(HSCElookupEqs0: forall scentryaddr,
                              isSCE scentryaddr s0
                              -> beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) scentryaddr = false
                              -> beqAddr (CPaddr (idNewSubblock + scoffset)) scentryaddr = false
                              -> lookup scentryaddr (memory s) beqAddr = lookup scentryaddr (memory s0) beqAddr).
  {
    intros scentryaddr HsceIsSCE HbeqBlockSceSce HbeqNewSceSce. unfold isSCE in HsceIsSCE.
    destruct (beqAddr currentPart scentryaddr) eqn:HbeqCurrSceBis.
    {
      rewrite <-beqAddrTrue in HbeqCurrSceBis. subst scentryaddr. rewrite HlookupCurrs0 in HsceIsSCE.
      exfalso; congruence.
    }
    assert(HlookupEqs1: lookup scentryaddr (memory s1) beqAddr = lookup scentryaddr (memory s0) beqAddr).
    {
      rewrite Hs1. simpl. rewrite Hsceaddr. rewrite HbeqNewSceSce. rewrite beqAddrSym in HbeqNewSceNew.
      rewrite HbeqNewSceNew. simpl.
      destruct (beqAddr idNewSubblock scentryaddr) eqn:HbeqNewSceBis.
      {
        rewrite <-beqAddrTrue in HbeqNewSceBis. subst scentryaddr. rewrite HlookupNews0 in HsceIsSCE.
        exfalso; congruence.
      }
      rewrite InternalLemmas.beqAddrTrue. rewrite HbeqCurrNew. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption). simpl. rewrite beqAddrFalse in HbeqCurrSceBis.
      rewrite HbeqCurrSceBis. rewrite InternalLemmas.beqAddrTrue. rewrite <-beqAddrFalse in HbeqCurrSceBis.
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption). reflexivity.
    }
    assert(HlookupEqs2: lookup scentryaddr (memory s2) beqAddr = lookup scentryaddr (memory s0) beqAddr).
    {
      rewrite <-HlookupEqs1. rewrite Hs2. simpl.
      destruct (beqAddr blockToShareInCurrPartAddr scentryaddr) eqn:HbeqBlockSce.
      {
        rewrite <-beqAddrTrue in HbeqBlockSce. subst scentryaddr. rewrite HlookupBlocks0 in HsceIsSCE.
        exfalso; congruence.
      }
      rewrite <-beqAddrFalse in HbeqBlockSce. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      reflexivity.
    }
    assert(HlookupEqs3: lookup scentryaddr (memory s3) beqAddr = lookup scentryaddr (memory s0) beqAddr).
    {
      rewrite <-HlookupEqs2. destruct blockToShareEnabled.
      - specialize(HblockEnabled HtrivTrue). destruct HblockEnabled as [pdentryCurrs3 (Hs3 & HblockEnabled)].
        rewrite Hs3. simpl. rewrite HbeqCurrSceBis. rewrite <-beqAddrFalse in HbeqCurrSceBis.
        rewrite removeDupIdentity; try(apply not_eq_sym; assumption). reflexivity.
      - specialize(HblockNotEnabled HtrivFalse). subst s3. reflexivity.
    }
    assert(HlookupEqs4: lookup scentryaddr (memory s4) beqAddr = lookup scentryaddr (memory s0) beqAddr).
    {
      rewrite <-HlookupEqs3. rewrite Hs4. simpl. rewrite HbeqNewSceSce.
      rewrite <-beqAddrFalse in HbeqNewSceSce. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      reflexivity.
    }
    assert(HlookupEqs5: lookup scentryaddr (memory s5) beqAddr = lookup scentryaddr (memory s0) beqAddr).
    {
      rewrite <-HlookupEqs4. rewrite Hs5. simpl. rewrite HbeqBlockSceSce.
      rewrite <-beqAddrFalse in HbeqBlockSceSce. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      reflexivity.
    }
    rewrite <-HlookupEqs5. destruct newSubEnabled.
    - specialize(HnewEnabled HtrivTrue). destruct HnewEnabled as [pdentryCurrs (Hs & HnewEnabled)].
      rewrite Hs. simpl. rewrite HbeqCurrSceBis. rewrite <-beqAddrFalse in HbeqCurrSceBis.
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption). reflexivity.
    - specialize(HnewNotEnabled HtrivFalse). subst s. reflexivity.
  }

  split.
  { (* BEGIN sharedBlockPointsToChild s *)
    assert(Hcons0: sharedBlockPointsToChild s0) by (unfold consistency in *; unfold consistency2 in *; intuition).
    intros pdparent child addr blockParent sh1entryaddrBlock HparentIsPart HchildIsChild HaddrIsUsedChild
      HaddrInBlockParent HblockParentMapped Hsh1entryaddr.
    rewrite HgetPartsEqss0 in HparentIsPart.
    assert(HparentIsPDT: isPDT pdparent s0).
    {
      apply partitionsArePDT.
      unfold consistency in *; unfold consistency1 in *; intuition.
      unfold consistency in *; unfold consistency1 in *; intuition.
      assumption.
    }
    rewrite HgetChildrenEqss0 in HchildIsChild; try(assumption).
    assert(HchildIsPDT: isPDT child s0).
    {
      apply childrenArePDT with pdparent; try(assumption).
      unfold consistency in *; unfold consistency1 in *; intuition.
    }
    apply HgetUsedEqss0 in HaddrIsUsedChild; try(assumption).
    destruct (beqAddr pdparent currentPart) eqn:HbeqParentCurr.
    - rewrite <-beqAddrTrue in HbeqParentCurr. subst pdparent. rewrite HgetBlocksCurrEqss0 in HblockParentMapped.
      assert(HnoChild: noChildImpliesAddressesNotShared s0)
          by (unfold consistency in *; unfold consistency2 in *; intuition).
      destruct HPDChildBlocks0 as [sh1entry [sh1entryaddr (HlookupSh1 & HPDChildBlocks0 & Hsh1)]].
      rewrite <-beqAddrTrue in HbeqPDChildNull. subst PDChildAddr. unfold sh1entryAddr in Hsh1.
      rewrite HlookupBlocks0 in Hsh1.
      specialize(HnoChild currentPart pdentryCurrs0 blockToShareInCurrPartAddr sh1entryaddr HparentIsPart
          HlookupCurrs0 HblockMappedCurrs0 Hsh1 HPDChildBlocks0 child addr HchildIsChild).
      assert(HchildIsPart: In child (getPartitions multiplexer s0)).
      {
        revert HchildIsChild. apply childrenPartitionInPartitionList; try(assumption).
        unfold consistency in *; unfold consistency1 in *; intuition.
      }
      specialize(HKDIs0 currentPart child HparentIsPart HchildIsPart).
      destruct (beqAddr idNewSubblock blockParent) eqn:HbeqNewBlockParent.
      {
        rewrite <-beqAddrTrue in HbeqNewBlockParent. subst blockParent. exfalso.
        assert(HaddrInBlocks0: In addr (getAllPaddrAux [blockToShareInCurrPartAddr] s0)).
        {
          apply HnewInclBlocs0. assumption.
        }
        specialize(HnoChild HaddrInBlocks0). unfold getUsedPaddr in HaddrIsUsedChild.
        apply in_app_or in HaddrIsUsedChild.
        destruct HaddrIsUsedChild as [HaddrIsConfigChild | Hcontra]; try(congruence).
        assert(HaddrIsAcc: In addr (getAccessibleMappedPaddr currentPart s0)).
        { apply addrInAccessibleBlockIsAccessibleMapped with blockToShareInCurrPartAddr; assumption. }
        specialize(HKDIs0 addr HaddrIsAcc). congruence.
      }
      rewrite <-beqAddrFalse in HbeqNewBlockParent.
      destruct HblockParentMapped as [Hcontra | HblockParentMappeds0]; try(exfalso; congruence).
      destruct (beqAddr blockToShareInCurrPartAddr blockParent) eqn:HbeqBlockBlock.
      {
        rewrite <-beqAddrTrue in HbeqBlockBlock. subst blockParent. apply HblockInclBlocks0 in HaddrInBlockParent.
        exfalso. specialize(HnoChild HaddrInBlockParent). unfold getUsedPaddr in HaddrIsUsedChild.
        apply in_app_or in HaddrIsUsedChild.
        destruct HaddrIsUsedChild as [HaddrIsConfigChild | Hcontra]; try(congruence).
        assert(HaddrIsAcc: In addr (getAccessibleMappedPaddr currentPart s0)).
        { apply addrInAccessibleBlockIsAccessibleMapped with blockToShareInCurrPartAddr; assumption. }
        specialize(HKDIs0 addr HaddrIsAcc). congruence.
      }
      rewrite beqAddrFalse in HbeqNewBlockParent.
      assert(HblockParentIsBEs: isBE blockParent s).
      {
        unfold isBE. unfold sh1entryAddr in Hsh1entryaddr.
        destruct (lookup blockParent (memory s) beqAddr); try(congruence). destruct v; try(congruence). trivial.
      }
      assert(HlookupEq: lookup blockParent (memory s) beqAddr = lookup blockParent (memory s0) beqAddr).
      {
        apply HBElookupEqss0; try(assumption). rewrite <-HBEEqss0. assumption.
      }
      unfold sh1entryAddr in Hsh1entryaddr. rewrite HlookupEq in Hsh1entryaddr.
      assert(HaddrInBlockParents0: In addr (getAllPaddrAux [blockParent] s0)).
      {
        simpl. simpl in HaddrInBlockParent. rewrite HlookupEq in HaddrInBlockParent. assumption.
      }
      specialize(Hcons0 currentPart child addr blockParent sh1entryaddrBlock HparentIsPart HchildIsChild
            HaddrIsUsedChild HaddrInBlockParents0 HblockParentMappeds0 Hsh1entryaddr).
      assert(HlookupParentSh1Eq: lookup (CPaddr (blockParent + sh1offset)) (memory s) beqAddr
                                  = lookup (CPaddr (blockParent + sh1offset)) (memory s0) beqAddr).
      {
        apply HSHElookupEqss0.
        assert(HwellFormed: wellFormedFstShadowIfBlockEntry s0)
            by (unfold consistency in *; unfold consistency1 in *; intuition).
        rewrite HBEEqss0 in HblockParentIsBEs. specialize(HwellFormed blockParent HblockParentIsBEs).
        assumption.
      }
      unfold sh1entryPDchild. unfold sh1entryPDflag. rewrite HlookupParentSh1Eq. assumption.
    - rewrite <-beqAddrFalse in HbeqParentCurr.
      assert(Hcopy: In blockParent (getMappedBlocks pdparent s)) by assumption.
      rewrite HgetBlocksEqss0 in HblockParentMapped; try(assumption).
      destruct (beqAddr blockToShareInCurrPartAddr blockParent) eqn:HbeqBlockBlock.
      {
        rewrite <-beqAddrTrue in HbeqBlockBlock. subst blockParent.
        assert(Hdisjoint: DisjointKSEntries s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
        specialize(Hdisjoint pdparent currentPart HparentIsPDT HcurrIsPDTs0 HbeqParentCurr).
        destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
        unfold getMappedBlocks in HblockParentMapped. apply InFilterPresentInList in HblockParentMapped.
        specialize(Hdisjoint blockToShareInCurrPartAddr HblockParentMapped).
        unfold getMappedBlocks in HblockMappedCurrs0. apply InFilterPresentInList in HblockMappedCurrs0.
        exfalso; congruence.
      }
      destruct (beqAddr idNewSubblock blockParent) eqn:HbeqNewBlockParent.
      {
        rewrite <-beqAddrTrue in HbeqNewBlockParent. subst blockParent. rewrite <-HPDTEqs2s0 in HparentIsPDT.
        rewrite <-HPDTEqs3s2 in HparentIsPDT. rewrite <-HPDTEqs4s3 in HparentIsPDT.
        rewrite <-HPDTEqs5s4 in HparentIsPDT. rewrite <-HPDTEqss5 in HparentIsPDT.
        assert(Hdisjoint: DisjointKSEntries s) by (unfold consistency1 in *; intuition).
        specialize(Hdisjoint pdparent currentPart HparentIsPDT HcurrIsPDTs HbeqParentCurr).
        destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
        unfold getMappedBlocks in Hcopy. apply InFilterPresentInList in Hcopy.
        specialize(Hdisjoint idNewSubblock Hcopy).
        unfold getMappedBlocks in HnewMappedCurrs. apply InFilterPresentInList in HnewMappedCurrs.
        exfalso; congruence.
      }
      assert(HblockParentIsBEs: isBE blockParent s).
      {
        unfold isBE. unfold sh1entryAddr in Hsh1entryaddr.
        destruct (lookup blockParent (memory s) beqAddr); try(congruence). destruct v; try(congruence). trivial.
      }
      assert(HlookupEq: lookup blockParent (memory s) beqAddr = lookup blockParent (memory s0) beqAddr).
      {
        apply HBElookupEqss0; try(assumption). rewrite <-HBEEqss0. assumption.
      }
      unfold sh1entryAddr in Hsh1entryaddr. rewrite HlookupEq in Hsh1entryaddr.
      assert(HaddrInBlockParents0: In addr (getAllPaddrAux [blockParent] s0)).
      {
        simpl. simpl in HaddrInBlockParent. rewrite HlookupEq in HaddrInBlockParent. assumption.
      }
      specialize(Hcons0 pdparent child addr blockParent sh1entryaddrBlock HparentIsPart HchildIsChild
            HaddrIsUsedChild HaddrInBlockParents0 HblockParentMapped Hsh1entryaddr).
      assert(HlookupParentSh1Eq: lookup (CPaddr (blockParent + sh1offset)) (memory s) beqAddr
                                  = lookup (CPaddr (blockParent + sh1offset)) (memory s0) beqAddr).
      {
        apply HSHElookupEqss0.
        assert(HwellFormed: wellFormedFstShadowIfBlockEntry s0)
            by (unfold consistency in *; unfold consistency1 in *; intuition).
        rewrite HBEEqss0 in HblockParentIsBEs. specialize(HwellFormed blockParent HblockParentIsBEs).
        assumption.
      }
      unfold sh1entryPDchild. unfold sh1entryPDflag. rewrite HlookupParentSh1Eq. assumption.
    (* END sharedBlockPointsToChild *)
  }

  assert(HoriginNews: scentryOrigin sceaddr blockOrigin s).
  {
    assert(HoriginNews1: scentryOrigin sceaddr blockOrigin s1).
    {
      unfold scentryOrigin. rewrite Hs1. simpl. rewrite InternalLemmas.beqAddrTrue. simpl. reflexivity.
    }
    assert(HoriginNews2: scentryOrigin sceaddr blockOrigin s2).
    {
      unfold scentryOrigin in *. rewrite Hs2. simpl.
      destruct (beqAddr blockToShareInCurrPartAddr sceaddr) eqn:HbeqBlockSce.
      {
        rewrite <-beqAddrTrue in HbeqBlockSce. rewrite HbeqBlockSce in *. rewrite HlookupBlocks1 in HoriginNews1.
        congruence.
      }
      rewrite <-beqAddrFalse in HbeqBlockSce. rewrite removeDupIdentity; intuition.
    }
    assert(HoriginNews3: scentryOrigin sceaddr blockOrigin s3).
    {
      unfold scentryOrigin in *. destruct blockToShareEnabled.
      - specialize(HblockEnabled HtrivTrue). destruct HblockEnabled as [pdentryCurrs3 (Hs3 & HblockEnabled)].
        rewrite Hs3. simpl. rewrite HbeqCurrSce. rewrite <-beqAddrFalse in HbeqCurrSce.
        rewrite removeDupIdentity; intuition.
      - specialize(HblockNotEnabled HtrivFalse). subst s3. assumption.
    }
    assert(HoriginNews4: scentryOrigin sceaddr blockOrigin s4).
    {
      unfold scentryOrigin in *. rewrite Hs4. simpl. subst sceaddr. rewrite InternalLemmas.beqAddrTrue. simpl.
      rewrite HlookupNewSces3 in HoriginNews3. assumption.
    }
    assert(HoriginNews5: scentryOrigin sceaddr blockOrigin s5).
    {
      unfold scentryOrigin in *. rewrite Hs5. simpl. subst sceaddr. rewrite beqAddrSym in HbeqNewSceBlockSce.
      rewrite HbeqNewSceBlockSce. rewrite <-beqAddrFalse in HbeqNewSceBlockSce.
      rewrite removeDupIdentity; intuition.
    }
    unfold scentryOrigin in *. destruct newSubEnabled.
    - specialize(HnewEnabled HtrivTrue). destruct HnewEnabled as [pdentryCurrs (Hs & HnewEnabled)].
      rewrite Hs. simpl. rewrite HbeqCurrSce. rewrite <-beqAddrFalse in HbeqCurrSce.
      rewrite removeDupIdentity; intuition.
    - specialize(HnewNotEnabled HtrivFalse). subst s. assumption.
  }

  split.
  { (* BEGIN adressesRangePreservedIfOriginAndNextOk s *)
    assert(Hcons0: adressesRangePreservedIfOriginAndNextOk s0)
        by (unfold consistency in *; unfold consistency2 in *; intuition).
    intros part pdentryPart block scentryaddr startaddr endaddr HpartIsPart HblockMapped HblockIsBE Hstart Hend
      HPFlag Hscentryaddr Horigin Hnext HlookupPart HbeqPartRoot. rewrite HBEEqss0 in HblockIsBE.
    rewrite HgetPartsEqss0 in HpartIsPart.
    destruct (beqAddr idNewSubblock block) eqn:HbeqNewBlockBis.
    {
      rewrite <-beqAddrTrue in HbeqNewBlockBis. subst block. rewrite <-Hsceaddr in Hscentryaddr.
      subst scentryaddr. unfold scentryOrigin in *. exfalso.
      assert(HoriginCopy: scentryOrigin sceaddr blockOrigin s) by assumption.
      destruct (lookup sceaddr (memory s) beqAddr); try(congruence). destruct v; try(congruence).
      rewrite <-HoriginNews in Horigin. subst startaddr. unfold bentryStartAddr in Hstart.
      rewrite HlookupNews in Hstart. rewrite Hbentry6simpl in Hstart. simpl in Hstart.
      assert(HpartIsCurr: part = currentPart).
      {
        destruct (beqAddr part currentPart) eqn:HbeqPartCurr; try(apply beqAddrTrue; assumption). exfalso.
        rewrite <-beqAddrFalse in HbeqPartCurr. unfold getMappedBlocks in HnewMappedCurrs.
        unfold getMappedBlocks in HblockMapped. apply InFilterPresentInList in HnewMappedCurrs.
        apply InFilterPresentInList in HblockMapped.
        assert(Hdisjoint: DisjointKSEntries s) by (unfold consistency1 in *; intuition).
        assert(HpartIsPDT: isPDT part s) by (unfold isPDT; rewrite HlookupPart; trivial).
        specialize(Hdisjoint part currentPart HpartIsPDT HcurrIsPDTs HbeqPartCurr).
        destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
        specialize(Hdisjoint idNewSubblock HblockMapped). congruence.
      }
      subst part. assert(HoriginParent: originIsParentBlocksStart s) by (unfold consistency1 in *; intuition).
      assert(HblockMappedCurrs: In blockToShareInCurrPartAddr (getMappedBlocks currentPart s)).
      { apply HgetBlocksCurrEqss0. right. assumption. }
      assert(HeqTriv: CPaddr (blockToShareInCurrPartAddr + scoffset)
                      = CPaddr (blockToShareInCurrPartAddr + scoffset)) by reflexivity.
      rewrite <-HgetPartsEqss0 in HpartIsPart.
      assert(HoriginBlocks: scentryOrigin (CPaddr (blockToShareInCurrPartAddr + scoffset)) blockOrigin s).
      {
        unfold scentryOrigin. rewrite HlookupBlockSceEqss5. rewrite Hs5. simpl.
        rewrite InternalLemmas.beqAddrTrue. simpl.
        assert(HlookupBlockSceEqs4s3: lookup (CPaddr (blockToShareInCurrPartAddr + scoffset)) (memory s4) beqAddr
                                = lookup (CPaddr (blockToShareInCurrPartAddr + scoffset)) (memory s3) beqAddr).
        {
          rewrite Hs4. simpl. rewrite HbeqNewSceBlockSce. rewrite <-beqAddrFalse in HbeqNewSceBlockSce.
          rewrite removeDupIdentity; try(apply not_eq_sym; assumption). reflexivity.
        }
        assert(HlookupBlockSceEqs3s2: lookup (CPaddr (blockToShareInCurrPartAddr + scoffset)) (memory s3) beqAddr
                                = lookup (CPaddr (blockToShareInCurrPartAddr + scoffset)) (memory s2) beqAddr).
        {
          destruct blockToShareEnabled.
          - specialize(HblockEnabled HtrivTrue). destruct HblockEnabled as [pdentryCurrs3 (Hs3 & HblockEnabled)].
            rewrite Hs3. simpl. rewrite HbeqCurrBlockSce. rewrite <-beqAddrFalse in HbeqCurrBlockSce.
            rewrite removeDupIdentity; intuition.
          - specialize(HblockNotEnabled HtrivFalse). subst s3. reflexivity.
        }
        assert(HlookupBlockSceEqs2s1: lookup (CPaddr (blockToShareInCurrPartAddr + scoffset)) (memory s2) beqAddr
                                = lookup (CPaddr (blockToShareInCurrPartAddr + scoffset)) (memory s1) beqAddr).
        {
          rewrite Hs2. simpl. rewrite beqAddrSym in HbeqBlockSceBlock. rewrite HbeqBlockSceBlock.
          rewrite <-beqAddrFalse in HbeqBlockSceBlock.
          rewrite removeDupIdentity; try(apply not_eq_sym; assumption). reflexivity.
        }
        assert(HlookupBlockSceEqs1s0: lookup (CPaddr (blockToShareInCurrPartAddr + scoffset)) (memory s1) beqAddr
                                = lookup (CPaddr (blockToShareInCurrPartAddr + scoffset)) (memory s0) beqAddr).
        {
          rewrite Hs1. simpl. rewrite Hsceaddr. rewrite HbeqNewSceBlockSce.
          assert(HbeqNewNewSce: beqAddr idNewSubblock (CPaddr (idNewSubblock + scoffset)) = false)
            by (rewrite beqAddrSym; assumption). rewrite HbeqNewNewSce. simpl.
          assert(HbeqNewBlockSce: beqAddr idNewSubblock (CPaddr (blockToShareInCurrPartAddr + scoffset)) = false)
            by (rewrite beqAddrSym; assumption). rewrite HbeqNewBlockSce. rewrite InternalLemmas.beqAddrTrue.
          rewrite HbeqCurrNew. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
          rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
          rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
          rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
          rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
          rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
          rewrite removeDupIdentity; try(apply not_eq_sym; assumption). simpl.
          rewrite beqAddrFalse in HbeqCurrBlockSce. rewrite HbeqCurrBlockSce. rewrite InternalLemmas.beqAddrTrue.
          rewrite <-beqAddrFalse in HbeqCurrBlockSce.
          rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
          rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
          rewrite removeDupIdentity; try(apply not_eq_sym; assumption). reflexivity.
        }
        rewrite HlookupBlockSceEqs4s3 in HlookupBlockSces4. rewrite HlookupBlockSceEqs3s2 in HlookupBlockSces4.
        rewrite HlookupBlockSceEqs2s1 in HlookupBlockSces4. rewrite HlookupBlockSceEqs1s0 in HlookupBlockSces4.
        rewrite HlookupBlockSces4 in HoriginBlocks0. assumption.
      }
      specialize(HoriginParent currentPart pdentryPart blockToShareInCurrPartAddr
          (CPaddr (blockToShareInCurrPartAddr + scoffset)) blockOrigin HpartIsPart HlookupPart HblockMappedCurrs
          HeqTriv HoriginBlocks). destruct HoriginParent as (_ & HstartAbove).
      assert(HstartBlocks: bentryStartAddr blockToShareInCurrPartAddr blockToCutStartAddr s).
      {
        unfold bentryStartAddr in *. rewrite HlookupBlocks. rewrite HlookupBlocks0 in HstartBlocks0.
        rewrite HbentryShares2. simpl. assumption.
      }
      specialize(HstartAbove blockToCutStartAddr HstartBlocks). unfold StateLib.Paddr.leb in HlebCutStart.
      apply eq_sym in HlebCutStart. apply PeanoNat.Nat.leb_gt in HlebCutStart. subst cutAddr. lia.
    }
    destruct (beqAddr blockToShareInCurrPartAddr block) eqn:HbeqBlockBlock.
    {
      rewrite <-beqAddrTrue in HbeqBlockBlock. subst block. unfold scentryNext in Hnext. subst scentryaddr.
      rewrite HlookupBlockSceEqss5 in Hnext. rewrite Hs5 in Hnext. simpl in Hnext.
      rewrite InternalLemmas.beqAddrTrue in Hnext. simpl in Hnext. rewrite <-beqAddrFalse in HbeqNullNew.
      exfalso; congruence.
    }
    destruct (beqAddr part currentPart) eqn:HbeqPartCurr.
    - rewrite <-beqAddrTrue in HbeqPartCurr. subst part. rewrite HgetBlocksCurrEqss0 in HblockMapped.
      rewrite <-beqAddrFalse in HbeqNewBlockBis.
      destruct HblockMapped as [Hcontra | HblockMapped]; try(exfalso; congruence).
      rewrite beqAddrFalse in HbeqNewBlockBis.
      assert(HlookupBlockEq: lookup block (memory s) beqAddr = lookup block (memory s0) beqAddr).
      { apply HBElookupEqss0; assumption. }
      unfold bentryStartAddr in Hstart. unfold bentryEndAddr in Hend. unfold bentryPFlag in HPFlag.
      rewrite HlookupBlockEq in *.
      destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) scentryaddr) eqn:HbeqBlockSceSce.
      {
        assert(Hnull: nullAddrExists s4) by (unfold consistency1 in *; intuition). unfold nullAddrExists in Hnull.
        unfold isPADDR in Hnull.
        rewrite <-beqAddrTrue in HbeqBlockSceSce. rewrite <-HbeqBlockSceSce in *. exfalso.
        rewrite <-beqAddrFalse in HbeqBlockBlock. unfold CPaddr in Hscentryaddr.
        destruct (Compare_dec.le_dec (blockToShareInCurrPartAddr + scoffset) maxAddr) eqn:HleBlockSceMax.
        + destruct (Compare_dec.le_dec (block + scoffset) maxAddr).
          * injection Hscentryaddr as Hcontra. apply PeanoNat.Nat.add_cancel_r in Hcontra.
            contradict HbeqBlockBlock. destruct blockToShareInCurrPartAddr. destruct block. simpl in Hcontra.
            subst p0. f_equal. apply proof_irrelevance.
          * assert(Hcontra: CPaddr (blockToShareInCurrPartAddr + scoffset) = nullAddr).
            {
              unfold nullAddr. unfold CPaddr. rewrite HleBlockSceMax. rewrite Hscentryaddr.
              destruct (Compare_dec.le_dec 0 maxAddr); try(lia). f_equal. apply proof_irrelevance.
            }
            rewrite Hcontra in *. rewrite HlookupBlockSces4 in Hnull. congruence.
        + assert(Hcontra: CPaddr (blockToShareInCurrPartAddr + scoffset) = nullAddr).
          {
            unfold nullAddr. unfold CPaddr. rewrite HleBlockSceMax.
            destruct (Compare_dec.le_dec 0 maxAddr); try(lia). f_equal. apply proof_irrelevance.
          }
          rewrite Hcontra in *. rewrite HlookupBlockSces4 in Hnull. congruence.
      }
      destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) scentryaddr) eqn:HbeqNewSceSce.
      {
        rewrite <-beqAddrTrue in HbeqNewSceSce. rewrite <-HbeqNewSceSce in *. exfalso.
        rewrite <-beqAddrFalse in HbeqNewBlockBis. unfold CPaddr in Hscentryaddr.
        assert(Hnull: nullAddrExists s3) by (unfold consistency1 in *; intuition). unfold nullAddrExists in Hnull.
        unfold isPADDR in Hnull.
        destruct (Compare_dec.le_dec (idNewSubblock + scoffset) maxAddr) eqn:HleNewSceMax.
        + destruct (Compare_dec.le_dec (block + scoffset) maxAddr).
          * injection Hscentryaddr as Hcontra. apply PeanoNat.Nat.add_cancel_r in Hcontra.
            contradict HbeqNewBlockBis. destruct idNewSubblock. destruct block. simpl in Hcontra.
            subst p0. f_equal. apply proof_irrelevance.
          * assert(Hcontra: CPaddr (idNewSubblock + scoffset) = nullAddr).
            {
              unfold nullAddr. unfold CPaddr. rewrite HleNewSceMax. rewrite Hscentryaddr.
              destruct (Compare_dec.le_dec 0 maxAddr); try(lia). f_equal. apply proof_irrelevance.
            }
            rewrite Hcontra in *. rewrite HlookupNewSces3 in Hnull. congruence.
        + assert(Hcontra: CPaddr (idNewSubblock + scoffset) = nullAddr).
          {
            unfold nullAddr. unfold CPaddr. rewrite HleNewSceMax.
            destruct (Compare_dec.le_dec 0 maxAddr); try(lia). f_equal. apply proof_irrelevance.
          }
          rewrite Hcontra in *. rewrite HlookupNewSces3 in Hnull. congruence.
      }
      assert(HlookupSceEq: lookup scentryaddr (memory s) beqAddr = lookup scentryaddr (memory s0) beqAddr).
      {
        apply HSCElookupEqs0; try(assumption).
        assert(HwellFormedShadow: wellFormedShadowCutIfBlockEntry s0)
            by (unfold consistency in *; unfold consistency1 in *; intuition).
        specialize(HwellFormedShadow block HblockIsBE). destruct HwellFormedShadow as [sce (Hres & Hsce)].
        subst sce. rewrite <-Hscentryaddr in Hres. assumption.
      }
      unfold scentryOrigin in Horigin. unfold scentryNext in Hnext. rewrite HlookupSceEq in *.
      specialize(Hcons0 currentPart pdentryCurrs0 block scentryaddr startaddr endaddr HpartIsPart HblockMapped
          HblockIsBE Hstart Hend HPFlag Hscentryaddr Horigin Hnext HlookupCurrs0 HbeqPartRoot).
      destruct Hcons0 as [blockParent (HblockParentMapped & HblockParentIsBE & HstartParent & HendParent)].
      exists blockParent.
      assert(HparentsEq: parent pdentryPart = parent pdentryCurrs0).
      {
        assert(Heqss5: parent pdentryPart = parent pdentryCurrs5).
        {
          destruct newSubEnabled.
          + specialize(HnewEnabled HtrivTrue). destruct HnewEnabled as [pdentryCurrs (Hs & HnewEnabled)].
            rewrite Hs in HlookupPart. simpl in HlookupPart. rewrite InternalLemmas.beqAddrTrue in HlookupPart.
            injection HlookupPart as Hres. rewrite <-Hres. simpl. reflexivity.
          + specialize(HnewNotEnabled HtrivFalse). subst s. rewrite HlookupCurrs5 in HlookupPart.
            injection HlookupPart as Hres. subst pdentryPart. reflexivity.
        }
        assert(Heqs5s2: parent pdentryCurrs5 = parent pdentryCurrs2).
        {
          rewrite Hs5 in HlookupCurrs5. simpl in HlookupCurrs5. rewrite beqAddrSym in HbeqCurrBlockSce.
          rewrite HbeqCurrBlockSce in HlookupCurrs5. rewrite <-beqAddrFalse in HbeqCurrBlockSce.
          rewrite removeDupIdentity in HlookupCurrs5; try(apply not_eq_sym; assumption).
          rewrite Hs4 in HlookupCurrs5. simpl in HlookupCurrs5.
          destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) currentPart) eqn:HbeqNewSceCurr;
            try(exfalso; congruence). rewrite <-beqAddrFalse in HbeqNewSceCurr.
          rewrite removeDupIdentity in HlookupCurrs5; try(apply not_eq_sym; assumption).
          destruct blockToShareEnabled.
          + specialize(HblockEnabled HtrivTrue). destruct HblockEnabled as [pdentryCurrs3 (Hs3 & HblockEnabled)].
            rewrite Hs3 in HlookupCurrs5. simpl in HlookupCurrs5.
            rewrite InternalLemmas.beqAddrTrue in HlookupCurrs5. injection HlookupCurrs5 as Hres.
            rewrite <-Hres. simpl. reflexivity.
          + specialize(HblockNotEnabled HtrivFalse). subst s3. rewrite HlookupCurrs2 in HlookupCurrs5.
            injection HlookupCurrs5 as Hres. rewrite Hres. reflexivity.
        }
        assert(Heqs2s0: parent pdentryCurrs2 = parent pdentryCurrs0).
        {
          rewrite Hs2 in HlookupCurrs2. simpl in HlookupCurrs2. rewrite beqAddrSym in HbeqCurrBlock.
          rewrite HbeqCurrBlock in HlookupCurrs2. rewrite <-beqAddrFalse in HbeqCurrBlock.
          rewrite removeDupIdentity in HlookupCurrs2; try(apply not_eq_sym; assumption).
          rewrite Hs1 in HlookupCurrs2. simpl in HlookupCurrs2. rewrite beqAddrSym in HbeqCurrSce.
          rewrite HbeqCurrSce in HlookupCurrs2. rewrite HbeqNewSce in HlookupCurrs2. simpl in HlookupCurrs2.
          assert(HbeqNewCurr: beqAddr idNewSubblock currentPart = false) by (rewrite beqAddrSym; assumption).
          rewrite HbeqNewCurr in HlookupCurrs2. rewrite InternalLemmas.beqAddrTrue in HlookupCurrs2.
          rewrite HbeqCurrNew in HlookupCurrs2. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in HlookupCurrs2; try(apply not_eq_sym; assumption).
          rewrite removeDupIdentity in HlookupCurrs2; try(apply not_eq_sym; assumption).
          rewrite removeDupIdentity in HlookupCurrs2; try(apply not_eq_sym; assumption).
          rewrite removeDupIdentity in HlookupCurrs2; try(apply not_eq_sym; assumption).
          rewrite removeDupIdentity in HlookupCurrs2; try(apply not_eq_sym; assumption).
          rewrite removeDupIdentity in HlookupCurrs2; try(apply not_eq_sym; assumption).
          rewrite removeDupIdentity in HlookupCurrs2; try(apply not_eq_sym; assumption).
          simpl in HlookupCurrs2. rewrite InternalLemmas.beqAddrTrue in HlookupCurrs2.
          injection HlookupCurrs2 as Hres. rewrite <-Hres. simpl. rewrite HpdentryInter0. simpl. reflexivity.
        }
        rewrite Heqss5. rewrite Heqs5s2. rewrite Heqs2s0. reflexivity.
      }
      rewrite HparentsEq.
      assert(HparentOfPart: parentOfPartitionIsPartition s0)
          by (unfold consistency in *; unfold consistency1 in *; intuition).
      specialize(HparentOfPart currentPart pdentryCurrs0 HlookupCurrs0).
      destruct HparentOfPart as (HparentIsPart & _ & HparentNotPart). specialize(HparentIsPart HbeqPartRoot).
      destruct HparentIsPart as ([pdentryParent HlookupParent] & HparentIsPart).
      assert(HparentIsPDT: isPDT (parent pdentryCurrs0) s0) by (unfold isPDT; rewrite HlookupParent; trivial).
      rewrite HgetBlocksEqss0; try(assumption). rewrite HBEEqss0. split. assumption. split. assumption.
      unfold getMappedBlocks in HblockMappedCurrs0. apply InFilterPresentInList in HblockMappedCurrs0.
      unfold getMappedBlocks in HnewMappedCurrs. apply InFilterPresentInList in HnewMappedCurrs.
      destruct (beqAddr blockToShareInCurrPartAddr blockParent) eqn:HbeqBlockBlockParent.
      {
        unfold getMappedBlocks in HblockParentMapped. apply InFilterPresentInList in HblockParentMapped.
        assert(Hdisjoint: DisjointKSEntries s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
        specialize(Hdisjoint (parent pdentryCurrs0) currentPart HparentIsPDT HcurrIsPDTs0 HparentNotPart).
        destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
        specialize(Hdisjoint blockParent HblockParentMapped). rewrite <-beqAddrTrue in HbeqBlockBlockParent.
        rewrite HbeqBlockBlockParent in *. exfalso; congruence.
      }
      destruct (beqAddr idNewSubblock blockParent) eqn:HbeqNewBlockParent.
      {
        rewrite <-HgetBlocksEqss0 in HblockParentMapped; try(assumption).
        unfold getMappedBlocks in HblockParentMapped. apply InFilterPresentInList in HblockParentMapped.
        rewrite <-HPDTEqs2s0 in HparentIsPDT. rewrite <-HPDTEqs3s2 in HparentIsPDT.
        rewrite <-HPDTEqs4s3 in HparentIsPDT. rewrite <-HPDTEqs5s4 in HparentIsPDT.
        rewrite <-HPDTEqss5 in HparentIsPDT.
        assert(Hdisjoint: DisjointKSEntries s) by (unfold consistency in *; unfold consistency1 in *; intuition).
        specialize(Hdisjoint (parent pdentryCurrs0) currentPart HparentIsPDT HcurrIsPDTs HparentNotPart).
        destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
        specialize(Hdisjoint blockParent HblockParentMapped). rewrite <-beqAddrTrue in HbeqNewBlockParent.
        rewrite HbeqNewBlockParent in *. exfalso; congruence.
      }
      assert(HlookupBlockParentEq: lookup blockParent (memory s) beqAddr
                                    = lookup blockParent (memory s0) beqAddr).
      { apply HBElookupEqss0; assumption. }
      unfold bentryStartAddr. unfold bentryEndAddr. rewrite HlookupBlockParentEq. split; assumption.
    - rewrite <-beqAddrFalse in HbeqPartCurr.
      assert(HpartIsPDT: isPDT part s) by (unfold isPDT; rewrite HlookupPart; trivial).
      assert(HpartIsPDTs0: isPDT part s0).
      {
        rewrite <-HPDTEqs2s0. rewrite <-HPDTEqs3s2. rewrite <-HPDTEqs4s3. rewrite <-HPDTEqs5s4.
        rewrite <-HPDTEqss5. assumption.
      }
      rewrite HgetBlocksEqss0 in HblockMapped; try(assumption).
      assert(HlookupBlockEq: lookup block (memory s) beqAddr = lookup block (memory s0) beqAddr).
      { apply HBElookupEqss0; assumption. }
      unfold bentryStartAddr in Hstart. unfold bentryEndAddr in Hend. unfold bentryPFlag in HPFlag.
      rewrite HlookupBlockEq in *.
      destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + scoffset)) scentryaddr) eqn:HbeqBlockSceSce.
      {
        assert(Hnull: nullAddrExists s4) by (unfold consistency1 in *; intuition). unfold nullAddrExists in Hnull.
        unfold isPADDR in Hnull.
        rewrite <-beqAddrTrue in HbeqBlockSceSce. rewrite <-HbeqBlockSceSce in *. exfalso.
        rewrite <-beqAddrFalse in HbeqBlockBlock. unfold CPaddr in Hscentryaddr.
        destruct (Compare_dec.le_dec (blockToShareInCurrPartAddr + scoffset) maxAddr) eqn:HleBlockSceMax.
        + destruct (Compare_dec.le_dec (block + scoffset) maxAddr).
          * injection Hscentryaddr as Hcontra. apply PeanoNat.Nat.add_cancel_r in Hcontra.
            contradict HbeqBlockBlock. destruct blockToShareInCurrPartAddr. destruct block. simpl in Hcontra.
            subst p0. f_equal. apply proof_irrelevance.
          * assert(Hcontra: CPaddr (blockToShareInCurrPartAddr + scoffset) = nullAddr).
            {
              unfold nullAddr. unfold CPaddr. rewrite HleBlockSceMax. rewrite Hscentryaddr.
              destruct (Compare_dec.le_dec 0 maxAddr); try(lia). f_equal. apply proof_irrelevance.
            }
            rewrite Hcontra in *. rewrite HlookupBlockSces4 in Hnull. congruence.
        + assert(Hcontra: CPaddr (blockToShareInCurrPartAddr + scoffset) = nullAddr).
          {
            unfold nullAddr. unfold CPaddr. rewrite HleBlockSceMax.
            destruct (Compare_dec.le_dec 0 maxAddr); try(lia). f_equal. apply proof_irrelevance.
          }
          rewrite Hcontra in *. rewrite HlookupBlockSces4 in Hnull. congruence.
      }
      destruct (beqAddr (CPaddr (idNewSubblock + scoffset)) scentryaddr) eqn:HbeqNewSceSce.
      {
        rewrite <-beqAddrTrue in HbeqNewSceSce. rewrite <-HbeqNewSceSce in *. exfalso.
        rewrite <-beqAddrFalse in HbeqNewBlockBis. unfold CPaddr in Hscentryaddr.
        assert(Hnull: nullAddrExists s3) by (unfold consistency1 in *; intuition). unfold nullAddrExists in Hnull.
        unfold isPADDR in Hnull.
        destruct (Compare_dec.le_dec (idNewSubblock + scoffset) maxAddr) eqn:HleNewSceMax.
        + destruct (Compare_dec.le_dec (block + scoffset) maxAddr).
          * injection Hscentryaddr as Hcontra. apply PeanoNat.Nat.add_cancel_r in Hcontra.
            contradict HbeqNewBlockBis. destruct idNewSubblock. destruct block. simpl in Hcontra.
            subst p0. f_equal. apply proof_irrelevance.
          * assert(Hcontra: CPaddr (idNewSubblock + scoffset) = nullAddr).
            {
              unfold nullAddr. unfold CPaddr. rewrite HleNewSceMax. rewrite Hscentryaddr.
              destruct (Compare_dec.le_dec 0 maxAddr); try(lia). f_equal. apply proof_irrelevance.
            }
            rewrite Hcontra in *. rewrite HlookupNewSces3 in Hnull. congruence.
        + assert(Hcontra: CPaddr (idNewSubblock + scoffset) = nullAddr).
          {
            unfold nullAddr. unfold CPaddr. rewrite HleNewSceMax.
            destruct (Compare_dec.le_dec 0 maxAddr); try(lia). f_equal. apply proof_irrelevance.
          }
          rewrite Hcontra in *. rewrite HlookupNewSces3 in Hnull. congruence.
      }
      assert(HlookupSceEq: lookup scentryaddr (memory s) beqAddr = lookup scentryaddr (memory s0) beqAddr).
      {
        apply HSCElookupEqs0; try(assumption).
        assert(HwellFormedShadow: wellFormedShadowCutIfBlockEntry s0)
            by (unfold consistency in *; unfold consistency1 in *; intuition).
        specialize(HwellFormedShadow block HblockIsBE). destruct HwellFormedShadow as [sce (Hres & Hsce)].
        subst sce. rewrite <-Hscentryaddr in Hres. assumption.
      }
      unfold scentryOrigin in Horigin. unfold scentryNext in Hnext. rewrite HlookupSceEq in *.
      assert(HpartLookupEqss0: lookup part (memory s) beqAddr = lookup part (memory s0) beqAddr).
      { apply HPDTlookupEqss0; try(assumption). rewrite <-beqAddrFalse. assumption. }
      rewrite HpartLookupEqss0 in HlookupPart.
      specialize(Hcons0 part pdentryPart block scentryaddr startaddr endaddr HpartIsPart HblockMapped HblockIsBE
          Hstart Hend HPFlag Hscentryaddr Horigin Hnext HlookupPart HbeqPartRoot).
      destruct Hcons0 as [blockParent (HblockParentMapped & HblockParentIsBE & HstartParent & HendParent)].
      exists blockParent. split.
      {
        destruct (beqAddr (parent pdentryPart) currentPart) eqn:HbeqParentCurr.
        - rewrite <-beqAddrTrue in HbeqParentCurr. rewrite HbeqParentCurr in *.
          apply HgetBlocksCurrEqss0. right. assumption.
        - rewrite <-beqAddrFalse in HbeqParentCurr. rewrite HgetBlocksEqss0; try(assumption).
          assert(HparentOfPart: parentOfPartitionIsPartition s0)
            by (unfold consistency in *; unfold consistency1 in *; intuition).
          specialize(HparentOfPart part pdentryPart HlookupPart).
          destruct HparentOfPart as (HparentIsPart & _ & _). specialize(HparentIsPart HbeqPartRoot).
          destruct HparentIsPart as ([pdentryParent HlookupParent] & _). unfold isPDT. rewrite HlookupParent.
          trivial.
      }
      rewrite HBEEqss0. split. assumption.
      destruct (beqAddr blockToShareInCurrPartAddr blockParent) eqn:HbeqBlockBlockParent.
      {
        rewrite <-beqAddrTrue in HbeqBlockBlockParent. subst blockParent.
        destruct HPDChildBlocks0 as [sh1entry [sh1entryaddr (HlookupSh1 & HPDChildBlocks0 & Hsh1IsSh1)]].
        rewrite <-beqAddrTrue in HbeqPDChildNull. exfalso.
        assert(HblockProps: childsBlocksPropsInParent s0)
            by (unfold consistency in *; unfold consistency2 in *; intuition).
        assert(HparentOfPart: parentOfPartitionIsPartition s0)
            by (unfold consistency in *; unfold consistency1 in *; intuition).
        specialize(HparentOfPart part pdentryPart HlookupPart).
        destruct HparentOfPart as (HparentIsPart & _ & HbeqParentPart). specialize(HparentIsPart HbeqPartRoot).
        destruct HparentIsPart as ([parentEntry HlookupParent] & HparentIsPart).
        assert(HpartIsChild: In part (getChildren (parent pdentryPart) s0)).
        {
          assert(HisChild: isChild s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
          specialize(HisChild part (parent pdentryPart) HpartIsPart). apply HisChild. unfold pdentryParent.
          rewrite HlookupPart. reflexivity.
        }
        assert(HstartTriv: startaddr <= startaddr) by lia.
        assert(HendTriv: endaddr >= endaddr) by lia.
        specialize(HblockProps part (parent pdentryPart) block startaddr endaddr blockToShareInCurrPartAddr
          startaddr endaddr HparentIsPart HpartIsChild HblockMapped Hstart Hend HPFlag HblockParentMapped
          HstartParent HendParent HPFlagBlocks0 HstartTriv HendTriv).
        destruct HblockProps as (_ & Hcontra & _). unfold sh1entryAddr in Hsh1IsSh1.
        rewrite HlookupBlocks0 in Hsh1IsSh1. subst sh1entryaddr.
        specialize(Hcontra PDChildAddr HPDChildBlocks0). congruence.
      }
      destruct (beqAddr idNewSubblock blockParent) eqn:HbeqNewBlockParent.
      {
        rewrite <-beqAddrTrue in HbeqNewBlockParent. subst blockParent. unfold isFreeSlot in HnewIsFreeSlots0.
        rewrite HlookupNews0 in HnewIsFreeSlots0. exfalso.
        destruct (lookup (CPaddr (idNewSubblock + sh1offset)) (memory s0) beqAddr); try(congruence).
        destruct v; try(congruence).
        destruct (lookup (CPaddr (idNewSubblock + scoffset)) (memory s0) beqAddr); try(congruence).
        destruct v; try(congruence). destruct HnewIsFreeSlots0 as (_ & _ & _ & _ & HnotPresent & _).
        pose proof (BlockPresentFalseNotMapped (parent pdentryPart) idNewSubblock bentry s0 HlookupNews0
          HnotPresent) as Hcontra. congruence.
      }
      assert(HlookupBlockParentEqss0: lookup blockParent (memory s) beqAddr
                                      = lookup blockParent (memory s0) beqAddr).
      { apply HBElookupEqss0; assumption. }
      unfold bentryStartAddr. unfold bentryEndAddr. rewrite HlookupBlockParentEqss0. split; assumption.
    (* END adressesRangePreservedIfOriginAndNextOk *)
  }

  split.
  {
    (* BEGIN childsBlocksPropsInParent s *)
    assert(Hcons0: childsBlocksPropsInParent s0)
        by (unfold consistency in *; unfold consistency2 in *; intuition).
    intros child pdparent blockChild startChild endChild blockParent startParent endParent HparentIsPart
      HchildIsChild HblockChildMapped HstartChild HendChild HPFlagChild HblockParentMapped HstartParent HendParent
      HPFlagParent HlebStart HlebEnd. rewrite HgetPartsEqss0 in HparentIsPart.
    assert(HparentIsPDTs0: isPDT pdparent s0).
    {
      apply partitionsArePDT; try(assumption).
      unfold consistency in *; unfold consistency1 in *; intuition.
      unfold consistency in *; unfold consistency1 in *; intuition.
    }
    rewrite HgetChildrenEqss0 in HchildIsChild; try(assumption).
    assert(Hparent: isParent s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
    specialize(Hparent child pdparent HparentIsPart HchildIsChild). unfold pdentryParent in Hparent.
    destruct (lookup child (memory s0) beqAddr) eqn:HlookupChild; try(exfalso; congruence).
    destruct v; try(exfalso; congruence).
    assert(HparentOfPart: parentOfPartitionIsPartition s0)
        by (unfold consistency in *; unfold consistency1 in *; intuition).
    specialize(HparentOfPart child p HlookupChild).
    destruct HparentOfPart as (HparentIsPDT & HparentOfRoot & HbeqParentChild).
    destruct (beqAddr child constantRootPartM) eqn:HbeqChildRoot.
    {
      rewrite <-beqAddrTrue in HbeqChildRoot. specialize(HparentOfRoot HbeqChildRoot). rewrite HparentOfRoot in *.
      subst pdparent.
      assert(Hnull: nullAddrExists s) by (unfold consistency1 in *; intuition).
      unfold nullAddrExists in Hnull. unfold isPADDR in Hnull. unfold getMappedBlocks in HblockParentMapped.
      unfold getKSEntries in HblockParentMapped. exfalso.
      destruct (lookup nullAddr (memory s) beqAddr); try(congruence). destruct v; try(congruence).
      simpl in HblockParentMapped. congruence.
    }
    rewrite <-beqAddrFalse in HbeqChildRoot. specialize(HparentIsPDT HbeqChildRoot).
    destruct HparentIsPDT as ([parentEntry HlookupParent] & _). rewrite <-Hparent in *.
    assert(HchildIsPDTs0: isPDT child s0) by (unfold isPDT; rewrite HlookupChild; trivial).
    assert(HblockChildIsBE: isBE blockChild s).
    {
      unfold isBE. unfold bentryStartAddr in HstartChild.
      destruct (lookup blockChild (memory s) beqAddr); try(congruence). destruct v; try(congruence). trivial.
    }
    rewrite HBEEqss0 in HblockChildIsBE.
    assert(HblockParentIsBE: isBE blockParent s).
    {
      unfold isBE. unfold bentryStartAddr in HstartParent.
      destruct (lookup blockParent (memory s) beqAddr); try(congruence). destruct v; try(congruence). trivial.
    }
    rewrite HBEEqss0 in HblockParentIsBE.
    destruct (beqAddr currentPart pdparent) eqn:HbeqCurrParent.
    - rewrite <-beqAddrTrue in HbeqCurrParent. rewrite <-HbeqCurrParent in *.
      destruct (beqAddr idNewSubblock blockChild) eqn:HbeqNewBlockChild.
      {
        rewrite <-beqAddrTrue in HbeqNewBlockChild. subst blockChild. exfalso.
        assert(Hdisjoint: DisjointKSEntries s) by (unfold consistency1 in *; intuition).
        rewrite <-HPDTEqs2s0 in HchildIsPDTs0. rewrite <-HPDTEqs3s2 in HchildIsPDTs0.
        rewrite <-HPDTEqs4s3 in HchildIsPDTs0. rewrite <-HPDTEqs5s4 in HchildIsPDTs0.
        rewrite <-HPDTEqss5 in HchildIsPDTs0.
        specialize(Hdisjoint currentPart child HcurrIsPDTs HchildIsPDTs0 HbeqParentChild).
        destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
        unfold getMappedBlocks in HnewMappedCurrs. unfold getMappedBlocks in HblockChildMapped.
        apply InFilterPresentInList in HnewMappedCurrs. apply InFilterPresentInList in HblockChildMapped.
        specialize(Hdisjoint idNewSubblock HnewMappedCurrs). congruence.
      }
      rewrite HgetBlocksEqss0 in HblockChildMapped; try(apply not_eq_sym in HbeqParentChild; assumption).
      destruct (beqAddr blockToShareInCurrPartAddr blockChild) eqn:HbeqBlockBlockChild.
      {
        rewrite <-beqAddrTrue in HbeqBlockBlockChild. subst blockChild.
        assert(Hdisjoint: DisjointKSEntries s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
        specialize(Hdisjoint currentPart child HcurrIsPDTs0 HchildIsPDTs0 HbeqParentChild).
        destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
        unfold getMappedBlocks in HblockMappedCurrs0. unfold getMappedBlocks in HblockChildMapped.
        apply InFilterPresentInList in HblockMappedCurrs0. apply InFilterPresentInList in HblockChildMapped.
        specialize(Hdisjoint blockToShareInCurrPartAddr HblockMappedCurrs0). congruence.
      }
      assert(HlookupBlockChildEq: lookup blockChild (memory s) beqAddr = lookup blockChild (memory s0) beqAddr).
      { apply HBElookupEqss0; assumption. }
      unfold bentryStartAddr in HstartChild. unfold bentryEndAddr in HendChild. unfold bentryPFlag in HPFlagChild.
      rewrite HlookupBlockChildEq in *.
      destruct (beqAddr idNewSubblock blockParent) eqn:HbeqNewBlockParent.
      {
        rewrite <-beqAddrTrue in HbeqNewBlockParent. subst blockParent. exfalso.
        assert(HlebStartBlock: blockToCutStartAddr <= startChild).
        {
          unfold bentryStartAddr in HstartParent. rewrite HlookupNews in HstartParent.
          rewrite Hbentry6simpl in HstartParent. simpl in HstartParent. subst startParent.
          unfold StateLib.Paddr.leb in HlebCutStart. apply eq_sym in HlebCutStart.
          apply Compare_dec.leb_iff_conv in HlebCutStart. lia.
        }
        assert(HlebEndBlock: blockToCutEndAddr >= endChild).
        {
          unfold bentryEndAddr in HendParent. rewrite HlookupNews in HendParent.
          rewrite Hbentry6simpl in HendParent. simpl in HendParent. subst endParent.
          unfold StateLib.Paddr.leb in HlebEndCut. apply eq_sym in HlebEndCut.
          apply Compare_dec.leb_iff_conv in HlebEndCut. unfold bentryEndAddr in *. rewrite HlookupBlocks0 in *.
          rewrite <-HendBlocks0 in HendBlockBiss0. subst blockToCutEndAddr. lia.
        }
        specialize(Hcons0 child currentPart blockChild startChild endChild blockToShareInCurrPartAddr
          blockToCutStartAddr blockToCutEndAddr HparentIsPart HchildIsChild HblockChildMapped HstartChild
          HendChild HPFlagChild HblockMappedCurrs0 HstartBlocks0 HendBlockBiss0 HPFlagBlocks0 HlebStartBlock
          HlebEndBlock).
        destruct Hcons0 as (_ & Hcontra & _).
        destruct HPDChildBlocks0 as [sh1entry [sh1entryaddr (HlookupSh1 & HPDChildBlocks0 & Hsh1)]].
        unfold sh1entryAddr in Hsh1. rewrite HlookupBlocks0 in Hsh1. subst sh1entryaddr.
        specialize(Hcontra PDChildAddr HPDChildBlocks0). rewrite <-beqAddrTrue in HbeqPDChildNull. congruence.
      }
      apply HgetBlocksCurrEqss0 in HblockParentMapped. rewrite <-beqAddrFalse in HbeqNewBlockParent.
      destruct HblockParentMapped as [Hcontra | HblockParentMapped]; try(exfalso; congruence).
      destruct (beqAddr blockToShareInCurrPartAddr blockParent) eqn:HbeqBlockBlockParent.
      {
        rewrite <-beqAddrTrue in HbeqBlockBlockParent. subst blockParent. exfalso.
        assert(HstartParents0: bentryStartAddr blockToShareInCurrPartAddr startParent s0).
        {
          unfold bentryStartAddr in *. rewrite HlookupBlocks in HstartParent. rewrite HlookupBlocks0.
          rewrite HbentryShares2 in HstartParent. simpl in HstartParent. assumption.
        }
        assert(HlebEndBlock: blockToCutEndAddr >= endChild).
        {
          unfold bentryEndAddr in HendParent. rewrite HlookupBlocks in HendParent.
          rewrite HbentryShares2 in HendParent. simpl in HendParent. subst endParent.
          unfold StateLib.Paddr.leb in HlebEndCut. apply eq_sym in HlebEndCut.
          apply Compare_dec.leb_iff_conv in HlebEndCut. unfold bentryEndAddr in *. rewrite HlookupBlocks0 in *.
          rewrite <-HendBlocks0 in HendBlockBiss0. subst blockToCutEndAddr. lia.
        }
        specialize(Hcons0 child currentPart blockChild startChild endChild blockToShareInCurrPartAddr
          startParent blockToCutEndAddr HparentIsPart HchildIsChild HblockChildMapped HstartChild HendChild
          HPFlagChild HblockMappedCurrs0 HstartParents0 HendBlockBiss0 HPFlagBlocks0 HlebStart HlebEndBlock).
        destruct Hcons0 as (_ & Hcontra & _).
        destruct HPDChildBlocks0 as [sh1entry [sh1entryaddr (HlookupSh1 & HPDChildBlocks0 & Hsh1)]].
        unfold sh1entryAddr in Hsh1. rewrite HlookupBlocks0 in Hsh1. subst sh1entryaddr.
        specialize(Hcontra PDChildAddr HPDChildBlocks0). rewrite <-beqAddrTrue in HbeqPDChildNull. congruence.
      }
      rewrite beqAddrFalse in HbeqNewBlockParent.
      assert(HlookupBlockParentEq: lookup blockParent (memory s) beqAddr
                                    = lookup blockParent (memory s0) beqAddr).
      { apply HBElookupEqss0; assumption. }
      unfold bentryStartAddr in HstartParent. unfold bentryEndAddr in HendParent.
      unfold bentryPFlag in HPFlagParent. rewrite HlookupBlockParentEq in *.
      specialize(Hcons0 child currentPart blockChild startChild endChild blockParent startParent endParent
        HparentIsPart HchildIsChild HblockChildMapped HstartChild HendChild HPFlagChild HblockParentMapped
        HstartParent HendParent HPFlagParent HlebStart HlebEnd).
      assert(HlookupParentSh1Eq: lookup (CPaddr (blockParent + sh1offset)) (memory s) beqAddr
                                  = lookup (CPaddr (blockParent + sh1offset)) (memory s0) beqAddr).
      {
        assert(HwellFormed: wellFormedFstShadowIfBlockEntry s0)
          by (unfold consistency in *; unfold consistency1 in *; intuition).
        specialize(HwellFormed blockParent HblockParentIsBE). apply HSHElookupEqss0; assumption.
      }
      destruct Hcons0 as (HcheckChild & HPDChild & HchildLoc & HblockAccIfNotCut). split.
      {
        unfold checkChild in *. rewrite HlookupBlockParentEq. rewrite HlookupParentSh1Eq. assumption.
      } split.
      {
        intros childGlobalID HPDChilds. apply HPDChild. unfold sh1entryPDchild in *. rewrite <-HlookupParentSh1Eq.
        assumption.
      } split.
      {
        unfold sh1entryInChildLocation in *. rewrite HlookupParentSh1Eq. intros blockIDInChild HchildLocs.
        apply HchildLoc. destruct (lookup (CPaddr (blockParent + sh1offset)) (memory s0) beqAddr);
        try(congruence). destruct v; congruence.
      }
      unfold bentryAFlag. rewrite HlookupBlockParentEq. assumption.
    - rewrite <-beqAddrFalse in HbeqCurrParent.
      destruct (beqAddr idNewSubblock blockParent) eqn:HbeqNewBlockParent.
      {
        rewrite <-beqAddrTrue in HbeqNewBlockParent. subst blockParent. exfalso.
        assert(Hdisjoint: DisjointKSEntries s) by (unfold consistency1 in *; intuition).
        rewrite <-HPDTEqs2s0 in HparentIsPDTs0. rewrite <-HPDTEqs3s2 in HparentIsPDTs0.
        rewrite <-HPDTEqs4s3 in HparentIsPDTs0. rewrite <-HPDTEqs5s4 in HparentIsPDTs0.
        rewrite <-HPDTEqss5 in HparentIsPDTs0.
        specialize(Hdisjoint currentPart pdparent HcurrIsPDTs HparentIsPDTs0 HbeqCurrParent).
        destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
        unfold getMappedBlocks in HnewMappedCurrs. unfold getMappedBlocks in HblockParentMapped.
        apply InFilterPresentInList in HnewMappedCurrs. apply InFilterPresentInList in HblockParentMapped.
        specialize(Hdisjoint idNewSubblock HnewMappedCurrs). congruence.
      }
      destruct (beqAddr blockToShareInCurrPartAddr blockParent) eqn:HbeqBlockBlockParent.
      {
        rewrite HgetBlocksEqss0 in HblockParentMapped; try(apply not_eq_sym in HbeqCurrParent; assumption).
        rewrite <-beqAddrTrue in HbeqBlockBlockParent. subst blockParent.
        assert(Hdisjoint: DisjointKSEntries s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
        specialize(Hdisjoint currentPart pdparent HcurrIsPDTs0 HparentIsPDTs0 HbeqCurrParent).
        destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
        unfold getMappedBlocks in HblockMappedCurrs0. unfold getMappedBlocks in HblockParentMapped.
        apply InFilterPresentInList in HblockMappedCurrs0. apply InFilterPresentInList in HblockParentMapped.
        specialize(Hdisjoint blockToShareInCurrPartAddr HblockMappedCurrs0). congruence.
      }
      assert(HlookupBlockParentEq: lookup blockParent (memory s) beqAddr
                                    = lookup blockParent (memory s0) beqAddr).
      { apply HBElookupEqss0; assumption. }
      assert(HlookupParentSh1Eq: lookup (CPaddr (blockParent + sh1offset)) (memory s) beqAddr
                                  = lookup (CPaddr (blockParent + sh1offset)) (memory s0) beqAddr).
      {
        assert(HwellFormed: wellFormedFstShadowIfBlockEntry s0)
          by (unfold consistency in *; unfold consistency1 in *; intuition).
        specialize(HwellFormed blockParent HblockParentIsBE). apply HSHElookupEqss0; assumption.
      }
      unfold bentryStartAddr in HstartParent. unfold bentryEndAddr in HendParent.
      unfold bentryPFlag in HPFlagParent. rewrite HlookupBlockParentEq in *.
      destruct (beqAddr currentPart child) eqn:HbeqCurrChild.
      + rewrite <-beqAddrTrue in HbeqCurrChild. subst child.
        assert(HblockEquiv: blockInChildHasAtLeastEquivalentBlockInParent s0)
            by (unfold consistency in *; unfold consistency1 in *; intuition).
        specialize(HblockEquiv pdparent currentPart blockToShareInCurrPartAddr blockToCutStartAddr
          blockToCutEndAddr HparentIsPart HchildIsChild HblockMappedCurrs0 HstartBlocks0 HendBlockBiss0
          HPFlagBlocks0).
        destruct HblockEquiv as [blockParentBis [startParentBis [endParentBis (HblockParentBisMapped &
        HstartParentBis & HendParentBis & Hstart & Hend)]]].
        rewrite HgetBlocksEqss0 in HblockParentMapped; try(apply not_eq_sym in HbeqCurrParent; assumption).
        destruct (beqAddr idNewSubblock blockChild) eqn:HbeqNewBlockChild.
        * rewrite <-beqAddrTrue in HbeqNewBlockChild. subst blockChild.
          assert(Heq: blockParentBis = blockParent).
          {
            destruct (beqAddr blockParentBis blockParent) eqn:HbeqBlocks; try(rewrite beqAddrTrue; assumption).
            rewrite <-beqAddrFalse in HbeqBlocks. exfalso.
            assert(HwellFormedBlock: wellFormedBlock s0)
                by (unfold consistency in *; unfold consistency1 in *; intuition).
            assert(HPFlagParentBis: bentryPFlag blockParentBis true s0).
            {
              pose proof (mappedBlockIsBE blockParentBis pdparent s0 HblockParentBisMapped) as Hres.
              destruct Hres as [bentryBis (HlookupBis & Hpresent)]. unfold bentryPFlag. rewrite HlookupBis.
              apply eq_sym. assumption.
            }
            specialize(HwellFormedBlock blockParentBis startParentBis endParentBis HPFlagParentBis HstartParentBis
              HendParentBis). destruct HwellFormedBlock as (HwellFormedBlock & _).
            assert(HwellFormedBlockChild: wellFormedBlock s) by (unfold consistency1 in *; intuition).
            specialize(HwellFormedBlockChild idNewSubblock startChild endChild HPFlagChild HstartChild
              HendChild). destruct HwellFormedBlockChild as (HwellFormedBlockChild & _).
            unfold bentryStartAddr in HstartChild. unfold bentryEndAddr in HendChild. rewrite HlookupNews in *.
            rewrite Hbentry6simpl in HstartChild. rewrite Hbentry6simpl in HendChild. simpl in HstartChild.
            simpl in HendChild. subst startChild. subst endChild.
            assert(HstartChildInBis: In cutAddr (getAllPaddrAux [blockParentBis] s0)).
            {
              simpl. unfold bentryStartAddr in HstartParentBis. unfold bentryEndAddr in HendParentBis.
              destruct (lookup blockParentBis (memory s0) beqAddr); try(simpl; congruence).
              destruct v; try(simpl; congruence). rewrite app_nil_r. rewrite <-HstartParentBis in *.
              rewrite <-HendParentBis in *. unfold StateLib.Paddr.leb in *.
              apply eq_sym in HlebCutStart. apply Compare_dec.leb_iff_conv in HlebCutStart.
              apply eq_sym in HlebEndCut. apply Compare_dec.leb_iff_conv in HlebEndCut.
              unfold bentryEndAddr in *. rewrite HlookupBlocks0 in *. rewrite <-HendBlocks0 in HendBlockBiss0.
              subst blockToCutEndAddr. apply getAllPaddrBlockIncl; lia.
            }
            assert(HnoDupPaddr: noDupUsedPaddrList s0)
                by (unfold consistency in *; unfold consistency2 in *; intuition).
            pose proof (DisjointPaddrInPart pdparent blockParentBis blockParent cutAddr s0 HnoDupPaddr
              HparentIsPDTs0 HblockParentBisMapped HblockParentMapped HbeqBlocks HstartChildInBis) as Hcontra.
            contradict Hcontra. simpl. destruct (lookup blockParent (memory s0) beqAddr); try(simpl; congruence).
            destruct v; try(simpl; congruence). rewrite app_nil_r. rewrite <-HstartParent in *.
            rewrite <-HendParent in *. apply getAllPaddrBlockIncl; lia.
          }
          subst blockParentBis.
          assert(startParentBis = startParent).
          {
            unfold bentryStartAddr in HstartParentBis.
            destruct (lookup blockParent (memory s0) beqAddr); try(exfalso; congruence).
            destruct v; try(exfalso; congruence). rewrite <-HstartParent in HstartParentBis. assumption.
          }
          subst startParentBis.
          assert(endParentBis = endParent).
          {
            unfold bentryEndAddr in HendParentBis.
            destruct (lookup blockParent (memory s0) beqAddr); try(exfalso; congruence).
            destruct v; try(exfalso; congruence). rewrite <-HendParent in HendParentBis. assumption.
          }
          subst endParentBis.
          specialize(Hcons0 currentPart pdparent blockToShareInCurrPartAddr blockToCutStartAddr blockToCutEndAddr
            blockParent startParent endParent HparentIsPart HchildIsChild HblockMappedCurrs0 HstartBlocks0
            HendBlockBiss0 HPFlagBlocks0 HblockParentMapped HstartParent HendParent HPFlagParent Hstart Hend).
          unfold checkChild. unfold sh1entryPDchild. unfold sh1entryInChildLocation. unfold bentryAFlag.
          rewrite HlookupBlockParentEq. rewrite HlookupParentSh1Eq. split. apply Hcons0. split. apply Hcons0.
          destruct Hcons0 as (_ & _ & HchildLoc & HaccIfNotCut). split.
          -- intros blockIDInChild HchildLocs0. rewrite HBEEqss0 in HchildLocs0.
             specialize(HchildLoc blockIDInChild HchildLocs0).
             destruct HchildLoc as (HidInChildNotNull & HchildLoc). split. assumption.
             unfold bentryStartAddr in HstartChild. rewrite HlookupNews in HstartChild.
             rewrite Hbentry6simpl in HstartChild. simpl in HstartChild. subst startChild.
             unfold StateLib.Paddr.leb in HlebCutStart. apply eq_sym in HlebCutStart.
             apply Compare_dec.leb_iff_conv in HlebCutStart. intro Hcontra. exfalso. subst startParent. lia.
          -- intro HboundsWrong. unfold bentryStartAddr in HstartChild. rewrite HlookupNews in HstartChild.
             rewrite Hbentry6simpl in HstartChild. simpl in HstartChild. subst startChild.
             rewrite Hparent in HblockParentMapped. rewrite HlookupChild in HlookupCurrs0.
             injection HlookupCurrs0 as HpdentriesEq. subst p. unfold bentryEndAddr in HendChild.
             rewrite HlookupNews in HendChild. rewrite Hbentry6simpl in HendChild. simpl in HendChild.
             subst endChild. unfold bentryEndAddr in *. rewrite HlookupBlocks0 in *.
             rewrite <-HendBlockBiss0 in HendBlocks0. subst blockEndAddr.
             destruct (beqAddr startParent blockToCutStartAddr) eqn:HbeqStarts.
             ++ rewrite <-beqAddrTrue in HbeqStarts. subst startParent.
                destruct (beqAddr endParent blockToCutEndAddr) eqn:HbeqEnds.
                ** rewrite <-beqAddrTrue in HbeqEnds. subst endParent.
                   specialize(HparentBlockNotAcc blockParent HblockParentMapped HstartParent HendParent).
                   assumption.
                ** apply HaccIfNotCut. right. rewrite beqAddrFalse. assumption.
             ++ apply HaccIfNotCut. left. rewrite beqAddrFalse. assumption.
        * destruct (beqAddr blockToShareInCurrPartAddr blockChild) eqn:HbeqBlockBlockChild.
          -- rewrite <-beqAddrTrue in HbeqBlockBlockChild. subst blockChild.
             assert(Heq: blockParentBis = blockParent).
             {
               destruct (beqAddr blockParentBis blockParent) eqn:HbeqBlocks; try(rewrite beqAddrTrue; assumption).
               rewrite <-beqAddrFalse in HbeqBlocks. exfalso.
               assert(HwellFormedBlock: wellFormedBlock s0)
                   by (unfold consistency in *; unfold consistency1 in *; intuition).
               assert(HPFlagParentBis: bentryPFlag blockParentBis true s0).
               {
                 pose proof (mappedBlockIsBE blockParentBis pdparent s0 HblockParentBisMapped) as Hres.
                 destruct Hres as [bentryBis (HlookupBis & Hpresent)]. unfold bentryPFlag. rewrite HlookupBis.
                 apply eq_sym. assumption.
               }
               specialize(HwellFormedBlock blockParentBis startParentBis endParentBis HPFlagParentBis
                 HstartParentBis HendParentBis). destruct HwellFormedBlock as (HwellFormedBlock & _).
               assert(HwellFormedBlockChild: wellFormedBlock s) by (unfold consistency1 in *; intuition).
               specialize(HwellFormedBlockChild blockToShareInCurrPartAddr startChild endChild HPFlagChild
                 HstartChild HendChild). destruct HwellFormedBlockChild as (HwellFormedBlockChild & _).
               unfold bentryStartAddr in *. unfold bentryEndAddr in *. rewrite HlookupBlocks in *.
               rewrite HbentryShares2 in HstartChild. rewrite HbentryShares2 in HendChild. simpl in HstartChild.
               simpl in HendChild. rewrite HlookupBlocks0 in *. rewrite <-HstartBlocks0 in HstartChild.
               subst startChild. subst endChild.
               assert(HstartChildInBis: In blockToCutStartAddr (getAllPaddrAux [blockParentBis] s0)).
               {
                 simpl. unfold bentryStartAddr in HstartParentBis. unfold bentryEndAddr in HendParentBis.
                 destruct (lookup blockParentBis (memory s0) beqAddr); try(simpl; congruence).
                 destruct v; try(simpl; congruence). rewrite app_nil_r. rewrite <-HstartParentBis in *.
                 rewrite <-HendParentBis in *. unfold StateLib.Paddr.leb in *.
                 apply eq_sym in HlebCutStart. apply Compare_dec.leb_iff_conv in HlebCutStart.
                 apply eq_sym in HlebEndCut. apply Compare_dec.leb_iff_conv in HlebEndCut.
                 unfold bentryEndAddr in *. rewrite <-HendBlocks0 in HendBlockBiss0.
                 subst blockToCutEndAddr. apply getAllPaddrBlockIncl; lia.
               }
               assert(HnoDupPaddr: noDupUsedPaddrList s0)
                   by (unfold consistency in *; unfold consistency2 in *; intuition).
               pose proof (DisjointPaddrInPart pdparent blockParentBis blockParent blockToCutStartAddr s0
                 HnoDupPaddr HparentIsPDTs0 HblockParentBisMapped HblockParentMapped HbeqBlocks HstartChildInBis)
                as Hcontra.
               contradict Hcontra. simpl. destruct (lookup blockParent (memory s0) beqAddr);
                  try(simpl; congruence).
               destruct v; try(simpl; congruence). rewrite app_nil_r. rewrite <-HstartParent in *.
               rewrite <-HendParent in *. apply getAllPaddrBlockIncl; lia.
             }
             subst blockParentBis.
             assert(startParentBis = startParent).
             {
               unfold bentryStartAddr in HstartParentBis.
               destruct (lookup blockParent (memory s0) beqAddr); try(exfalso; congruence).
               destruct v; try(exfalso; congruence). rewrite <-HstartParent in HstartParentBis. assumption.
             }
             subst startParentBis.
             assert(endParentBis = endParent).
             {
               unfold bentryEndAddr in HendParentBis.
               destruct (lookup blockParent (memory s0) beqAddr); try(exfalso; congruence).
               destruct v; try(exfalso; congruence). rewrite <-HendParent in HendParentBis. assumption.
             }
             subst endParentBis.
             specialize(Hcons0 currentPart pdparent blockToShareInCurrPartAddr blockToCutStartAddr
               blockToCutEndAddr blockParent startParent endParent HparentIsPart HchildIsChild HblockMappedCurrs0
               HstartBlocks0 HendBlockBiss0 HPFlagBlocks0 HblockParentMapped HstartParent HendParent HPFlagParent
               Hstart Hend). unfold checkChild. unfold sh1entryPDchild. unfold sh1entryInChildLocation.
             unfold bentryAFlag. rewrite HlookupBlockParentEq. rewrite HlookupParentSh1Eq. split. apply Hcons0.
             split. apply Hcons0. unfold bentryStartAddr in *. rewrite HlookupBlocks0 in *.
             rewrite HlookupBlocks in *. rewrite HbentryShares2 in HstartChild. simpl in HstartChild.
             rewrite <-HstartBlocks0 in HstartChild. subst startChild.
             destruct Hcons0 as (_ & _ & HchildLoc & HaccIfNotCut). split.
             ++ intros blockIDInChild HinChildLoc. apply HchildLoc. unfold sh1entryInChildLocation.
                destruct (lookup (CPaddr (blockParent + sh1offset)) (memory s0) beqAddr); try(congruence).
                destruct v; congruence.
             ++ intro HboundsWrong.
                destruct (beqAddr startParent blockToCutStartAddr) eqn:HbeqStarts.
                ** rewrite <-beqAddrTrue in HbeqStarts. subst startParent.
                   destruct (beqAddr endParent blockToCutEndAddr) eqn:HbeqEnds.
                   --- rewrite <-beqAddrTrue in HbeqEnds. subst endParent. rewrite Hparent in HblockParentMapped.
                       rewrite HlookupChild in HlookupCurrs0. injection HlookupCurrs0 as HpdentriesEq. subst p.
                       specialize(HparentBlockNotAcc blockParent HblockParentMapped HstartParent HendParent).
                       assumption.
                   --- apply HaccIfNotCut. right. rewrite beqAddrFalse. assumption.
                ** apply HaccIfNotCut. left. rewrite beqAddrFalse. assumption.
          -- assert(HlookupBlockChildEq: lookup blockChild (memory s) beqAddr
                                          = lookup blockChild (memory s0) beqAddr).
             { apply HBElookupEqss0; assumption. }
             unfold bentryStartAddr in HstartChild. unfold bentryEndAddr in HendChild.
             unfold bentryPFlag in HPFlagChild. rewrite HlookupBlockChildEq in *.
             rewrite HgetBlocksCurrEqss0 in HblockChildMapped. rewrite <-beqAddrFalse in HbeqNewBlockChild.
             destruct HblockChildMapped as [Hcontra | HblockChildMapped]; try(exfalso; congruence).
             specialize(Hcons0 currentPart pdparent blockChild startChild endChild blockParent startParent
                endParent HparentIsPart HchildIsChild HblockChildMapped HstartChild HendChild HPFlagChild
                HblockParentMapped HstartParent HendParent HPFlagParent HlebStart HlebEnd).
             unfold checkChild. unfold sh1entryPDchild. unfold sh1entryInChildLocation.
             unfold bentryAFlag. rewrite HlookupBlockParentEq. rewrite HlookupParentSh1Eq. split. apply Hcons0.
             split. apply Hcons0. split; try(apply Hcons0). intros blockIDInChild HinChildLoc. apply Hcons0.
             unfold sh1entryInChildLocation.
             destruct (lookup (CPaddr (blockParent + sh1offset)) (memory s0) beqAddr); try(congruence).
             destruct v; congruence.
      + rewrite <-beqAddrFalse in HbeqCurrChild.
        rewrite HgetBlocksEqss0 in HblockParentMapped; try(apply not_eq_sym in HbeqCurrParent; assumption).
        destruct (beqAddr idNewSubblock blockChild) eqn:HbeqNewBlockChild.
        {
          rewrite <-beqAddrTrue in HbeqNewBlockChild. subst blockChild. unfold getMappedBlocks in HnewMappedCurrs.
          unfold getMappedBlocks in HblockChildMapped. apply InFilterPresentInList in HnewMappedCurrs.
          apply InFilterPresentInList in HblockChildMapped.
          assert(Hdisjoint: DisjointKSEntries s) by (unfold consistency1 in *; intuition).
          assert(HchildIsPDT: isPDT child s).
          {
            rewrite HPDTEqss5. rewrite HPDTEqs5s4. rewrite HPDTEqs4s3. rewrite HPDTEqs3s2. rewrite HPDTEqs2s0.
            assumption.
          }
          specialize(Hdisjoint currentPart child HcurrIsPDTs HchildIsPDT HbeqCurrChild).
          destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
          specialize(Hdisjoint idNewSubblock HnewMappedCurrs). congruence.
        }
        assert(HblockMappedCurrs: In blockToShareInCurrPartAddr (getMappedBlocks currentPart s)).
        { apply HgetBlocksCurrEqss0. right. assumption. }
        destruct (beqAddr blockToShareInCurrPartAddr blockChild) eqn:HbeqBlockBlockChild.
        {
          rewrite <-beqAddrTrue in HbeqBlockBlockChild. subst blockChild.
          unfold getMappedBlocks in HblockMappedCurrs. unfold getMappedBlocks in HblockChildMapped.
          apply InFilterPresentInList in HblockMappedCurrs. apply InFilterPresentInList in HblockChildMapped.
          assert(Hdisjoint: DisjointKSEntries s) by (unfold consistency1 in *; intuition).
          assert(HchildIsPDT: isPDT child s).
          {
            rewrite HPDTEqss5. rewrite HPDTEqs5s4. rewrite HPDTEqs4s3. rewrite HPDTEqs3s2. rewrite HPDTEqs2s0.
            assumption.
          }
          specialize(Hdisjoint currentPart child HcurrIsPDTs HchildIsPDT HbeqCurrChild).
          destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
          specialize(Hdisjoint blockToShareInCurrPartAddr HblockMappedCurrs). congruence.
        }
        assert(HlookupBlockChildEq: lookup blockChild (memory s) beqAddr = lookup blockChild (memory s0) beqAddr).
        { apply HBElookupEqss0; assumption. }
        unfold bentryStartAddr in HstartChild. unfold bentryEndAddr in HendChild.
        unfold bentryPFlag in HPFlagChild. rewrite HlookupBlockChildEq in *.
        rewrite HgetBlocksEqss0 in HblockChildMapped; try(apply not_eq_sym); try(assumption).
        specialize(Hcons0 child pdparent blockChild startChild endChild blockParent startParent
           endParent HparentIsPart HchildIsChild HblockChildMapped HstartChild HendChild HPFlagChild
           HblockParentMapped HstartParent HendParent HPFlagParent HlebStart HlebEnd).
        unfold checkChild. unfold sh1entryPDchild. unfold sh1entryInChildLocation.
        unfold bentryAFlag. rewrite HlookupBlockParentEq. rewrite HlookupParentSh1Eq. split. apply Hcons0.
        split. apply Hcons0. split; try(apply Hcons0). intros blockIDInChild HinChildLoc. apply Hcons0.
        unfold sh1entryInChildLocation.
        destruct (lookup (CPaddr (blockParent + sh1offset)) (memory s0) beqAddr); try(congruence).
        destruct v; congruence.
    (* END childsBlocksPropsInParent *)
  }

  (* BEGIN noChildImpliesAddressesNotShared s *)
  assert(Hcons0: noChildImpliesAddressesNotShared s0)
    by (unfold consistency in *; unfold consistency2 in *; intuition).
  intros part pdentryPart block sh1entryaddr HpartIsPart HlookupPart HblockMapped Hsh1 HPDChild child addr
    HchildIsChild HaddrInBlock. rewrite HgetPartsEqss0 in HpartIsPart.
  assert(HpartIsPDTs: isPDT part s) by (unfold isPDT; rewrite HlookupPart; trivial).
  assert(HpartIsPDTs0: isPDT part s0).
  {
    rewrite <-HPDTEqs2s0. rewrite <-HPDTEqs3s2. rewrite <-HPDTEqs4s3. rewrite <-HPDTEqs5s4. rewrite <-HPDTEqss5.
    assumption.
  }
  rewrite HgetChildrenEqss0 in HchildIsChild; try(assumption).
  destruct (beqAddr part currentPart) eqn:HbeqPartCurr.
  - rewrite <-beqAddrTrue in HbeqPartCurr. subst part.
    destruct (beqAddr idNewSubblock block) eqn:HbeqNewBlockBis.
    + rewrite <-beqAddrTrue in HbeqNewBlockBis. subst block.
      assert(HeqTriv: CPaddr (blockToShareInCurrPartAddr + sh1offset)
                      = CPaddr (blockToShareInCurrPartAddr + sh1offset)) by reflexivity.
      destruct HPDChildBlocks0 as [sh1entry [sh1entryaddrBlock (HlookupSh1 & HPDChildBlock & Hsh1Block)]].
      unfold sh1entryAddr in Hsh1Block. rewrite HlookupBlocks0 in Hsh1Block.
      rewrite <-beqAddrTrue in HbeqPDChildNull. subst PDChildAddr. apply HnewInclBlocs0 in HaddrInBlock.
      specialize(Hcons0 currentPart pdentryCurrs0 blockToShareInCurrPartAddr sh1entryaddrBlock HpartIsPart
        HlookupCurrs0 HblockMappedCurrs0 Hsh1Block HPDChildBlock child addr HchildIsChild HaddrInBlock).
      contradict Hcons0. apply HgetPaddrEqss0; try(assumption).
      apply childrenArePDT with currentPart; try(assumption).
      unfold consistency in *; unfold consistency1 in *; intuition.
    + assert(HblockMappeds0: In block (getMappedBlocks currentPart s0)).
      {
        rewrite <-beqAddrFalse in HbeqNewBlockBis. apply HgetBlocksCurrEqss0 in HblockMapped.
        destruct HblockMapped as [Hcontra | Hres]; try(exfalso; congruence). assumption.
      }
      destruct (beqAddr blockToShareInCurrPartAddr block) eqn:HbeqBlockBlockBis.
      * rewrite <-beqAddrTrue in HbeqBlockBlockBis. subst block.
        assert(HeqTriv: CPaddr (blockToShareInCurrPartAddr + sh1offset)
                        = CPaddr (blockToShareInCurrPartAddr + sh1offset)) by reflexivity.
        destruct HPDChildBlocks0 as [sh1entry [sh1entryaddrBlock (HlookupSh1 & HPDChildBlock & Hsh1Block)]].
        unfold sh1entryAddr in Hsh1Block. rewrite HlookupBlocks0 in Hsh1Block.
        rewrite <-beqAddrTrue in HbeqPDChildNull. subst PDChildAddr. apply HblockInclBlocks0 in HaddrInBlock.
        specialize(Hcons0 currentPart pdentryCurrs0 blockToShareInCurrPartAddr sh1entryaddrBlock HpartIsPart
          HlookupCurrs0 HblockMappedCurrs0 Hsh1Block HPDChildBlock child addr HchildIsChild HaddrInBlock).
        contradict Hcons0. apply HgetPaddrEqss0; try(assumption).
        apply childrenArePDT with currentPart; try(assumption).
        unfold consistency in *; unfold consistency1 in *; intuition.
      * assert(HlookupBlockEq: lookup block (memory s) beqAddr = lookup block (memory s0) beqAddr).
        {
          apply HBElookupEqss0; try(assumption). apply mappedBlockIsBE in HblockMappeds0.
          destruct HblockMappeds0 as [bentryBlock (HlookupBlock & _)]. unfold isBE. rewrite HlookupBlock.
          trivial.
        }
        assert(HaddrInBlocks0: In addr (getAllPaddrAux [block] s0)).
        {
          simpl. simpl in HaddrInBlock. rewrite HlookupBlockEq in HaddrInBlock. assumption.
        }
        apply isPDTLookupEq in HpartIsPDTs0. destruct HpartIsPDTs0 as [pdentryParts0 HlookupParts0].
        assert(HPDChilds0: sh1entryPDchild sh1entryaddr nullAddr s0).
        {
          assert(HlookupSh1: lookup sh1entryaddr (memory s) beqAddr = lookup sh1entryaddr (memory s0) beqAddr).
          {
            apply HSHElookupEqss0. rewrite Hsh1.
            assert(HwellFormedSh1: wellFormedFstShadowIfBlockEntry s0)
              by (unfold consistency in *; unfold consistency1 in *; intuition). apply HwellFormedSh1.
            apply mappedBlockIsBE in HblockMappeds0. destruct HblockMappeds0 as [bentryBlock (HlookupBlock & _)].
            unfold isBE. rewrite HlookupBlock. trivial.
          }
          unfold sh1entryPDchild in *. rewrite HlookupSh1 in HPDChild. assumption.
        }
        specialize(Hcons0 currentPart pdentryParts0 block sh1entryaddr HpartIsPart HlookupParts0 HblockMappeds0
            Hsh1 HPDChilds0 child addr HchildIsChild HaddrInBlocks0). contradict Hcons0.
        apply HgetPaddrEqss0; try(assumption).
        apply childrenArePDT with currentPart; try(assumption).
        unfold consistency in *; unfold consistency1 in *; intuition.
  - rewrite <-beqAddrFalse in HbeqPartCurr.
    destruct (beqAddr idNewSubblock block) eqn:HbeqNewBlockBis.
    {
      rewrite <-beqAddrTrue in HbeqNewBlockBis. subst block. unfold getMappedBlocks in *.
      apply InFilterPresentInList in HnewMappedCurrs. apply InFilterPresentInList in HblockMapped.
      assert(Hdisjoint: DisjointKSEntries s) by (unfold consistency1 in *; intuition).
      specialize(Hdisjoint part currentPart HpartIsPDTs HcurrIsPDTs HbeqPartCurr).
      destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
      specialize(Hdisjoint idNewSubblock HblockMapped). congruence.
    }
    destruct (beqAddr blockToShareInCurrPartAddr block) eqn:HbeqBlockBlockBis.
    {
      assert(HblockMappedCurrs: In blockToShareInCurrPartAddr (getMappedBlocks currentPart s)).
      { apply HgetBlocksCurrEqss0. right. assumption. }
      rewrite <-beqAddrTrue in HbeqBlockBlockBis. subst block. unfold getMappedBlocks in *.
      apply InFilterPresentInList in HblockMappedCurrs. apply InFilterPresentInList in HblockMapped.
      assert(Hdisjoint: DisjointKSEntries s) by (unfold consistency1 in *; intuition).
      specialize(Hdisjoint part currentPart HpartIsPDTs HcurrIsPDTs HbeqPartCurr).
      destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
      specialize(Hdisjoint blockToShareInCurrPartAddr HblockMapped). congruence.
    }
    assert(HblockMappeds0: In block (getMappedBlocks part s0)).
    { rewrite <-HgetBlocksEqss0; assumption. }
    assert(HlookupBlockEq: lookup block (memory s) beqAddr = lookup block (memory s0) beqAddr).
    {
      apply HBElookupEqss0; try(assumption). apply mappedBlockIsBE in HblockMappeds0.
      destruct HblockMappeds0 as [bentryBlock (HlookupBlock & _)]. unfold isBE. rewrite HlookupBlock.
      trivial.
    }
    assert(HaddrInBlocks0: In addr (getAllPaddrAux [block] s0)).
    {
      simpl. simpl in HaddrInBlock. rewrite HlookupBlockEq in HaddrInBlock. assumption.
    }
    apply isPDTLookupEq in HpartIsPDTs0. destruct HpartIsPDTs0 as [pdentryParts0 HlookupParts0].
    assert(HPDChilds0: sh1entryPDchild sh1entryaddr nullAddr s0).
    {
      assert(HlookupSh1: lookup sh1entryaddr (memory s) beqAddr = lookup sh1entryaddr (memory s0) beqAddr).
      {
        apply HSHElookupEqss0. rewrite Hsh1.
        assert(HwellFormedSh1: wellFormedFstShadowIfBlockEntry s0)
          by (unfold consistency in *; unfold consistency1 in *; intuition). apply HwellFormedSh1.
        apply mappedBlockIsBE in HblockMappeds0. destruct HblockMappeds0 as [bentryBlock (HlookupBlock & _)].
        unfold isBE. rewrite HlookupBlock. trivial.
      }
      unfold sh1entryPDchild in *. rewrite HlookupSh1 in HPDChild. assumption.
    }
    specialize(Hcons0 part pdentryParts0 block sh1entryaddr HpartIsPart HlookupParts0 HblockMappeds0
        Hsh1 HPDChilds0 child addr HchildIsChild HaddrInBlocks0). contradict Hcons0.
    apply HgetPaddrEqss0; try(assumption).
    apply childrenArePDT with part; try(assumption).
    unfold consistency in *; unfold consistency1 in *; intuition.
  (* END noChildImpliesAddressesNotShared *)

Qed.
