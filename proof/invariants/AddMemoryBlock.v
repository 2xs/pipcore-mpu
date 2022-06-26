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
Proof.StateLib Proof.DependentTypeLemmas Proof.InternalLemmas.

Require Import Invariants checkChildOfCurrPart insertNewEntry.

Require Import Bool List EqNat Lia Compare_dec Coq.Logic.ProofIrrelevance.

Require Import Model.Monad.

Module WP := WeakestPreconditions.

(** * Summary
    This file contains the invariant of [addMemoryBlock].
    We prove that this PIP service preserves the isolation properties as well as
		the consistency properties *)

Lemma addMemoryBlock  (idPDchild idBlockToShare: paddr) (r w e : bool) :
{{fun s => consistency s /\ partitionsIsolation s  /\ kernelDataIsolation s /\ verticalSharing s }}
Services.addMemoryBlock idPDchild idBlockToShare r w e
{{fun _ s  => consistency s /\ partitionsIsolation s  /\ kernelDataIsolation s /\ verticalSharing s }}.
Proof.
unfold addMemoryBlock.
eapply WP.bindRev.
{ (** getCurPartition **)
	eapply WP.weaken. apply Invariants.getCurPartition.
	cbn. intros. split. exact H. intuition.
}
intro currentPart.
eapply WP.bindRev.
{ (** findBlockInKSWithAddr **)
	eapply weaken. eapply findBlockInKSWithAddr.findBlockInKSWithAddr.
	intros. simpl. split. apply H. intuition.
}
intro blockToShareInCurrPartAddr.
eapply WP.bindRev.
{ (** compareAddrToNull **)
	eapply weaken. apply Invariants.compareAddrToNull.
	intros. simpl. apply H.
}
intro addrIsNull.
case_eq addrIsNull.
- (* case_eq addrIsNull = true *)
	intros.
	{ (** ret **)
		eapply WP.weaken. apply WP.ret.
		simpl. intros. intuition.
	}
- (* case_eq addrIsNull = false *)
	intros.
	eapply bindRev.
	{ (** checkRights **)
		eapply weaken. apply Invariants.checkRights.
		intros. simpl. split.
		assert(HBTSNotNull : blockToShareInCurrPartAddr <> nullAddr).
		{ rewrite <- beqAddrFalse in *. intuition. }
		pose (Hconj := conj H0 HBTSNotNull).
		apply Hconj. rewrite <- beqAddrFalse in *. intuition.
		destruct H8. exists x. apply H5.
	}
	intro rcheck.
	case_eq (negb rcheck).
	+ (* case_eq negb rcheck = true *)
		intros.
		{ (** ret **)
			eapply WP.weaken. apply WP.ret.
			simpl. intros. intuition.
		}
	+ (* case_eq negb rcheck = false *)
		intros.
		eapply WP.bindRev.
		{ (** checkChildOfCurrPart **)
			eapply weaken. apply checkChildOfCurrPart.checkChildOfCurrPart.
			intros. simpl. split. apply H1. intuition.
		}
		intro isChildCurrPart.
		case_eq (negb isChildCurrPart).
		* (* case_eq negb isChildCurrPart = true *)
			intros.
			{ (** ret **)
				eapply WP.weaken. apply WP.ret.
				simpl. intros. intuition.
			}
		* (* case_eq negb isChildCurrPart = true *)
			intros.
			eapply WP.bindRev.
			{ (** readBlockStartFromBlockEntryAddr **)
				eapply weaken. apply Invariants.readBlockStartFromBlockEntryAddr.
				intros. simpl. split. apply H2.
				repeat rewrite <- beqAddrFalse in *. (* get rid of NULL conditions since we
				are in this branch *)
				rewrite negb_false_iff in *. (* get rif of trivial cases *)
				intuition.
				(* child has been checked, we know that idPDchild is valid and isBE *)
				destruct H10. (* exists sh1entryaddr ... checkChild ... *)
				destruct H4. (* isChildCurrPart = checkChild ... *)
				destruct H10. (* exists... lookup idPDchild... *)
				unfold isBE. intuition.
				assert(Hlookup : lookup idPDchild (memory s) beqAddr = Some (BE x0)) by intuition.
				rewrite Hlookup; trivial.
			}
			intro globalIdPDChild.
			eapply WP.bindRev.
			{ (** readPDNbFreeSlots **)
				eapply weaken. apply Invariants.readPDNbFreeSlots.
				intros. simpl.
				assert(HPDTGlobalIdPDChild : isPDT globalIdPDChild s).
				{
					(* globalIdPDChild is a PDT because it is the start address of idPDchild
							who is a child *)
					repeat rewrite <- beqAddrFalse in *. rewrite negb_false_iff in *. intuition.
					unfold bentryStartAddr in *.
					destruct H11 as [sh1entryaddr (Hcheckchild & ( idpdchildentry & (HlookupidPDchild & (sh1entry & (Hsh1entryaddr & Hlookupshe1entryaddr)))))].
					assert(HPDTIfPDFlag : PDTIfPDFlag s) by (unfold consistency in * ; intuition).
					unfold PDTIfPDFlag in *.
					unfold entryPDT in *.
					specialize (HPDTIfPDFlag idPDchild sh1entryaddr).
					rewrite HlookupidPDchild in *. subst.
					intuition.
					destruct H4.
					unfold isPDT. destruct H1.
					destruct (lookup (startAddr (blockrange idpdchildentry)) (memory s) beqAddr) eqn:Hlookup ; try(exfalso ; congruence).
					destruct v eqn:Hv ; try (exfalso ; congruence).
					trivial.
				}
				assert(HglobalIdPDChildNotNull : globalIdPDChild <> nullAddr).
				{
					assert(HnullAddrExists : nullAddrExists s)
						by (unfold consistency in * ; intuition).
					unfold nullAddrExists in *.
					unfold isPADDR in *.
					unfold isPDT in *.
					intro HglobalNull.
					rewrite HglobalNull in *.
					destruct (lookup nullAddr (memory s) beqAddr) eqn:Hf ; try(exfalso ; congruence).
					destruct v ; try(exfalso ; congruence).
				}
				pose(Hconj1 := conj H2 HglobalIdPDChildNotNull).
				pose(Hconj2 := conj Hconj1 HPDTGlobalIdPDChild).
				split. apply Hconj2.
				assumption.
			}
			intro nbfreeslots.
			eapply bindRev.
			{ (** zero **)
				eapply weaken. apply Invariants.Index.zero.
				intros. simpl. apply H2.
			}
			intro zero.
			eapply bindRev.
			{ (** MALInternal.Index.leb nbfreeslots zero **)
				eapply weaken. apply Invariants.Index.leb.
				intros. simpl. apply H2.
			}
			intro isFull.
			case_eq (isFull).
			-- (* case_eq isFull = false *)
					intros.
					{ (** ret **)
						eapply weaken. apply WP.ret.
						intros. simpl. apply H3.
					}
			-- (*case_eq isFull = true *)
					intros.
					(* TODO :  remove next when link between nbfreeslots and actual list is done *)
					eapply bindRev.
					{ (** readPDFirstFreeSlotPointer *)
						eapply weaken. apply readPDFirstFreeSlotPointer.
						intros. simpl. split. apply H3.
						intuition.
					}
					intro childfirststructurepointer.
					eapply bindRev.
					{ (** compareAddrToNull **)
						eapply weaken. apply Invariants.compareAddrToNull.
						intros. simpl. apply H3.
					}
					intro slotIsNull.
					case_eq slotIsNull.
					------ (* case_eq slotIsNull = true *)
									intros.
									{ (** ret **)
										eapply WP.weaken. apply WP.ret.
										simpl. intros. intuition.
									}
					------ (* case_eq slotIsNull = false *)
									intros.
									eapply bindRev.
									{ (** readBlockAccessibleFromBlockEntryAddr *)
										eapply weaken. apply readBlockAccessibleFromBlockEntryAddr.
										intros. simpl. split. apply H4.
										repeat rewrite beqAddrFalse in *. rewrite negb_false_iff in *. subst.
										assert(HBE : exists entry : BlockEntry, lookup blockToShareInCurrPartAddr (memory s) beqAddr =
									 								Some (BE entry)) by intuition.
										destruct HBE as [blocktoshareentry HLookupblocktoshare].
										intuition ; (unfold isBE ; rewrite HLookupblocktoshare ; trivial).
									}
									intro addrIsAccessible.
									case_eq (negb addrIsAccessible).
									++ (*case_eq negb addrIsAccessible = true *)
											intros. simpl.
											{ (** ret **)
												eapply weaken. apply WP.ret.
												intros. simpl. intuition.
											}
									++ (*case_eq negb addrIsAccessible = false *)
											intros.
											eapply bindRev.
											{ (** readBlockPresentFromBlockEntryAddr **)
												eapply weaken. apply readBlockPresentFromBlockEntryAddr.
												intros. simpl. split. apply H5.
												repeat rewrite <- beqAddrFalse in *.
												unfold isBE. intuition.
												assert(HBE : exists entry : BlockEntry, lookup blockToShareInCurrPartAddr (memory s) beqAddr =
									 								Some (BE entry)) by intuition.
												destruct HBE as [blocktoshareentry HLookupblocktoshare].
												rewrite HLookupblocktoshare. trivial.
											}
											intro addrIsPresent.
											case_eq (negb addrIsPresent).
											** (*case_eq negb addrIsPresent = true *)
												intros. simpl.
												{ (** ret **)
													eapply weaken. apply WP.ret.
													intros. simpl. intuition.
												}
											** (*case_eq negb addrIsPresent = false *)
													intros.
													eapply bindRev.
												{	(** readPDVidt **)
													eapply weaken. apply readPDVidt.
													intros. simpl. split. apply H6.
													intuition.
												}
												intro vidtBlockGlobalId.
												destruct (beqAddr vidtBlockGlobalId blockToShareInCurrPartAddr) eqn:beqBToShareVIDT.
												--- (* vidtBlockGlobalId = blockToShareInCurrPartAddr *)
														intros. simpl.
														{ (** ret **)
															eapply weaken. apply WP.ret.
															intros. simpl. intuition.
														}
												--- (* vidtBlockGlobalId <> blockToShareInCurrPartAddr *)
														eapply bindRev.
														{	(** readBlockStartFromBlockEntryAddr **)
															eapply weaken. apply readBlockStartFromBlockEntryAddr.
															intros. simpl. split. apply H6.
															repeat rewrite <- beqAddrFalse in *.
															unfold isBE. intuition.
															assert(HblockToShare : exists entry : BlockEntry,
																	lookup blockToShareInCurrPartAddr (memory s) beqAddr = Some (BE entry) /\
																	blockToShareInCurrPartAddr = idBlockToShare)
																by intuition.
															destruct HblockToShare as [blocktoshareentry (Hlookupblocktoshare & HblocktoshqreEq)].
															subst. rewrite Hlookupblocktoshare. trivial.
														}
														intro blockstart.
														eapply bindRev.
														{	(** readBlockEndFromBlockEntryAddr **)
															eapply weaken. apply readBlockEndFromBlockEntryAddr.
															intros. simpl. split. apply H6.
															repeat rewrite <- beqAddrFalse in *.
															unfold isBE. intuition.
															assert(HblockToShare : exists entry : BlockEntry,
																	lookup blockToShareInCurrPartAddr (memory s) beqAddr = Some (BE entry) /\
																	blockToShareInCurrPartAddr = idBlockToShare)
																by intuition.
															destruct HblockToShare as [blocktoshareentry (Hlookupblocktoshare & HblocktoshqreEq)].
															subst. rewrite Hlookupblocktoshare. trivial.
														}
														intro blockend.

(* Start of structure modifications *)
eapply bindRev.
{ eapply weaken. apply insertNewEntry.insertNewEntry.
	intros. simpl.
	split. intuition. split. intuition. split. intuition.
	assert(HPDTGlobalIdPDChild : isPDT globalIdPDChild s) by intuition.
	apply isPDTLookupEq in HPDTGlobalIdPDChild.
	assert(HnfbfreeslotsNotZero : nbfreeslots > 0).
	{
		unfold StateLib.Index.leb in *.
		assert(Hnbfreeslots : PeanoNat.Nat.leb nbfreeslots zero = false) by intuition.
		apply PeanoNat.Nat.leb_gt. assert (Hzero : zero = CIndex 0) by intuition.
		subst. simpl in Hnbfreeslots. intuition.
	}
	split. intuition.
	split. intuition.
	(* TODO : to remove once NbFreeSlotsISNbFreeSlotsInList is proven *)
	split.
	{ unfold pdentryFirstFreeSlot.
		destruct HPDTGlobalIdPDChild as [globalpdentry Hlookupglobal].
		unfold pdentryFirstFreeSlot in *.
		rewrite Hlookupglobal in *.
		exists childfirststructurepointer.
		rewrite <- beqAddrFalse in *.
		intuition.
		rewrite <- beqAddrFalse in *. intuition.
	}
	apply H6.
}
intro blockToShareChildEntryAddr. simpl.
eapply bindRev.
{ (** MAL.writeSh1PDChildFromBlockEntryAddr **)
	eapply weaken. apply writeSh1PDChildFromBlockEntryAddr.
	intros. simpl.
	assert(HBEbts : isBE blockToShareInCurrPartAddr s).
	{ destruct H6 as [s0 Hprops].
		destruct Hprops as [Hprops0 (Hcons & Hprops)].
		destruct Hprops as [pdentry (pdentry0 & (pdentry1
												& (bentry & (bentry0 & (bentry1 & (bentry2 & (bentry3 & (bentry4 & (bentry5 & (bentry6
												& (sceaddr & (scentry
												& (newBlockEntryAddr & (newFirstFreeSlotAddr
												& (predCurrentNbFreeSlots & Hprops)))))))))))))))].
		assert(beqbtsnew : newBlockEntryAddr <> blockToShareInCurrPartAddr).
		{
			(* at s0, newBlockEntryAddr is a free slot, which is not the case of
					blockToShareInCurrPartAddr *)
			assert(HFirstFreeSlotPointerIsBEAndFreeSlot : FirstFreeSlotPointerIsBEAndFreeSlot s0)
					by (unfold consistency in * ; intuition).
			unfold FirstFreeSlotPointerIsBEAndFreeSlot in *.
			assert(HPDTchilds0 : isPDT globalIdPDChild s0) by intuition.
			apply isPDTLookupEq in HPDTchilds0.
			destruct HPDTchilds0 as [childpdentry Hlookupchilds0].
			specialize(HFirstFreeSlotPointerIsBEAndFreeSlot globalIdPDChild childpdentry Hlookupchilds0).
			assert(HfirstfreeNotNull : firstfreeslot childpdentry <> nullAddr).
			{
				assert(Hfirstfreechilds0 : pdentryFirstFreeSlot globalIdPDChild childfirststructurepointer s0 /\
               beqAddr nullAddr childfirststructurepointer = false) by intuition.
				unfold pdentryFirstFreeSlot in *. rewrite Hlookupchilds0 in *.
				rewrite <- beqAddrFalse in *.
				destruct Hfirstfreechilds0 as [HfirstfreeEq HfirstFreeNotNull].
				subst childfirststructurepointer. congruence.
			}
			specialize (HFirstFreeSlotPointerIsBEAndFreeSlot HfirstfreeNotNull).
			assert(HnewBEq : firstfreeslot childpdentry = newBlockEntryAddr).
			{ unfold pdentryFirstFreeSlot in *. rewrite Hlookupchilds0 in *. intuition. }
				rewrite HnewBEq in *.
				intro HBTSnewBEq. (* newB is a free slot, so its present flag is false
															blockToShareInCurrPartAddr is not a free slot,
															so the equality is a constradiction*)
				subst blockToShareInCurrPartAddr.
				assert(HwellFormedsh1newBs0 : wellFormedFstShadowIfBlockEntry s0)
					by (unfold consistency in * ; intuition).
				unfold wellFormedFstShadowIfBlockEntry in *.
				assert(HwellFormedSCnewBs0 : wellFormedShadowCutIfBlockEntry s0)
					by (unfold consistency in * ; intuition).
				unfold wellFormedShadowCutIfBlockEntry in *.
				assert(HBEs0 : isBE newBlockEntryAddr s0) by intuition.
				specialize (HwellFormedsh1newBs0 newBlockEntryAddr HBEs0).
				specialize (HwellFormedSCnewBs0 newBlockEntryAddr HBEs0).
				unfold isBE in *. unfold isSHE in *. unfold isSCE in *.
				unfold isFreeSlot in *.
				unfold bentryPFlag in *.
				destruct (lookup newBlockEntryAddr (memory s0) beqAddr) eqn:Hbe ; try(exfalso ; congruence).
				destruct v ; try(exfalso ; congruence).
				destruct (lookup (CPaddr (newBlockEntryAddr + sh1offset)) (memory s0) beqAddr) eqn:Hsh1 ; try(exfalso ; congruence).
				destruct v ; try(exfalso ; congruence).
				destruct HwellFormedSCnewBs0 as [scentryaddr (HSCEs0 & HscentryEq)].
				subst scentryaddr.
				destruct (lookup (CPaddr (newBlockEntryAddr + scoffset))  (memory s0) beqAddr) eqn:Hsce ; try(exfalso ; congruence).
				destruct v ; try(exfalso ; congruence).
				intuition. subst addrIsPresent.
				assert(Hfalse : negb (present b) = true).
				{ assert(Htrue : present b = false) by intuition.
					rewrite Htrue. trivial.
				}
				congruence.
			}
			assert(HBEs0 : isBE blockToShareInCurrPartAddr s0).
			{
				assert(Hlookups0 : exists entry : BlockEntry,
                    lookup blockToShareInCurrPartAddr (memory s0) beqAddr = Some (BE entry))
					by intuition.
				destruct Hlookups0 as [btsentry Hlookups0].
				unfold isBE. rewrite Hlookups0. trivial.
			}
			assert(HidpdchildbtsNotEq : globalIdPDChild <> blockToShareInCurrPartAddr).
			{
				intro Heqfalse. rewrite Heqfalse in *.
				unfold isPDT in *.
				unfold isBE in *.
				destruct (lookup blockToShareInCurrPartAddr (memory s0) beqAddr) eqn:Hlookup ; try(intuition ; exfalso ; congruence).
				destruct v ; try(intuition ; exfalso ; congruence).
			}

			destruct Hprops as [Hs Hprops].
			assert(HlookupBTSs : lookup blockToShareInCurrPartAddr (memory s) beqAddr =
													lookup blockToShareInCurrPartAddr (memory s0) beqAddr).
			{
				rewrite Hs.
				cbn. rewrite Proof.InternalLemmas.beqAddrTrue.
				destruct (beqAddr sceaddr blockToShareInCurrPartAddr) eqn:beqscebts ; try(exfalso ; congruence).
				- (* sceaddr = blockToShareInCurrPartAddr *)
					rewrite <- DependentTypeLemmas.beqAddrTrue in beqscebts.
					rewrite <- beqscebts in *.
					apply eq_sym.
					assert(HSCEs0 : isSCE sceaddr s0) by intuition.
					unfold isSCE in *.
					unfold isBE in *.
					destruct (lookup sceaddr (memory s0) beqAddr) eqn:Hf ; try(exfalso ; congruence).
					destruct v ; try(exfalso ; congruence).
				- (* sceaddr <> blockToShareInCurrPartAddr *)
					cbn.
					assert(HnewBsceNotEq : beqAddr newBlockEntryAddr sceaddr = false)
						by (rewrite <- beqAddrFalse in *  ; intuition).
					rewrite HnewBsceNotEq. (*newBlock <> sce *)
					cbn.
					destruct (beqAddr newBlockEntryAddr blockToShareInCurrPartAddr) eqn:Hf ; try(exfalso ; congruence).
					rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
					rewrite <- beqAddrFalse in *.
					repeat rewrite removeDupIdentity ; intuition.
					destruct (beqAddr globalIdPDChild newBlockEntryAddr) eqn:Hfg ; try(exfalso ; congruence).
					rewrite <- DependentTypeLemmas.beqAddrTrue in Hfg. congruence.
					cbn.
					destruct (beqAddr globalIdPDChild blockToShareInCurrPartAddr) eqn:Hfff ; try(exfalso ; congruence).
					rewrite <- DependentTypeLemmas.beqAddrTrue in Hfff. congruence.
					rewrite beqAddrTrue.
					rewrite <- beqAddrFalse in *.
					repeat rewrite removeDupIdentity ; intuition.
			}
			apply isBELookupEq in HBEs0. destruct HBEs0 as [btsentry0 Hlookups0].
			unfold isBE. rewrite HlookupBTSs. rewrite Hlookups0. trivial.
	}
	destruct H6 as [s0 Hprops].
	assert(HwellFormedFstShadowIfBlockEntry : wellFormedFstShadowIfBlockEntry s)
			by (unfold consistency in * ; intuition).
	specialize (HwellFormedFstShadowIfBlockEntry blockToShareInCurrPartAddr HBEbts).
	apply isSHELookupEq in HwellFormedFstShadowIfBlockEntry as [sh1entrybts HSHEbtss].
	exists sh1entrybts. split. intuition.
	assert(Hcons_conj : wellFormedFstShadowIfBlockEntry s
							/\ KernelStructureStartFromBlockEntryAddrIsKS s)
		by (unfold consistency in * ; intuition).
	destruct Hprops as [Hprops0 (Hcons & Hprops)].
		instantiate (1:= fun _ s =>
exists s0,
	(* s0 *)
	(partitionsIsolation s0 /\
                           kernelDataIsolation s0 /\
                           verticalSharing s0 /\ consistency s0 /\
                          consistency s0 /\
                          isPDT currentPart s0 /\
                          currentPart = currentPartition s0 /\
                         (blockToShareInCurrPartAddr = nullAddr \/
                          (exists entry : BlockEntry,
                             lookup blockToShareInCurrPartAddr
                               (memory s0) beqAddr =
                             Some (BE entry) /\
                             blockToShareInCurrPartAddr = idBlockToShare)) /\
                        beqAddr nullAddr blockToShareInCurrPartAddr =
                        false /\
                       (exists entry : BlockEntry,
                          lookup blockToShareInCurrPartAddr
                            (memory s0) beqAddr =
                          Some (BE entry)) /\
                      (isChildCurrPart = true ->
                       exists sh1entryaddr : paddr,
                         isChildCurrPart =
                         checkChild idPDchild s0 sh1entryaddr /\
                         (exists entry : BlockEntry,
                            lookup idPDchild (memory s0) beqAddr =
                            Some (BE entry) /\
                            (exists sh1entry : Sh1Entry,
                               sh1entryAddr idPDchild sh1entryaddr s0 /\
                               lookup sh1entryaddr (memory s0) beqAddr =
                               Some (SHE sh1entry)))) /\
                     bentryStartAddr idPDchild globalIdPDChild s0 /\
                    isPDT globalIdPDChild s0 /\
                   pdentryNbFreeSlots globalIdPDChild nbfreeslots s0 /\
                  zero = CIndex 0 /\
                 false = StateLib.Index.leb nbfreeslots zero /\
                pdentryFirstFreeSlot globalIdPDChild
                  childfirststructurepointer s0 /\
               beqAddr nullAddr childfirststructurepointer = false /\
              bentryAFlag blockToShareInCurrPartAddr addrIsAccessible s0 /\
             bentryPFlag blockToShareInCurrPartAddr addrIsPresent s0 /\
            pdentryVidt globalIdPDChild vidtBlockGlobalId s0 /\
           bentryStartAddr blockToShareInCurrPartAddr blockstart s0 /\
          bentryEndAddr blockToShareInCurrPartAddr blockend s0)

/\ (exists pdentry pdentry0 pdentry1: PDTable,
		exists bentry bentry0 bentry1 bentry2 bentry3 bentry4 bentry5 bentry6: BlockEntry,
		exists sceaddr : paddr, exists scentry : SCEntry,
		exists newBlockEntryAddr newFirstFreeSlotAddr : paddr,
		exists predCurrentNbFreeSlots : index,
		exists sh1eaddr : paddr, exists sh1entry sh1entry0 : Sh1Entry,

  s = {|
     currentPartition := currentPartition s0;
     memory := add sh1eaddr
                     (SHE
                        {|	PDchild := globalIdPDChild;
                        		PDflag := PDflag sh1entry;
                        		inChildLocation := inChildLocation sh1entry |})
							(add sceaddr
									(SCE {| origin := blockstart; next := next scentry |})
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
                    (CBlockEntry (read bentry2) (write bentry2) (exec bentry2) true
                       (accessible bentry2) (blockindex bentry2) (blockrange bentry2)))
							(add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry1) (write bentry1) (exec bentry1)
                       (present bentry1) true (blockindex bentry1) (blockrange bentry1)))
							(add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry0) (write bentry0) (exec bentry0)
                       (present bentry0) (accessible bentry0) (blockindex bentry0)
                       (CBlock (startAddr (blockrange bentry0)) blockend)))
							(add newBlockEntryAddr
                     (BE
                        (CBlockEntry (read bentry) (write bentry)
                           (exec bentry) (present bentry) (accessible bentry)
                           (blockindex bentry)
                           (CBlock blockstart (endAddr (blockrange bentry)))))
								(add globalIdPDChild
                 (PDT
                    {|
                    structure := structure pdentry0;
                    firstfreeslot := firstfreeslot pdentry0;
                    nbfreeslots := predCurrentNbFreeSlots;
                    nbprepare := nbprepare pdentry0;
                    parent := parent pdentry0;
                    MPU := MPU pdentry0;
										vidtBlock := vidtBlock pdentry0 |})
								(add globalIdPDChild
                 (PDT
                    {|
                    structure := structure pdentry;
                    firstfreeslot := newFirstFreeSlotAddr;
                    nbfreeslots := ADT.nbfreeslots pdentry;
                    nbprepare := nbprepare pdentry;
                    parent := parent pdentry;
                    MPU := MPU pdentry;
										vidtBlock := vidtBlock pdentry |}) (memory s0) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr |}
/\ lookup sh1eaddr (memory s0) beqAddr = Some (SHE sh1entry)
/\ lookup sh1eaddr (memory s) beqAddr = Some (SHE sh1entry0) /\
sh1entry0 = {| PDchild := globalIdPDChild;
             	PDflag := PDflag sh1entry;
             	inChildLocation := inChildLocation sh1entry |}
/\ newBlockEntryAddr = blockToShareChildEntryAddr
/\ lookup newBlockEntryAddr (memory s0) beqAddr = Some (BE bentry)
/\ lookup newBlockEntryAddr (memory s) beqAddr = Some (BE bentry6)
/\
bentry6 = (CBlockEntry (read bentry5) (write bentry5) e (present bentry5)
                       (accessible bentry5) (blockindex bentry5) (blockrange bentry5))
/\
bentry5 = (CBlockEntry (read bentry4) w (exec bentry4) (present bentry4)
                       (accessible bentry4) (blockindex bentry4) (blockrange bentry4))
/\
bentry4 = (CBlockEntry r (write bentry3) (exec bentry3) (present bentry3)
                       (accessible bentry3) (blockindex bentry3) (blockrange bentry3))
/\
bentry3 = (CBlockEntry (read bentry2) (write bentry2) (exec bentry2) true
                       (accessible bentry2) (blockindex bentry2) (blockrange bentry2))
/\
bentry2 = (CBlockEntry (read bentry1) (write bentry1) (exec bentry1)
                       (present bentry1) true (blockindex bentry1) (blockrange bentry1))
/\
bentry1 = (CBlockEntry (read bentry0) (write bentry0) (exec bentry0)
                       (present bentry0) (accessible bentry0) (blockindex bentry0)
                       (CBlock (startAddr (blockrange bentry0)) blockend))
/\
bentry0 = (CBlockEntry (read bentry) (write bentry)
                           (exec bentry) (present bentry) (accessible bentry)
                           (blockindex bentry)
                           (CBlock blockstart (endAddr (blockrange bentry))))
/\ sceaddr = (CPaddr (newBlockEntryAddr + scoffset))
/\ lookup globalIdPDChild (memory s0) beqAddr = Some (PDT pdentry)
/\ lookup globalIdPDChild (memory s) beqAddr = Some (PDT pdentry1) /\
pdentry1 = {|     structure := structure pdentry0;
                    firstfreeslot := firstfreeslot pdentry0;
                    nbfreeslots := predCurrentNbFreeSlots;
                    nbprepare := nbprepare pdentry0;
                    parent := parent pdentry0;
                    MPU := MPU pdentry0;
										vidtBlock := vidtBlock pdentry0 |} /\
pdentry0 = {|    structure := structure pdentry;
                    firstfreeslot := newFirstFreeSlotAddr;
                    nbfreeslots := ADT.nbfreeslots pdentry;
                    nbprepare := nbprepare pdentry;
                    parent := parent pdentry;
                    MPU := MPU pdentry;
										vidtBlock := vidtBlock pdentry|}
	(* propagate new properties (copied from last step) *)
	/\ pdentryNbFreeSlots globalIdPDChild predCurrentNbFreeSlots s
	/\ StateLib.Index.pred nbfreeslots = Some predCurrentNbFreeSlots
	/\ blockindex bentry6 = blockindex bentry5
	/\ blockindex bentry5 = blockindex bentry4
	/\ blockindex bentry4 = blockindex bentry3
	/\ blockindex bentry3 = blockindex bentry2
	/\ blockindex bentry2 = blockindex bentry1
	/\ blockindex bentry1 = blockindex bentry0
	/\ blockindex bentry0 = blockindex bentry
	/\ blockindex bentry6 = blockindex bentry
	/\ isPDT globalIdPDChild s0
	/\ isPDT globalIdPDChild s
	/\ isBE newBlockEntryAddr s0
	/\ isBE newBlockEntryAddr s
	/\ isBE blockToShareInCurrPartAddr s0
	/\ isSCE sceaddr s0
	/\ isSCE sceaddr s
	/\ isSHE sh1eaddr s0
	/\ isSHE sh1eaddr s
	/\ sceaddr = CPaddr (newBlockEntryAddr + scoffset)
	/\ sh1eaddr = CPaddr (blockToShareInCurrPartAddr + sh1offset)
	/\ firstfreeslot pdentry1 = newFirstFreeSlotAddr
	/\ newBlockEntryAddr = (firstfreeslot pdentry)
	/\ newBlockEntryAddr <> blockToShareInCurrPartAddr
	/\ newFirstFreeSlotAddr <> globalIdPDChild
	/\ globalIdPDChild <> newBlockEntryAddr
	/\ globalIdPDChild <> blockToShareInCurrPartAddr
	/\ newFirstFreeSlotAddr <> newBlockEntryAddr
	/\ newFirstFreeSlotAddr <> sh1eaddr
	/\ sh1eaddr <> sceaddr
	/\ sh1eaddr <> newBlockEntryAddr
	/\ sh1eaddr <> globalIdPDChild
	/\ sh1eaddr <> blockToShareInCurrPartAddr
	/\ sceaddr <> newBlockEntryAddr
	/\ sceaddr <> globalIdPDChild
	/\ sceaddr <> newFirstFreeSlotAddr
	/\ sceaddr <> blockToShareInCurrPartAddr
	(* pdinsertion's new free slots list and relation with list at s0 *)
	/\ (exists (optionfreeslotslist : list optionPaddr) (s2 : state)
					(n0 n1 n2 : nat) (nbleft : index),
			nbleft = CIndex (nbfreeslots - 1) /\
			nbleft < maxIdx /\
			s =
			{|
				currentPartition := currentPartition s0;
				memory :=
					add sh1eaddr
                     (SHE
                        {|	PDchild := globalIdPDChild;
                        		PDflag := PDflag sh1entry;
                        		inChildLocation := inChildLocation sh1entry |})
						(memory s2) beqAddr
			|} /\
			optionfreeslotslist = getFreeSlotsListRec n1 newFirstFreeSlotAddr s2 nbleft /\
			getFreeSlotsListRec n2 newFirstFreeSlotAddr s nbleft = optionfreeslotslist /\
			optionfreeslotslist = getFreeSlotsListRec n0 newFirstFreeSlotAddr s0 nbleft /\
			n0 <= n1 /\
			nbleft < n0 /\
			n1 <= n2 /\
			nbleft < n2 /\
			n2 <= maxIdx + 1 /\
			(wellFormedFreeSlotsList optionfreeslotslist = False -> False) /\
			NoDup (filterOption optionfreeslotslist) /\
			(In newBlockEntryAddr (filterOption optionfreeslotslist) -> False))
		/\ lookup blockToShareInCurrPartAddr (memory s) beqAddr =
						lookup blockToShareInCurrPartAddr (memory s0) beqAddr

(* intermediate steps *)
/\ (exists s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11,
s1 = {|
     currentPartition := currentPartition s0;
     memory := add globalIdPDChild
                (PDT
                   {|
                     structure := structure pdentry;
                     firstfreeslot := newFirstFreeSlotAddr;
                     nbfreeslots := ADT.nbfreeslots pdentry;
                     nbprepare := nbprepare pdentry;
                     parent := parent pdentry;
                     MPU := MPU pdentry;
                     vidtBlock := vidtBlock pdentry
                   |}) (memory s0) beqAddr |}
/\ s2 = {|
     currentPartition := currentPartition s1;
     memory := add globalIdPDChild
		           (PDT
		              {|
		                structure := structure pdentry0;
		                firstfreeslot := firstfreeslot pdentry0;
		                nbfreeslots := predCurrentNbFreeSlots;
		                nbprepare := nbprepare pdentry0;
		                parent := parent pdentry0;
		                MPU := MPU pdentry0;
		                vidtBlock := vidtBlock pdentry0
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
	                  (CBlock blockstart (endAddr (blockrange bentry))))
                 ) (memory s2) beqAddr |}
/\ s4 = {|
     currentPartition := currentPartition s3;
     memory := add newBlockEntryAddr
               (BE
                  (CBlockEntry (read bentry0)
                     (write bentry0) (exec bentry0)
                     (present bentry0) (accessible bentry0)
                     (blockindex bentry0)
                     (CBlock (startAddr (blockrange bentry0)) blockend))
                 ) (memory s3) beqAddr |}
/\ s5 = {|
     currentPartition := currentPartition s4;
     memory := add newBlockEntryAddr
              (BE
                 (CBlockEntry (read bentry1)
                    (write bentry1) (exec bentry1)
                    (present bentry1) true (blockindex bentry1)
                    (blockrange bentry1))
                 ) (memory s4) beqAddr |}
/\ s6 = {|
     currentPartition := currentPartition s5;
     memory := add newBlockEntryAddr
               (BE
                  (CBlockEntry (read bentry2) (write bentry2)
                     (exec bentry2) true (accessible bentry2)
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
								(SCE {| origin := blockstart; next := next scentry |}
                 ) (memory s9) beqAddr |}
/\ s11 = {|
     currentPartition := currentPartition s10;
     memory := add sh1eaddr
        (SHE
           {|
             PDchild := globalIdPDChild;
             PDflag := PDflag sh1entry;
             inChildLocation := inChildLocation sh1entry
           |}) (memory s10) beqAddr |}
(* by setting s10 as the new base, no need to get down to s0 anymore
		since we have already proven all consistency properties for s10 *)
/\ consistency s10
/\ isPDT globalIdPDChild s10
/\ isSCE sceaddr s10
/\ isSHE sh1eaddr s10
/\ isBE newBlockEntryAddr s10
/\ isSHE sh1eaddr s10 = isSHE sh1eaddr s0
))).
intros. simpl.  set (s' := {|
      currentPartition :=  _|}).
			destruct Hprops as [pdentry (pdentry0 & (pdentry1
												& (bentry & (bentry0 & (bentry1 & (bentry2 & (bentry3 & (bentry4 & (bentry5 & (bentry6
												& (sceaddr & (scentry
												& (newBlockEntryAddr & (newFirstFreeSlotAddr
												& (predCurrentNbFreeSlots & (Hs & Hprops))))))))))))))))].
			intuition. subst blockToShareChildEntryAddr.
			exists s0. intuition.
			exists pdentry. exists pdentry0. exists pdentry1.
			exists bentry. exists bentry0. exists bentry1. exists bentry2. exists bentry3.
			exists bentry4. exists bentry5. exists bentry6. exists sceaddr. exists scentry.
			exists newBlockEntryAddr. exists newFirstFreeSlotAddr. exists predCurrentNbFreeSlots.
			exists (CPaddr (blockToShareInCurrPartAddr + sh1offset)).
			assert(HSHEbts0 : isSHE (CPaddr (blockToShareInCurrPartAddr + sh1offset)) s0).
			{
				assert(HwellFormedSh1s0 : wellFormedFstShadowIfBlockEntry s0)
				by (unfold consistency in * ; intuition).
				assert(HBEbtss0 : isBE blockToShareInCurrPartAddr s0).
				{
					assert(Hlookups0 : exists entry : BlockEntry,
      													lookup blockToShareInCurrPartAddr (memory s0) beqAddr = Some (BE entry))
						by intuition.
					destruct Hlookups0 as [btsentry Hlookups0].
					unfold isBE. rewrite Hlookups0. trivial.
				}
				specialize(HwellFormedSh1s0 blockToShareInCurrPartAddr HBEbtss0).
				assumption.
			}
			apply isSHELookupEq in HSHEbts0. destruct HSHEbts0 as [sh1entry Hsh1entry].
			exists sh1entry.
			assert(beqsh1pdchild : beqAddr (CPaddr (blockToShareInCurrPartAddr + sh1offset)) globalIdPDChild = false).
			{
				rewrite <- beqAddrFalse.
				intro Hsh1pdchildEq. rewrite Hsh1pdchildEq in *.
				unfold isPDT in *. unfold isSHE in *.
				destruct(lookup globalIdPDChild (memory s0) beqAddr) eqn:Hf ; try(exfalso ; congruence).
			}
			assert(beqsh1newB : beqAddr (CPaddr (blockToShareInCurrPartAddr + sh1offset)) newBlockEntryAddr = false).
			{
				rewrite <- beqAddrFalse.
				intro Hsh1newBEq. rewrite Hsh1newBEq in *.
				unfold isBE in *. unfold isSHE in *.
				destruct(lookup globalIdPDChild (memory s0) beqAddr) eqn:Hf ; try(exfalso ; congruence).
			}
			assert(beqsh1sce : beqAddr (CPaddr (blockToShareInCurrPartAddr + sh1offset)) sceaddr = false).
			{
				rewrite <- beqAddrFalse.
				intro Hsh1sceEq. rewrite Hsh1sceEq in *.
				unfold isSCE in *. unfold isSHE in *.
				destruct(lookup sceaddr (memory s0) beqAddr) eqn:Hf ; try(exfalso ; congruence).
				destruct v ; try(exfalso ; congruence).
			}
			assert(Hlookupsh1btseq : lookup (CPaddr (blockToShareInCurrPartAddr + sh1offset)) (memory s) beqAddr =
						lookup (CPaddr (blockToShareInCurrPartAddr + sh1offset)) (memory s0) beqAddr).
			{
				rewrite Hs.
				cbn. rewrite beqAddrTrue.
				rewrite beqAddrSym in beqsh1sce.
				rewrite beqsh1sce.
				assert(HnewBsce : beqAddr newBlockEntryAddr sceaddr = false)
					by (rewrite <- beqAddrFalse ; intuition).
				rewrite HnewBsce.
				cbn.
				assert(HnewBsh1bts : beqAddr newBlockEntryAddr (CPaddr (blockToShareInCurrPartAddr + sh1offset)) = false)
					by (rewrite <- beqAddrFalse in * ; intuition).
				rewrite HnewBsh1bts.
				rewrite <- beqAddrFalse in *.
				repeat rewrite removeDupIdentity ; intuition.
				destruct (beqAddr globalIdPDChild newBlockEntryAddr) eqn:Hf ; try (exfalso ; congruence).
				rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
				cbn.
				assert(Hpdchildsh1bts : beqAddr globalIdPDChild (CPaddr (blockToShareInCurrPartAddr + sh1offset)) = false)
					by (rewrite <- beqAddrFalse in * ; intuition).
				rewrite Hpdchildsh1bts.
				rewrite beqAddrTrue.
				rewrite <- beqAddrFalse in *.
				repeat rewrite removeDupIdentity ; intuition.
			}
			rewrite Hlookupsh1btseq in *.
			assert(HBEs0 : isBE blockToShareInCurrPartAddr s0).
			{
				assert(Hlookups0 : exists entry : BlockEntry,
		                lookup blockToShareInCurrPartAddr (memory s0) beqAddr = Some (BE entry))
					by intuition.
				destruct Hlookups0 as [btsentry Hlookups0].
				unfold isBE. rewrite Hlookups0. trivial.
			}
			assert(HidpdchildbtsNotEq : globalIdPDChild <> blockToShareInCurrPartAddr).
			{
				intro Heqfalse. rewrite Heqfalse in *.
				unfold isPDT in *.
				unfold isBE in *.
				destruct (lookup blockToShareInCurrPartAddr (memory s0) beqAddr) eqn:Hlookup ; try(intuition ; exfalso ; congruence).
				destruct v ; try(intuition ; exfalso ; congruence).
			}
			assert(Hsh1btsNotEq : beqAddr (CPaddr (blockToShareInCurrPartAddr + sh1offset)) blockToShareInCurrPartAddr = false).
			{ rewrite <- beqAddrFalse in *.
				intro Hsh1btsEqfalse.
				rewrite Hsh1btsEqfalse in *.
				unfold isSHE in *. unfold isBE in *.
				destruct (lookup blockToShareInCurrPartAddr (memory s0) beqAddr) ; try(intuition ; exfalso ; congruence).
				destruct v ; try(exfalso ; congruence).
			}

			assert(beqscebts : beqAddr sceaddr blockToShareInCurrPartAddr = false).
			{
				rewrite <- beqAddrFalse. intro Heqfalse.
				assert(HSCEs0 : isSCE sceaddr s0) by intuition.
				rewrite Heqfalse in *.
				unfold isSCE in *. unfold isBE in *.
				destruct (lookup blockToShareInCurrPartAddr (memory s0) beqAddr) eqn:Hf ; try(exfalso ; congruence).
				destruct v ; try(exfalso ; congruence).
			}
			assert(beqnewBsh1 : beqAddr newBlockEntryAddr (CPaddr (blockToShareInCurrPartAddr + sh1offset)) = false).
			{
				rewrite <- beqAddrFalse. intro Heqfalse.
				rewrite Heqfalse in *.
				unfold isSHE in *.
				intuition ; destruct (lookup (CPaddr (blockToShareInCurrPartAddr + sh1offset)) (memory s0) beqAddr) eqn:Hf ; try(exfalso ; congruence) ;
				destruct v ; try(exfalso ; congruence).
			}
		assert(beqbtsnew : newBlockEntryAddr <> blockToShareInCurrPartAddr).
		{
			(* at s0, newBlockEntryAddr is a free slot, which is not the case of
					blockToShareInCurrPartAddr *)
			assert(HFirstFreeSlotPointerIsBEAndFreeSlot : FirstFreeSlotPointerIsBEAndFreeSlot s0)
					by (unfold consistency in * ; intuition).
			unfold FirstFreeSlotPointerIsBEAndFreeSlot in *.
			assert(HPDTchilds0 : isPDT globalIdPDChild s0) by intuition.
			apply isPDTLookupEq in HPDTchilds0.
			destruct HPDTchilds0 as [childpdentry Hlookupchilds0].
			specialize(HFirstFreeSlotPointerIsBEAndFreeSlot globalIdPDChild childpdentry Hlookupchilds0).
			assert(HfirstfreeNotNull : firstfreeslot childpdentry <> nullAddr).
			{
				assert(Hfirstfreechilds0 : pdentryFirstFreeSlot globalIdPDChild childfirststructurepointer s0 /\
               beqAddr nullAddr childfirststructurepointer = false) by intuition.
				unfold pdentryFirstFreeSlot in *. rewrite Hlookupchilds0 in *.
				rewrite <- beqAddrFalse in *.
				destruct Hfirstfreechilds0 as [HfirstfreeEq HfirstFreeNotNull].
				subst childfirststructurepointer. congruence.
			}
			specialize (HFirstFreeSlotPointerIsBEAndFreeSlot HfirstfreeNotNull).
			assert(Hlookuppdchilds0 : lookup globalIdPDChild (memory s0) beqAddr = Some (PDT pdentry)) by intuition.
			assert(HpdEq: childpdentry = pdentry).
			{ unfold pdentryFirstFreeSlot in *. rewrite Hlookuppdchilds0 in *.
				inversion Hlookupchilds0. intuition.
			}
			rewrite HpdEq in *.
			assert(HnewBEq : firstfreeslot pdentry = newBlockEntryAddr) by intuition.
			rewrite HnewBEq in *.
			intro HBTSnewBEq. (* newB is a free slot, so its present flag is false
														blockToShareInCurrPartAddr is not a free slot,
														so the equality is a constradiction*)
			subst blockToShareInCurrPartAddr.
			assert(HwellFormedsh1newBs0 : wellFormedFstShadowIfBlockEntry s0)
				by (unfold consistency in * ; intuition).
			unfold wellFormedFstShadowIfBlockEntry in *.
			assert(HwellFormedSCnewBs0 : wellFormedShadowCutIfBlockEntry s0)
				by (unfold consistency in * ; intuition).
			unfold wellFormedShadowCutIfBlockEntry in *.
			assert(HBEnewBs0 : isBE newBlockEntryAddr s0) by intuition.
			specialize (HwellFormedsh1newBs0 newBlockEntryAddr HBEnewBs0).
			specialize (HwellFormedSCnewBs0 newBlockEntryAddr HBEnewBs0).
			unfold isBE in *. unfold isSHE in *. unfold isSCE in *.
			unfold isFreeSlot in *.
			unfold bentryPFlag in *.
			destruct (lookup newBlockEntryAddr (memory s0) beqAddr) eqn:Hbe ; try(exfalso ; congruence).
			destruct v ; try(exfalso ; congruence).
			destruct (lookup (CPaddr (newBlockEntryAddr + sh1offset)) (memory s0) beqAddr) eqn:Hsh1 ; try(exfalso ; congruence).
			destruct v ; try(exfalso ; congruence).
			destruct HwellFormedSCnewBs0 as [scentryaddr (HSCEs0 & HscentryEq)].
			subst scentryaddr.
			destruct (lookup (CPaddr (newBlockEntryAddr + scoffset))  (memory s0) beqAddr) eqn:Hsce ; try(exfalso ; congruence).
			destruct v ; try(exfalso ; congruence).
			intuition. subst addrIsPresent.
			assert(Hfalse : negb (present b) = true).
			{
				assert(Htrue : present b = false) by intuition.
				rewrite Htrue. trivial.
			}
			congruence.
		}
			assert(HlookupBTSEq : lookup blockToShareInCurrPartAddr (memory s) beqAddr =
													lookup blockToShareInCurrPartAddr (memory s0) beqAddr).
			{
				rewrite Hs.
				cbn. rewrite beqAddrTrue.
				rewrite beqscebts.
						assert (HnewBsceNotEq : beqAddr newBlockEntryAddr sceaddr = false) by (rewrite <- beqAddrFalse in * ; intuition).
						rewrite HnewBsceNotEq. (*newBlock <> sce *)
						cbn.
						destruct (beqAddr newBlockEntryAddr blockToShareInCurrPartAddr) eqn:Hf ; try(exfalso ; congruence).
						rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
						rewrite <- beqAddrFalse in *.
						repeat rewrite removeDupIdentity ; intuition.
						destruct (beqAddr globalIdPDChild newBlockEntryAddr) eqn:Hfg ; try(exfalso ; congruence).
						rewrite <- DependentTypeLemmas.beqAddrTrue in Hfg. congruence.
						cbn.
						destruct (beqAddr globalIdPDChild blockToShareInCurrPartAddr) eqn:Hfff ; try(exfalso ; congruence).
						rewrite <- DependentTypeLemmas.beqAddrTrue in Hfff. congruence.
						rewrite beqAddrTrue.
						rewrite <- beqAddrFalse in *.
						repeat rewrite removeDupIdentity ; intuition.
			}
			assert(newFsceNotEq : newFirstFreeSlotAddr <> (CPaddr (blockToShareInCurrPartAddr + sh1offset))).
			{
				intro HnewFirstsh1Eq.
				assert(HFirstFreeBE : FirstFreeSlotPointerIsBEAndFreeSlot s)
						by (unfold consistency in * ; intuition).
				unfold FirstFreeSlotPointerIsBEAndFreeSlot in *.
				assert(Hlookuppdchild : lookup globalIdPDChild (memory s) beqAddr = Some (PDT pdentry1)) by intuition.
				specialize (HFirstFreeBE globalIdPDChild pdentry1 Hlookuppdchild).
				assert(HnewFEq : firstfreeslot pdentry1 = newFirstFreeSlotAddr).
				{ subst pdentry1. subst pdentry0. simpl. reflexivity. }
				rewrite HnewFEq in *.
				destruct HFirstFreeBE.
				- (* newFirstFreeSlotAddr = nullAddr *)
					intro HnewFNullEq.
					rewrite HnewFirstsh1Eq in *.
					rewrite HnewFNullEq in *.
					assert(HnullAddrExists : nullAddrExists s)
						by (unfold consistency in * ; intuition).
					unfold nullAddrExists in *. unfold isPADDR in *.
					destruct (lookup nullAddr (memory s) beqAddr) ; try(exfalso ; congruence).
					destruct v ; try(exfalso ; congruence).
				- (* newFirstFreeSlotAddr = nullAddr *)
					rewrite <- HnewFirstsh1Eq in *.
					unfold isBE in *. unfold isSHE in *.
					destruct (lookup newFirstFreeSlotAddr (memory s) beqAddr) ; try(exfalso ; congruence).
					destruct v ; try(exfalso ; congruence).
			}

			rewrite beqAddrTrue.
			assert(Hsh1entryEq : sh1entrybts = sh1entry).
			{ rewrite Hsh1entry in *. inversion HSHEbtss. trivial. }
			rewrite Hsh1entryEq in *.

			destruct H77 as [s1 (s2 & (s3 & (s4 & (s5 & (s6 & (s7 & (s8 & (s9 & (s10 & Hstates)))))))))].
			assert(HsEq : s = s10).
			{ intuition. subst s10. subst s9. subst s8. subst s7. subst s6. subst s5. subst s4.
				subst s3. subst s2. subst s1. simpl. subst s.
				f_equal.
			}
			eexists. intuition.
			+ unfold s'. rewrite Hs. simpl. rewrite Hsh1entryEq in *. intuition.
			+ rewrite beqsh1newB.
				rewrite <- beqAddrFalse in *.
				repeat rewrite removeDupIdentity ; intuition.
			+ rewrite beqsh1pdchild.
				rewrite <- beqAddrFalse in *.
				repeat rewrite removeDupIdentity ; intuition.
			+ unfold pdentryNbFreeSlots in *. unfold s'.
 				cbn.
				rewrite beqsh1pdchild.
				rewrite <- beqAddrFalse in *.
				repeat rewrite removeDupIdentity ; intuition.
			+ unfold isPDT. unfold s'. cbn.
				rewrite beqsh1pdchild.
				rewrite <- beqAddrFalse in *.
				repeat rewrite removeDupIdentity ; intuition.
			+ unfold isBE. unfold s'.
				cbn.
				rewrite beqsh1newB.
				rewrite <- beqAddrFalse in *.
				repeat rewrite removeDupIdentity ; intuition.
			+ unfold isSCE. unfold s'.
				cbn.
				rewrite beqsh1sce.
				rewrite <- beqAddrFalse in *.
				repeat rewrite removeDupIdentity ; intuition.
			+ unfold isSHE. rewrite Hsh1entry. trivial.
			+ unfold isSHE. unfold s'.
				cbn. rewrite beqAddrTrue. trivial.
			+ rewrite <- beqAddrFalse in *. congruence.
			+ rewrite <- beqAddrFalse in *. congruence.
			+ rewrite <- beqAddrFalse in *. congruence.
			+ rewrite <- beqAddrFalse in *. congruence.
			+ rewrite <- beqAddrFalse in *. congruence.
			+ destruct H75 as [optionfreeslotslist (s2' & (n0 & (n1 & (n2 & (nbleft & Hoptionfreeslotslist)))))].
				exists optionfreeslotslist. exists s. exists n0. exists n1. exists n2.
				exists nbleft. intuition.
				++ unfold s'. f_equal. rewrite Hs. simpl. intuition.
						rewrite Hsh1entryEq. f_equal.
				++ assert(HfreeSlotsEq : getFreeSlotsListRec n2 newFirstFreeSlotAddr s nbleft =
      															optionfreeslotslist) by intuition.
					rewrite <- HfreeSlotsEq.
					apply eq_sym.
					eapply getFreeSlotsListRecEqN ; intuition.
					lia.
				++ assert(HfreeSlotsEq : getFreeSlotsListRec n2 newFirstFreeSlotAddr s nbleft =
      															optionfreeslotslist) by intuition.
					unfold s'.
						rewrite <- HfreeSlotsEq.
						eapply getFreeSlotsListRecEqSHE ; intuition.
						+++ unfold isBE in *. unfold isSHE in *.
								destruct (lookup (CPaddr (blockToShareInCurrPartAddr + sh1offset)) (memory s) beqAddr) ; try(exfalso ; congruence).
								destruct v ; try(exfalso ; congruence).
						+++ unfold isPADDR in *. unfold isSHE in *.
								destruct (lookup (CPaddr (blockToShareInCurrPartAddr + sh1offset)) (memory s) beqAddr) ; try(exfalso ; congruence).
								destruct v ; try(exfalso ; congruence).
			+	destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + sh1offset)) blockToShareInCurrPartAddr) eqn:btssh1bts ; try(exfalso ; congruence).
				rewrite <- beqAddrFalse in *.
				repeat rewrite removeDupIdentity ; intuition.
			+	exists s1. exists s2. exists s3. exists s4. exists s5. exists s6.
				exists s7. exists s8. exists s9. exists s10. eexists.
				rewrite <- HsEq. intuition.
				++ 	subst s9. subst s8. subst s7. subst s6. subst s5. subst s4.
						subst s3. subst s2. subst s1. simpl. subst s.
						f_equal.
				++ (* isSHE sh1eaddr s10 = isSHE sh1eaddr s0 *)
						assert(HwellFormedFstShadows : wellFormedFstShadowIfBlockEntry s)
							by (unfold consistency in * ; intuition).
						specialize(HwellFormedFstShadows blockToShareInCurrPartAddr HBEbts).
						unfold isSHE. rewrite Hs.
						simpl. rewrite beqAddrTrue.
						destruct (beqAddr sceaddr (CPaddr (blockToShareInCurrPartAddr + sh1offset))) eqn:beqscesh1 ; try(exfalso ; congruence).
						+++ (* sceaddr = (CPaddr (blockToShareInCurrPartAddr + sh1offset)) *)
								rewrite <- DependentTypeLemmas.beqAddrTrue in beqscesh1.
								rewrite <- beqscesh1 in *.
								unfold isSHE in *. unfold isSCE in *.
								destruct (lookup sceaddr (memory s0) beqAddr) eqn:Hlookup ; try(exfalso ; congruence).
								destruct v eqn:Hv ; try(exfalso ; congruence).
						+++ (* sceaddr <> (CPaddr (blockToShareInCurrPartAddr + sh1offset)) *)
								destruct (beqAddr newBlockEntryAddr sceaddr) eqn:HnewBsce ; try(exfalso ; congruence).
								rewrite <- DependentTypeLemmas.beqAddrTrue in HnewBsce. congruence.
								cbn. rewrite beqnewBsh1.
								cbn.
								rewrite <- beqAddrFalse in *.
									repeat rewrite removeDupIdentity; intuition.
									rewrite beqAddrTrue.
									destruct (beqAddr globalIdPDChild newBlockEntryAddr) eqn:HpdchildnewB ; try(exfalso ; congruence).
									rewrite <- DependentTypeLemmas.beqAddrTrue in HpdchildnewB. congruence.
									cbn.
									destruct (beqAddr globalIdPDChild (CPaddr (blockToShareInCurrPartAddr + sh1offset))) eqn:Hpdchildsh1pa ; try(exfalso ; congruence).
									-- (* globalIdPDChild = (CPaddr (pa + sh1offset)) *)
											rewrite <- DependentTypeLemmas.beqAddrTrue in Hpdchildsh1pa.
											rewrite <- Hpdchildsh1pa in *.
											unfold isSHE in *. unfold isPDT in *.
											destruct (lookup globalIdPDChild (memory s0) beqAddr) eqn:Hlookup ; try(exfalso ; congruence).
									-- (* globalIdPDChild <> (CPaddr (pa + sh1offset)) *)
										rewrite <- beqAddrFalse in *.
										repeat rewrite removeDupIdentity; intuition.
} intros. simpl.
eapply bindRev.
{ (** MAL.writeSh1InChildLocationFromBlockEntryAddr **)
	eapply weaken. apply writeSh1InChildLocationFromBlockEntryAddr.
	intros. simpl.
	destruct H6 as [s0 Hprops].
	destruct Hprops as [Hprops0 Hprops].
	destruct Hprops as [pdentry (pdentry0 & (pdentry1
											& (bentry & (bentry0 & (bentry1 & (bentry2 & (bentry3 & (bentry4 & (bentry5 & (bentry6
											& (sceaddr & (scentry
											& (newBlockEntryAddr & (newFirstFreeSlotAddr
											& (predCurrentNbFreeSlots
											& (sh1eaddr & (sh1entry & (sh1entry0
											& Hprops))))))))))))))))))].
	assert(HSh1Offset : sh1eaddr = CPaddr (blockToShareInCurrPartAddr + sh1offset))
							by intuition.
	rewrite <- HSh1Offset in *.
	assert(HBEs0 : isBE blockToShareInCurrPartAddr s0) by intuition.
	assert(HlookupBTSs : lookup blockToShareInCurrPartAddr (memory s) beqAddr =
												lookup blockToShareInCurrPartAddr (memory s0) beqAddr)
		by intuition.
	assert(HBEbts : isBE blockToShareInCurrPartAddr s).
	{ unfold isBE. rewrite HlookupBTSs.
		apply isBELookupEq in HBEs0. destruct HBEs0 as [btsentry0 Hlookups0].
		rewrite Hlookups0. trivial.
	}
	assert(HSHEs : isSHE sh1eaddr s) by intuition.
	apply isSHELookupEq in HSHEs as [sh1entrybts HSHEs].
	exists sh1entrybts.
	assert(HSHEEq : sh1eaddr = CPaddr (blockToShareInCurrPartAddr + sh1offset)) by intuition.
	split. subst sh1eaddr. intuition.
	instantiate (1:= fun _ s =>
exists s0,
	(* s0 *)
	(partitionsIsolation s0 /\
                           kernelDataIsolation s0 /\
                           verticalSharing s0 /\ consistency s0 /\
                          consistency s0 /\
                          isPDT currentPart s0 /\
                          currentPart = currentPartition s0 /\
                         (blockToShareInCurrPartAddr = nullAddr \/
                          (exists entry : BlockEntry,
                             lookup blockToShareInCurrPartAddr
                               (memory s0) beqAddr =
                             Some (BE entry) /\
                             blockToShareInCurrPartAddr = idBlockToShare)) /\
                        beqAddr nullAddr blockToShareInCurrPartAddr =
                        false /\
                       (exists entry : BlockEntry,
                          lookup blockToShareInCurrPartAddr
                            (memory s0) beqAddr =
                          Some (BE entry)) /\
                      (isChildCurrPart = true ->
                       exists sh1entryaddr : paddr,
                         isChildCurrPart =
                         checkChild idPDchild s0 sh1entryaddr /\
                         (exists entry : BlockEntry,
                            lookup idPDchild (memory s0) beqAddr =
                            Some (BE entry) /\
                            (exists sh1entry : Sh1Entry,
                               sh1entryAddr idPDchild sh1entryaddr s0 /\
                               lookup sh1entryaddr (memory s0) beqAddr =
                               Some (SHE sh1entry)))) /\
                     bentryStartAddr idPDchild globalIdPDChild s0 /\
                    isPDT globalIdPDChild s0 /\
                   pdentryNbFreeSlots globalIdPDChild nbfreeslots s0 /\
                  zero = CIndex 0 /\
                 false = StateLib.Index.leb nbfreeslots zero /\
                pdentryFirstFreeSlot globalIdPDChild
                  childfirststructurepointer s0 /\
               beqAddr nullAddr childfirststructurepointer = false /\
              bentryAFlag blockToShareInCurrPartAddr addrIsAccessible s0 /\
             bentryPFlag blockToShareInCurrPartAddr addrIsPresent s0 /\
            pdentryVidt globalIdPDChild vidtBlockGlobalId s0 /\
           bentryStartAddr blockToShareInCurrPartAddr blockstart s0 /\
          bentryEndAddr blockToShareInCurrPartAddr blockend s0)

/\ (exists pdentry pdentry0 pdentry1: PDTable,
		exists bentry bentry0 bentry1 bentry2 bentry3 bentry4 bentry5 bentry6: BlockEntry,
		exists sceaddr : paddr, exists scentry : SCEntry,
		exists newBlockEntryAddr newFirstFreeSlotAddr : paddr,
		exists predCurrentNbFreeSlots : index,
		exists sh1eaddr : paddr, exists sh1entry sh1entry0 sh1entry1: Sh1Entry,

  s = {|
     currentPartition := currentPartition s0;
     memory := add sh1eaddr
                     (SHE
                        {|	PDchild := PDchild sh1entry0;
                        		PDflag := PDflag sh1entry0;
                        		inChildLocation := blockToShareChildEntryAddr |})
							(add sh1eaddr
                     (SHE
                        {|	PDchild := globalIdPDChild;
                        		PDflag := PDflag sh1entry;
                        		inChildLocation := inChildLocation sh1entry |})
							(add sceaddr
									(SCE {| origin := blockstart; next := next scentry |})
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
                    (CBlockEntry (read bentry2) (write bentry2) (exec bentry2) true
                       (accessible bentry2) (blockindex bentry2) (blockrange bentry2)))
							(add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry1) (write bentry1) (exec bentry1)
                       (present bentry1) true (blockindex bentry1) (blockrange bentry1)))
							(add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry0) (write bentry0) (exec bentry0)
                       (present bentry0) (accessible bentry0) (blockindex bentry0)
                       (CBlock (startAddr (blockrange bentry0)) blockend)))
							(add newBlockEntryAddr
                     (BE
                        (CBlockEntry (read bentry) (write bentry)
                           (exec bentry) (present bentry) (accessible bentry)
                           (blockindex bentry)
                           (CBlock blockstart (endAddr (blockrange bentry)))))
								(add globalIdPDChild
                 (PDT
                    {|
                    structure := structure pdentry0;
                    firstfreeslot := firstfreeslot pdentry0;
                    nbfreeslots := predCurrentNbFreeSlots;
                    nbprepare := nbprepare pdentry0;
                    parent := parent pdentry0;
                    MPU := MPU pdentry0;
										vidtBlock := vidtBlock pdentry0 |})
								(add globalIdPDChild
                 (PDT
                    {|
                    structure := structure pdentry;
                    firstfreeslot := newFirstFreeSlotAddr;
                    nbfreeslots := ADT.nbfreeslots pdentry;
                    nbprepare := nbprepare pdentry;
                    parent := parent pdentry;
                    MPU := MPU pdentry;
										vidtBlock := vidtBlock pdentry |}) (memory s0) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr |}
/\ (lookup sh1eaddr (memory s0) beqAddr = Some (SHE sh1entry)
/\ lookup sh1eaddr (memory s) beqAddr = Some (SHE sh1entry1) /\
sh1entry1 = {| PDchild := PDchild sh1entry0;
             	PDflag := PDflag sh1entry0;
             	inChildLocation := blockToShareChildEntryAddr |} /\
sh1entry0 = {| PDchild := globalIdPDChild;
             	PDflag := PDflag sh1entry;
             	inChildLocation := inChildLocation sh1entry |}
/\ newBlockEntryAddr = blockToShareChildEntryAddr
/\ lookup newBlockEntryAddr (memory s0) beqAddr = Some (BE bentry)
/\ lookup newBlockEntryAddr (memory s) beqAddr = Some (BE bentry6)
/\
bentry6 = (CBlockEntry (read bentry5) (write bentry5) e (present bentry5)
                       (accessible bentry5) (blockindex bentry5) (blockrange bentry5))
/\
bentry5 = (CBlockEntry (read bentry4) w (exec bentry4) (present bentry4)
                       (accessible bentry4) (blockindex bentry4) (blockrange bentry4))
/\
bentry4 = (CBlockEntry r (write bentry3) (exec bentry3) (present bentry3)
                       (accessible bentry3) (blockindex bentry3) (blockrange bentry3))
/\
bentry3 = (CBlockEntry (read bentry2) (write bentry2) (exec bentry2) true
                       (accessible bentry2) (blockindex bentry2) (blockrange bentry2))
/\
bentry2 = (CBlockEntry (read bentry1) (write bentry1) (exec bentry1)
                       (present bentry1) true (blockindex bentry1) (blockrange bentry1))
/\
bentry1 = (CBlockEntry (read bentry0) (write bentry0) (exec bentry0)
                       (present bentry0) (accessible bentry0) (blockindex bentry0)
                       (CBlock (startAddr (blockrange bentry0)) blockend))
/\
bentry0 = (CBlockEntry (read bentry) (write bentry)
                           (exec bentry) (present bentry) (accessible bentry)
                           (blockindex bentry)
                           (CBlock blockstart (endAddr (blockrange bentry))))
/\ sceaddr = (CPaddr (newBlockEntryAddr + scoffset))
/\ lookup globalIdPDChild (memory s0) beqAddr = Some (PDT pdentry)
/\ lookup globalIdPDChild (memory s) beqAddr = Some (PDT pdentry1) /\
pdentry1 = {|     structure := structure pdentry0;
                    firstfreeslot := firstfreeslot pdentry0;
                    nbfreeslots := predCurrentNbFreeSlots;
                    nbprepare := nbprepare pdentry0;
                    parent := parent pdentry0;
                    MPU := MPU pdentry0;
										vidtBlock := vidtBlock pdentry0 |} /\
pdentry0 = {|    structure := structure pdentry;
                    firstfreeslot := newFirstFreeSlotAddr;
                    nbfreeslots := ADT.nbfreeslots pdentry;
                    nbprepare := nbprepare pdentry;
                    parent := parent pdentry;
                    MPU := MPU pdentry;
										vidtBlock := vidtBlock pdentry|}
	(* propagate new properties (copied from last step) *)
	/\ pdentryNbFreeSlots globalIdPDChild predCurrentNbFreeSlots s
	/\ StateLib.Index.pred nbfreeslots = Some predCurrentNbFreeSlots
	/\ blockindex bentry6 = blockindex bentry5
	/\ blockindex bentry5 = blockindex bentry4
	/\ blockindex bentry4 = blockindex bentry3
	/\ blockindex bentry3 = blockindex bentry2
	/\ blockindex bentry2 = blockindex bentry1
	/\ blockindex bentry1 = blockindex bentry0
	/\ blockindex bentry0 = blockindex bentry
	/\ blockindex bentry6 = blockindex bentry
	/\ isPDT globalIdPDChild s0
	/\ isPDT globalIdPDChild s
	/\ isBE newBlockEntryAddr s0
	/\ isBE newBlockEntryAddr s
	/\ isBE blockToShareInCurrPartAddr s0
	/\ isSCE sceaddr s0
	/\ isSCE sceaddr s
	/\ isSHE sh1eaddr s0
	/\ isSHE sh1eaddr s
	/\ sceaddr = CPaddr (newBlockEntryAddr + scoffset)
	/\ sh1eaddr = CPaddr (blockToShareInCurrPartAddr + sh1offset)
	/\ firstfreeslot pdentry1 = newFirstFreeSlotAddr
	/\ newBlockEntryAddr = (firstfreeslot pdentry)
	/\ newBlockEntryAddr <> blockToShareInCurrPartAddr
	/\ newFirstFreeSlotAddr <> globalIdPDChild
	/\ newFirstFreeSlotAddr <> newBlockEntryAddr
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
	/\ (exists (optionfreeslotslist : list optionPaddr) (s2 : state)
					(n0 n1 n2 : nat) (nbleft : index),
			nbleft = CIndex (nbfreeslots - 1) /\
			nbleft < maxIdx /\
			s =
			{|
				currentPartition := currentPartition s0;
				memory :=
					add sh1eaddr
                     (SHE
                        {|	PDchild := PDchild sh1entry0;
                        		PDflag := PDflag sh1entry0;
                        		inChildLocation := blockToShareChildEntryAddr |})
						(memory s2) beqAddr
			|} /\
			optionfreeslotslist = getFreeSlotsListRec n1 newFirstFreeSlotAddr s2 nbleft /\
			getFreeSlotsListRec n2 newFirstFreeSlotAddr s nbleft = optionfreeslotslist /\
			optionfreeslotslist = getFreeSlotsListRec n0 newFirstFreeSlotAddr s0 nbleft /\
			n0 <= n1 /\
			nbleft < n0 /\
			n1 <= n2 /\
			nbleft < n2 /\
			n2 <= maxIdx + 1 /\
			(wellFormedFreeSlotsList optionfreeslotslist = False -> False) /\
			NoDup (filterOption optionfreeslotslist) /\
			(In newBlockEntryAddr (filterOption optionfreeslotslist) -> False))
	/\ lookup blockToShareInCurrPartAddr (memory s) beqAddr =
						lookup blockToShareInCurrPartAddr (memory s0) beqAddr)

(* intermediate steps *)
/\ (exists s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12,
s1 = {|
     currentPartition := currentPartition s0;
     memory := add globalIdPDChild
                (PDT
                   {|
                     structure := structure pdentry;
                     firstfreeslot := newFirstFreeSlotAddr;
                     nbfreeslots := ADT.nbfreeslots pdentry;
                     nbprepare := nbprepare pdentry;
                     parent := parent pdentry;
                     MPU := MPU pdentry;
                     vidtBlock := vidtBlock pdentry
                   |}) (memory s0) beqAddr |}
/\ s2 = {|
     currentPartition := currentPartition s1;
     memory := add globalIdPDChild
		           (PDT
		              {|
		                structure := structure pdentry0;
		                firstfreeslot := firstfreeslot pdentry0;
		                nbfreeslots := predCurrentNbFreeSlots;
		                nbprepare := nbprepare pdentry0;
		                parent := parent pdentry0;
		                MPU := MPU pdentry0;
		                vidtBlock := vidtBlock pdentry0
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
	                  (CBlock blockstart (endAddr (blockrange bentry))))
                 ) (memory s2) beqAddr |}
/\ s4 = {|
     currentPartition := currentPartition s3;
     memory := add newBlockEntryAddr
               (BE
                  (CBlockEntry (read bentry0)
                     (write bentry0) (exec bentry0)
                     (present bentry0) (accessible bentry0)
                     (blockindex bentry0)
                     (CBlock (startAddr (blockrange bentry0)) blockend))
                 ) (memory s3) beqAddr |}
/\ s5 = {|
     currentPartition := currentPartition s4;
     memory := add newBlockEntryAddr
              (BE
                 (CBlockEntry (read bentry1)
                    (write bentry1) (exec bentry1)
                    (present bentry1) true (blockindex bentry1)
                    (blockrange bentry1))
                 ) (memory s4) beqAddr |}
/\ s6 = {|
     currentPartition := currentPartition s5;
     memory := add newBlockEntryAddr
               (BE
                  (CBlockEntry (read bentry2) (write bentry2)
                     (exec bentry2) true (accessible bentry2)
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
								(SCE {| origin := blockstart; next := next scentry |}
                 ) (memory s9) beqAddr |}
/\ s11 = {|
     currentPartition := currentPartition s10;
     memory := add sh1eaddr
        (SHE
           {|
             PDchild := globalIdPDChild;
             PDflag := PDflag sh1entry;
             inChildLocation := inChildLocation sh1entry
           |}) (memory s10) beqAddr |}
/\ s12 = {|
     currentPartition := currentPartition s11;
     memory := add sh1eaddr
         (SHE
            {|	PDchild := PDchild sh1entry0;
            		PDflag := PDflag sh1entry0;
            		inChildLocation := blockToShareChildEntryAddr
           |}) (memory s11) beqAddr |}
(* by setting s10 as the new base, no need to get down to s0 anymore
		since we have already proven all consistency properties for s10 *)
/\ consistency s10
/\ isPDT globalIdPDChild s10
/\ isSCE sceaddr s10
/\ isSHE sh1eaddr s10
/\ isBE newBlockEntryAddr s10
/\ isSHE sh1eaddr s10 = isSHE sh1eaddr s0
))).
intros. simpl.  set (s' := {|
      currentPartition :=  _|}).
			destruct Hprops as [Hs Hprops].
			split.
			exists s0. split. intuition.
			exists pdentry. exists pdentry0. exists pdentry1.
			exists bentry. exists bentry0. exists bentry1. exists bentry2. exists bentry3.
			exists bentry4. exists bentry5. exists bentry6. exists sceaddr. exists scentry.
			exists newBlockEntryAddr. exists newFirstFreeSlotAddr. exists predCurrentNbFreeSlots.
			exists sh1eaddr. exists sh1entry. exists sh1entry0.
			assert(beqsh1pdchild : beqAddr (CPaddr (blockToShareInCurrPartAddr + sh1offset)) globalIdPDChild = false)
					by (subst sh1eaddr; rewrite <- beqAddrFalse ; intuition).
			assert(beqsh1newB : beqAddr (CPaddr (blockToShareInCurrPartAddr + sh1offset)) newBlockEntryAddr = false)
					by (subst sh1eaddr; rewrite <- beqAddrFalse ; intuition).
			assert(beqsh1sce : beqAddr (CPaddr (blockToShareInCurrPartAddr + sh1offset)) sceaddr = false)
					by (subst sh1eaddr; rewrite <- beqAddrFalse ; intuition).

			assert(Hsh1btsNotEq : beqAddr (CPaddr (blockToShareInCurrPartAddr + sh1offset)) blockToShareInCurrPartAddr = false).
			{ rewrite <- beqAddrFalse in *.
				intro Hsh1btsEqfalse.
				rewrite Hsh1btsEqfalse in *.
				unfold isSHE in *. unfold isBE in *.
				destruct (lookup blockToShareInCurrPartAddr (memory s0) beqAddr) ; try(intuition ; exfalso ; congruence).
			}

			rewrite beqAddrTrue.
			assert(Hsh1entryEq : sh1entrybts = sh1entry0).
			{ rewrite HSHEs in *.
				assert(HEq : Some (SHE sh1entrybts) = Some (SHE sh1entry0)) by intuition.
				inversion HEq. trivial. }
			rewrite Hsh1entryEq in *. subst sh1eaddr.
			assert(HbtsNotNull : blockToShareInCurrPartAddr <> nullAddr)
				by (rewrite <- beqAddrFalse in * ; intuition).
			eexists. intuition.
			+ unfold s'. rewrite Hs. simpl. rewrite Hsh1entryEq. intuition.
			+ rewrite beqsh1newB.
				rewrite <- beqAddrFalse in *.
				repeat rewrite removeDupIdentity ; intuition.
			+ rewrite beqsh1pdchild.
				rewrite <- beqAddrFalse in *.
				repeat rewrite removeDupIdentity ; intuition.
			+ unfold pdentryNbFreeSlots in *. unfold s'.
 				cbn.
				rewrite beqsh1pdchild.
				rewrite <- beqAddrFalse in *.
				repeat rewrite removeDupIdentity ; intuition.
			+ unfold isPDT. unfold s'. cbn.
				rewrite beqsh1pdchild.
				rewrite <- beqAddrFalse in *.
				repeat rewrite removeDupIdentity ; intuition.
			+ unfold isBE. unfold s'.
				cbn.
				rewrite beqsh1newB.
				rewrite <- beqAddrFalse in *.
				repeat rewrite removeDupIdentity ; intuition.
			+ unfold isSCE. unfold s'.
				cbn.
				rewrite beqsh1sce.
				rewrite <- beqAddrFalse in *.
				repeat rewrite removeDupIdentity ; intuition.
			+ unfold isSHE. unfold s'.
				cbn. rewrite beqAddrTrue. trivial.
			+ destruct H84 as [optionfreeslotslist (s2 & (n0 & (n1 & (n2 & (nbleft & Hoptionfreeslotslist)))))].
				exists optionfreeslotslist. exists s. exists n0. exists n1. exists n2.
				exists nbleft. intuition.
				++ unfold s'. f_equal. rewrite Hs. simpl. intuition.
						rewrite Hsh1entryEq. f_equal.
				++ assert(HfreeSlotsEq : getFreeSlotsListRec n2 newFirstFreeSlotAddr s nbleft =
      															optionfreeslotslist) by intuition.
					rewrite <- HfreeSlotsEq.
					apply eq_sym.
					eapply getFreeSlotsListRecEqN ; intuition.
					lia.
				++ assert(HfreeSlotsEq : getFreeSlotsListRec n2 newFirstFreeSlotAddr s nbleft =
      															optionfreeslotslist) by intuition.
					unfold s'.
					assert(newFsceNotEq : newFirstFreeSlotAddr <> (CPaddr (blockToShareInCurrPartAddr + sh1offset)))
							by intuition.
						rewrite <- HfreeSlotsEq.
						eapply getFreeSlotsListRecEqSHE ; intuition.
						+++ unfold isBE in *. unfold isSHE in *.
								destruct (lookup (CPaddr (blockToShareInCurrPartAddr + sh1offset)) (memory s) beqAddr) ; try(exfalso ; congruence).
								destruct v ; try(exfalso ; congruence).
						+++ unfold isPADDR in *. unfold isSHE in *.
								destruct (lookup (CPaddr (blockToShareInCurrPartAddr + sh1offset)) (memory s) beqAddr) ; try(exfalso ; congruence).
								destruct v ; try(exfalso ; congruence).
			+	destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + sh1offset)) blockToShareInCurrPartAddr) eqn:btssh1bts ; try(exfalso ; congruence).
				rewrite <- beqAddrFalse in *.
				repeat rewrite removeDupIdentity ; intuition.
			+ destruct H87 as [s1 (s2 & (s3 & (s4 & (s5 & (s6 & (s7 & (s8 & (s9 & (s10 & (s11 & Hstates))))))))))].
				exists s1. exists s2. exists s3. exists s4. exists s5. exists s6.
				exists s7. exists s8. exists s9. exists s10. exists s11.
				eexists. intuition.
		+ assert(HbtsNotNull : blockToShareInCurrPartAddr <> nullAddr)
				by (rewrite <- beqAddrFalse in * ; intuition).
			intuition.
			++ (* wellFormedFstShadowIfBlockEntry *)
					(* DUP insertNewEntry *)
					unfold wellFormedFstShadowIfBlockEntry.
					intros pa HBEaddrs. intuition.

					(* check all possible values for pa in the modified state s
								-> only possible are newBlockEntryAddr and blockToShareInCurrPartAddr

						1) if pa == blockToShareInCurrPartAddr :
								so blockToShareInCurrPartAddr+sh1offset = sh1eaddr :
								-> still a SHE at s -> OK
						2) pa <> blockToShareInCurrPartAddr :
								3) if pa == newBlockEntryAddr :
										so pa+sh1offset :
										- is not modified -> leads to s0 -> OK
								4) if pa <> newBlockEntryAddr :
									- relates to another bentry than newBlockentryAddr
										(either in the same structure or another)
										- other entry not modified -> leads to s0 -> OK
					*)

					(* 1) isBE pa s in hypothesis: eliminate impossible values for pa *)
					destruct (beqAddr globalIdPDChild pa) eqn:beqpdpa in HBEaddrs ; try(exfalso ; congruence).
					* (* globalIdPDChild = pa *)
						rewrite <- DependentTypeLemmas.beqAddrTrue in beqpdpa.
						rewrite <- beqpdpa in *.
						unfold isPDT in *. unfold isBE in *.
						destruct (lookup globalIdPDChild (memory s) beqAddr) eqn:Hlookup ; try(exfalso ; congruence).
						destruct v eqn:Hv ; try(exfalso ; congruence).
					* (* globalIdPDChild <> pa *)
						destruct (beqAddr sceaddr pa) eqn:beqpasce ; try(exfalso ; congruence).
						** (* sceaddr <> pa *)
							rewrite <- DependentTypeLemmas.beqAddrTrue in beqpasce.
							rewrite <- beqpasce in *.
							unfold isSCE in *. unfold isBE in *.
							destruct (lookup sceaddr (memory s) beqAddr) eqn:Hlookup ; try(exfalso ; congruence).
							destruct v eqn:Hv ; try(exfalso ; congruence).
						** (* sceaddr = pa *)
							destruct (beqAddr sh1eaddr pa) eqn:beqsh1pa ; try(exfalso ; congruence).
							*** (* sh1eaddr = pa *)
									rewrite <- DependentTypeLemmas.beqAddrTrue in beqsh1pa.
									rewrite <- beqsh1pa in *.
									unfold isSHE in *. unfold isBE in *.
									destruct (lookup sh1eaddr (memory s) beqAddr) eqn:Hlookup ; try(exfalso ; congruence).
									destruct v eqn:Hv ; try(exfalso ; congruence).
							*** (* sh1eaddr <> pa *)
									destruct (beqAddr blockToShareInCurrPartAddr pa) eqn:beqbtspa ; try(exfalso ; congruence).
									**** (* 1) treat special case where blockToShareInCurrPartAddr = pa *)
											rewrite <- DependentTypeLemmas.beqAddrTrue in beqbtspa.
											rewrite <- beqbtspa in *.
											unfold isSHE.
											rewrite Hs. cbn.
											subst sh1eaddr.
											rewrite beqAddrTrue. trivial.
									**** (* 2) blockToShareInCurrPartAddr <> pa *)
												destruct (beqAddr newBlockEntryAddr pa) eqn:beqnewblockpa in HBEaddrs ; try(exfalso ; congruence).
												***** (* 3) treat special case where newBlockEntryAddr = pa *)
															rewrite <- DependentTypeLemmas.beqAddrTrue in beqnewblockpa.
															rewrite <- beqnewblockpa in *.
															assert(Hcons : wellFormedFstShadowIfBlockEntry s0)
																			by (unfold consistency in *; intuition).
															unfold wellFormedFstShadowIfBlockEntry in *.
															specialize (Hcons newBlockEntryAddr).
															unfold isBE in Hcons.
															assert(HBE : lookup newBlockEntryAddr (memory s0) beqAddr = Some (BE bentry))
																		by intuition.
															rewrite HBE in *.
															apply isSHELookupEq.
															rewrite Hs. cbn.
															rewrite beqAddrTrue.
															(* eliminate impossible values for (CPaddr (newBlockEntryAddr + sh1offset)) *)
															destruct (beqAddr sceaddr (CPaddr (newBlockEntryAddr + sh1offset))) eqn:beqsceoffset ; try(exfalso ; congruence).
															++++ (* sceaddr = (CPaddr (newBlockEntryAddr + sh1offset)) *)
																		rewrite <- DependentTypeLemmas.beqAddrTrue in beqsceoffset.
																		assert(HwellFormedSHE : wellFormedShadowCutIfBlockEntry s0)
																						by (unfold consistency in *; intuition).
																		specialize(HwellFormedSHE newBlockEntryAddr).
																		unfold isBE in HwellFormedSHE.
																		rewrite HBE in *. destruct HwellFormedSHE ; trivial.
																		intuition. subst x.
																		unfold isSCE in *. unfold isSHE in *.
																		rewrite <- beqsceoffset in *.
																		destruct (lookup sceaddr (memory s0) beqAddr) eqn:Hlookup ; try(exfalso ; congruence).
																		destruct v eqn:Hv ; try(exfalso ; congruence).
															++++ (*sceaddr <> (CPaddr (newBlockEntryAddr + sh1offset))*)
																		repeat rewrite beqAddrTrue.
																		rewrite <- beqAddrFalse in *. intuition.
																		repeat rewrite removeDupIdentity; intuition.
																		destruct (beqAddr newBlockEntryAddr sceaddr) eqn:Hfalse. (*proved before *)
																		rewrite <- DependentTypeLemmas.beqAddrTrue in Hfalse ; congruence.
																		cbn.
																		destruct (beqAddr newBlockEntryAddr (CPaddr (newBlockEntryAddr + sh1offset))) eqn:newblocksh1offset.
																		+++++ (* newBlockEntryAddr = (CPaddr (newBlockEntryAddr + sh1offset))*)
																					rewrite <- DependentTypeLemmas.beqAddrTrue in newblocksh1offset.
																					rewrite <- newblocksh1offset in *.
																					unfold isSHE in *. rewrite HBE in *.
																					exfalso ; congruence.
																		+++++ (* newBlockEntryAddr <> (CPaddr (newBlockEntryAddr + sh1offset))*)
																					cbn.
																					rewrite <- beqAddrFalse in *. intuition.
																					repeat rewrite removeDupIdentity; intuition.
																					destruct (beqAddr globalIdPDChild newBlockEntryAddr) eqn:Hffalse. (*proved before *)
																					rewrite <- DependentTypeLemmas.beqAddrTrue in Hffalse ; congruence.
																					cbn.
																					destruct (beqAddr globalIdPDChild (CPaddr (newBlockEntryAddr + sh1offset))) eqn:pdsh1offset.
																					++++++ (* globalIdPDChild = (CPaddr (newBlockEntryAddr + sh1offset))*)
																									rewrite <- DependentTypeLemmas.beqAddrTrue in *.
																									rewrite <- pdsh1offset in *.
																									unfold isSHE in *. unfold isPDT in *.
																									destruct (lookup globalIdPDChild (memory s0) beqAddr) eqn:Hlookup ; try(exfalso ; congruence).
																									destruct v eqn:Hv ; try(exfalso ; congruence).
																					++++++ (* globalIdPDChild <> (CPaddr (newBlockEntryAddr + sh1offset))*)
																									destruct (beqAddr sh1eaddr (CPaddr (newBlockEntryAddr + sh1offset))) eqn:beqsh1newBsh1 ; try(exfalso ; congruence).
																									- (* sh1eaddr = (CPaddr (newBlockEntryAddr + scoffset)) *)
																										(* can't discriminate by type, must do by showing it must be equal to newBlockEntryAddr and creates a contradiction *)
																										subst sh1eaddr.
																										rewrite <- DependentTypeLemmas.beqAddrTrue in beqsh1newBsh1.
																										rewrite <- beqsh1newBsh1 in *.
																										assert(HnullAddrExistss0 : nullAddrExists s0)
																												by (unfold consistency in *; intuition).
																										unfold nullAddrExists in *. unfold isPADDR in *.
																										unfold CPaddr in beqsh1newBsh1.
																										destruct (le_dec (blockToShareInCurrPartAddr + sh1offset) maxAddr) eqn:Hj.
																										-- destruct (le_dec (newBlockEntryAddr + sh1offset) maxAddr) eqn:Hk.
																											--- simpl in *.
																												inversion beqsh1newBsh1 as [Heq].
																												rewrite PeanoNat.Nat.add_cancel_r in Heq.
																												apply CPaddrInjectionNat in Heq.
																												repeat rewrite paddrEqId in Heq.
																												congruence.
																											--- inversion beqsh1newBsh1 as [Heq].
																												rewrite Heq in *.
																												rewrite <- nullAddrIs0 in *.
																												rewrite <- beqAddrFalse in *. (* newBlockEntryAddr <> nullAddr *)
																												destruct (lookup nullAddr (memory s0) beqAddr) ; try(exfalso ; congruence).
																												destruct v ; try(exfalso ; congruence).
																										-- assert(Heq : CPaddr(blockToShareInCurrPartAddr + sh1offset) = nullAddr).
																											{ rewrite nullAddrIs0.
																												unfold CPaddr. rewrite Hj.
																												destruct (le_dec 0 maxAddr) ; intuition.
																												f_equal. apply proof_irrelevance.
																											}
																											rewrite Heq in *.
																											destruct (lookup nullAddr (memory s0) beqAddr) ; try(exfalso ; congruence).
																											destruct v ; try(exfalso ; congruence).
																							- (* sh1eaddr <> (CPaddr (newBlockEntryAddr + sh1offset)) *)
																								subst sh1eaddr.
																								destruct (beqAddr sceaddr (CPaddr (newBlockEntryAddr + sh1offset))) eqn:beqscesh1 ; try(exfalso ; congruence).
																								rewrite <- DependentTypeLemmas.beqAddrTrue in beqscesh1. congruence.
																								destruct (beqAddr sceaddr (CPaddr (blockToShareInCurrPartAddr + sh1offset))) eqn:beqscebtssh1 ; try(exfalso ; congruence).
																								rewrite <- DependentTypeLemmas.beqAddrTrue in beqscebtssh1. congruence.
																								cbn.
																								rewrite beqscesh1.
																								destruct (beqAddr newBlockEntryAddr (CPaddr (blockToShareInCurrPartAddr + sh1offset))) eqn:beqnewsh1 ; try(exfalso ; congruence).
																								rewrite <- DependentTypeLemmas.beqAddrTrue in beqnewsh1. congruence.
																								cbn.
																								destruct (beqAddr newBlockEntryAddr (CPaddr (newBlockEntryAddr + sh1offset))) eqn:beqnewsh1new ; try(exfalso ; congruence).
																								rewrite <- DependentTypeLemmas.beqAddrTrue in beqnewsh1new. congruence.
																								cbn.
																								rewrite <- beqAddrFalse in *.
																								repeat rewrite removeDupIdentity; intuition.
																								destruct (beqAddr globalIdPDChild newBlockEntryAddr) eqn:beqglobalnew ; try(exfalso ; congruence).
																								rewrite <- DependentTypeLemmas.beqAddrTrue in beqglobalnew. congruence.
																								cbn.
																								destruct (beqAddr globalIdPDChild (CPaddr (newBlockEntryAddr + sh1offset))) eqn:beqglobalnewsh1 ; try(exfalso ; congruence).
																								rewrite <- DependentTypeLemmas.beqAddrTrue in beqglobalnewsh1. congruence.
																								rewrite <- beqAddrFalse in *.
																								repeat rewrite removeDupIdentity; intuition.
																								assert(HSHEs0: isSHE (CPaddr (newBlockEntryAddr + sh1offset)) s0)
																									by intuition.
																								apply isSHELookupEq in HSHEs0. destruct HSHEs0 as [shentry HSHEs0].
																								(* leads to s0 *)
																								exists shentry. easy.
							***** (* newBlockEntryAddr <> pa *)
										(* 4) treat special case where pa is not equal to any modified entries*)
										assert(Hcons : wellFormedFstShadowIfBlockEntry s0)
														by (unfold consistency in *; intuition).
										unfold wellFormedFstShadowIfBlockEntry in *.
										specialize (Hcons pa).
										assert(HBEpaEq : isBE pa s = isBE pa s0).
										{	unfold isBE. rewrite Hs.
											cbn. rewrite beqAddrTrue.
											destruct (beqAddr sh1eaddr pa) eqn:Hsh1pa ; try(exfalso ; congruence).
											subst sh1eaddr.
											destruct (beqAddr sceaddr (CPaddr (blockToShareInCurrPartAddr + sh1offset))) eqn:Hscesh1 ; try(exfalso ; congruence).
											rewrite <- DependentTypeLemmas.beqAddrTrue in Hscesh1. congruence.
											cbn.
											destruct (beqAddr sceaddr pa) eqn:Hscepa ; try(exfalso ; congruence).
											cbn.
											destruct (beqAddr newBlockEntryAddr sceaddr) eqn:HnewBsce ; try(exfalso ; congruence).
											rewrite <- DependentTypeLemmas.beqAddrTrue in HnewBsce. congruence.
											cbn.
											destruct (beqAddr newBlockEntryAddr (CPaddr (blockToShareInCurrPartAddr + sh1offset))) eqn:HnewBsh1 ; try(exfalso ; congruence).
											rewrite <- DependentTypeLemmas.beqAddrTrue in HnewBsh1. congruence.
											cbn.
											destruct (beqAddr newBlockEntryAddr pa) eqn:HnewBpa ; try(exfalso ; congruence).
											rewrite <- beqAddrFalse in *.
											repeat rewrite removeDupIdentity; intuition.
											destruct (beqAddr globalIdPDChild newBlockEntryAddr) eqn:HpdchildnewB ; try(exfalso ; congruence).
											rewrite <- DependentTypeLemmas.beqAddrTrue in HpdchildnewB. congruence.
											cbn.
											destruct (beqAddr globalIdPDChild pa) eqn:Hpdchildpa ; try(exfalso ; congruence).
											rewrite <- DependentTypeLemmas.beqAddrTrue in Hpdchildpa. congruence.
											rewrite beqAddrTrue.
											rewrite <- beqAddrFalse in *.
											repeat rewrite removeDupIdentity; intuition.
										}
										assert(HBEpas0 : isBE pa s0) by (rewrite HBEpaEq in * ; intuition).
										specialize(Hcons HBEpas0).
										(* no modifictions of SHE so what is true at s0 is still true at s *)
										assert(HSHEpaEq : isSHE (CPaddr (pa + sh1offset)) s = isSHE (CPaddr (pa + sh1offset)) s0).
										{
											unfold isSHE. rewrite Hs.
											cbn. rewrite beqAddrTrue.
											destruct (beqAddr sh1eaddr (CPaddr (pa + sh1offset))) eqn:beqsh1pash1 ; try(exfalso ; congruence).
											- (* sh1eaddr = (CPaddr (pa + scoffset)) *)
												(* can't discriminate by type, must do by showing it must be equal to pa and creates a contradiction *)
												subst sh1eaddr.
												rewrite <- DependentTypeLemmas.beqAddrTrue in beqsh1pash1.
												rewrite <- beqsh1pash1 in *.
												assert(HnullAddrExistss0 : nullAddrExists s0)
														by (unfold consistency in *; intuition).
												unfold nullAddrExists in *. unfold isPADDR in *.
												unfold CPaddr in beqsh1pash1.
												destruct (le_dec (blockToShareInCurrPartAddr + sh1offset) maxAddr) eqn:Hj.
												-- destruct (le_dec (pa + sh1offset) maxAddr) eqn:Hk.
													--- simpl in *.
														inversion beqsh1pash1 as [Heq].
														rewrite PeanoNat.Nat.add_cancel_r in Heq.
														apply CPaddrInjectionNat in Heq.
														repeat rewrite paddrEqId in Heq.
														rewrite <- beqAddrFalse in *.
														congruence.
													--- inversion beqsh1pash1 as [Heq].
														rewrite Heq in *.
														rewrite <- nullAddrIs0 in *.
														rewrite <- beqAddrFalse in *. (* newBlockEntryAddr <> nullAddr *)
														destruct (lookup nullAddr (memory s0) beqAddr) ; try(exfalso ; congruence).
														destruct v ; try(exfalso ; congruence).
												-- assert(Heq : CPaddr(blockToShareInCurrPartAddr + sh1offset) = nullAddr).
													{ rewrite nullAddrIs0.
														unfold CPaddr. rewrite Hj.
														destruct (le_dec 0 maxAddr) ; intuition.
														f_equal. apply proof_irrelevance.
													}
													rewrite Heq in *.
													destruct (lookup nullAddr (memory s0) beqAddr) ; try(exfalso ; congruence).
													destruct v ; try(exfalso ; congruence).
										- (* sh1eaddr <> (CPaddr (newBlockEntryAddr + sh1offset)) *)
											subst sh1eaddr.
											destruct (beqAddr sceaddr (CPaddr (blockToShareInCurrPartAddr + sh1offset))) eqn:Hscesh1 ; try(exfalso ; congruence).
											rewrite <- DependentTypeLemmas.beqAddrTrue in Hscesh1. congruence.
											cbn.
											destruct (beqAddr sceaddr (CPaddr (pa + sh1offset))) eqn:Hsh1pa ; try(exfalso ; congruence).
											+ (* sceaddr = (CPaddr (pa + sh1offset)) *)
												rewrite <- DependentTypeLemmas.beqAddrTrue in Hsh1pa.
												rewrite <- Hsh1pa in *.
												unfold isSHE in *. unfold isSCE in *.
												destruct (lookup sceaddr (memory s0) beqAddr) eqn:Hlookup ; try(exfalso ; congruence).
												destruct v eqn:Hv ; try(exfalso ; congruence).
											+ (* sceaddr <> (CPaddr (pa + sh1offset)) *)
												destruct (beqAddr newBlockEntryAddr sceaddr) eqn:HnewBsce ; try(exfalso ; congruence).
												rewrite <- DependentTypeLemmas.beqAddrTrue in HnewBsce. congruence.
												cbn.
												destruct (beqAddr newBlockEntryAddr (CPaddr (blockToShareInCurrPartAddr + sh1offset))) eqn:HnewBsh1 ; try(exfalso ; congruence).
												rewrite <- DependentTypeLemmas.beqAddrTrue in HnewBsh1. congruence.
												cbn.
												destruct (beqAddr newBlockEntryAddr (CPaddr (pa + sh1offset))) eqn:HnewBsh1pa ; try(exfalso ; congruence).
												* (* newBlockEntryAddr = (CPaddr (pa + sh1offset)) *)
													rewrite <- DependentTypeLemmas.beqAddrTrue in HnewBsh1pa.
													rewrite <- HnewBsh1pa in *.
													unfold isSHE in *. unfold isBE in *.
													destruct (lookup newBlockEntryAddr (memory s0) beqAddr) eqn:Hlookup ; try(exfalso ; congruence).
													destruct v eqn:Hv ; try(exfalso ; congruence).
												* (* newBlockEntryAddr <> (CPaddr (pa + sh1offset)) *)
													rewrite <- beqAddrFalse in *.
													repeat rewrite removeDupIdentity; intuition.
													rewrite beqAddrTrue.
													destruct (beqAddr globalIdPDChild newBlockEntryAddr) eqn:HpdchildnewB ; try(exfalso ; congruence).
													rewrite <- DependentTypeLemmas.beqAddrTrue in HpdchildnewB. congruence.
													cbn.
													destruct (beqAddr globalIdPDChild (CPaddr (pa + sh1offset))) eqn:Hpdchildsh1pa ; try(exfalso ; congruence).
													-- (* globalIdPDChild = (CPaddr (pa + sh1offset)) *)
															rewrite <- DependentTypeLemmas.beqAddrTrue in Hpdchildsh1pa.
															rewrite <- Hpdchildsh1pa in *.
															unfold isSHE in *. unfold isPDT in *.
															destruct (lookup globalIdPDChild (memory s0) beqAddr) eqn:Hlookup ; try(exfalso ; congruence).
															destruct v eqn:Hv ; try(exfalso ; congruence).
													-- (* globalIdPDChild <> (CPaddr (pa + sh1offset)) *)
														rewrite <- beqAddrFalse in *.
														repeat rewrite removeDupIdentity; intuition.
										}
										(* leads to s0 *)
										rewrite HSHEpaEq. intuition.
				++ (* KernelStructureStartFromBlockEntryAddrIsKS *)
						unfold KernelStructureStartFromBlockEntryAddrIsKS.
						intros bentryaddr blockidx Hlookup Hblockidx.

						assert(Hcons0 : KernelStructureStartFromBlockEntryAddrIsKS s0) by (unfold consistency in * ; intuition).
						unfold KernelStructureStartFromBlockEntryAddrIsKS in Hcons0.

						(* check all possible values for bentryaddr in the modified state s
								-> only possible is newBlockEntryAddr
							1) if bentryaddr == newBlockEntryAddr :
									so KS is
									- still a BlockEntry in s, index not modified
										- kernelStart is newBlock -> still a BE
										- kernelStart is not modified -> leads to s0 -> OK
							2) if bentryaddr <> newBlockEntryAddr :
									- relates to another bentry than newBlockentryAddr
										(either in the same structure or another)
										- kernelStart is newBlock -> still a BE
										- kernelStart is not modified -> leads to s0 -> OK
					*)
						(* Check all values except newBlockEntryAddr *)
						destruct (beqAddr sceaddr bentryaddr) eqn:beqscebentry; try(exfalso ; congruence).
						-	(* sceaddr = bentryaddr *)
							rewrite <- DependentTypeLemmas.beqAddrTrue in beqscebentry.
							rewrite <- beqscebentry in *.
							unfold isSCE in *.
							unfold isBE in *.
							destruct (lookup sceaddr (memory s) beqAddr) ; try(exfalso ; congruence).
							destruct v ; try(exfalso ; congruence).
						-	(* sceaddr <> bentryaddr *)
							destruct (beqAddr globalIdPDChild bentryaddr) eqn:beqpdbentry; try(exfalso ; congruence).
							-- (* globalIdPDChild = bentryaddr *)
								rewrite <- DependentTypeLemmas.beqAddrTrue in beqpdbentry.
								rewrite <- beqpdbentry in *.
								unfold isPDT in *.
								unfold isBE in *.
								destruct (lookup globalIdPDChild (memory s) beqAddr) ; try(exfalso ; congruence).
								destruct v ; try(exfalso ; congruence).
							-- (* globalIdPDChild <> bentryaddr *)
									destruct (beqAddr sh1eaddr bentryaddr) eqn:beqsh1bentry ; try(exfalso ; congruence).
									--- (* sh1eaddr = bentryaddr *)
											rewrite <- DependentTypeLemmas.beqAddrTrue in beqsh1bentry.
											rewrite <- beqsh1bentry in *.
											unfold isSHE in *.
											unfold isBE in *.
											destruct (lookup sh1eaddr (memory s) beqAddr) ; try(exfalso ; congruence).
											destruct v ; try(exfalso ; congruence).
									--- (* sh1eaddr <> bentryaddr *)
										destruct (beqAddr newBlockEntryAddr bentryaddr) eqn:newbentry ; try(exfalso ; congruence).
										---- (* newBlockEntryAddr = bentryaddr *)
												rewrite <- DependentTypeLemmas.beqAddrTrue in newbentry.
												rewrite <- newbentry in *.
												unfold bentryBlockIndex in *.
												assert(HlookupnewBs : lookup newBlockEntryAddr (memory s) beqAddr = Some (BE bentry6))
													by intuition.
												rewrite HlookupnewBs in *.
												destruct Hblockidx as [Hblockidx Hidxnb].
												assert(HBEnewBs0 : isBE newBlockEntryAddr s0) by intuition.
												specialize(Hcons0 newBlockEntryAddr blockidx HBEnewBs0).
												assert(HlookupnewBs0 : lookup newBlockEntryAddr (memory s0) beqAddr = Some (BE bentry))
													by intuition.
												rewrite HlookupnewBs0 in *.
												assert(HblockidxEq : blockindex bentry6 = blockindex bentry) by intuition.
												rewrite HblockidxEq in *.
												intuition.
												rewrite <- Hblockidx in *.
												intuition.

											(* Check all possible values for CPaddr (newBlockEntryAddr - blockidx)
													-> only possible is newBlockEntryAddr when blockidx = 0
													1) if CPaddr (newBlockEntryAddr - blockidx) == newBlockEntryAddr :
															- still a BlockEntry in s with blockindex newBlockEntryAddr = 0 -> OK
													2) if CPaddr (newBlockEntryAddr - blockidx) <> newBlockEntryAddr :
															- relates to another bentry than newBlockentryAddr
																that was not modified
																(either in the same structure or another)
															- -> leads to s0 -> OK
											*)

											(* Check all values for KS *)
											destruct (beqAddr sceaddr (CPaddr (newBlockEntryAddr - blockidx))) eqn:beqsceks; try(exfalso ; congruence).
											*	(* sceaddr = (CPaddr (newBlockEntryAddr - blockidx)) *)
												rewrite <- DependentTypeLemmas.beqAddrTrue in beqsceks.
												rewrite <- beqsceks in *.
												unfold isSCE in *.
												unfold isKS in *.
												destruct (lookup sceaddr (memory s0) beqAddr) ; try(exfalso ; congruence).
												destruct v ; try(exfalso ; congruence).
											*	(* sceaddr <> kernelstarts0 *)
												destruct (beqAddr globalIdPDChild (CPaddr (newBlockEntryAddr - blockidx))) eqn:beqpdks; try(exfalso ; congruence).
												** (* globalIdPDChild = (CPaddr (newBlockEntryAddr - blockidx)) *)
													rewrite <- DependentTypeLemmas.beqAddrTrue in beqpdks.
													rewrite <- beqpdks in *.
													unfold isPDT in *.
													unfold isKS in *.
													destruct (lookup globalIdPDChild (memory s0) beqAddr) ; try(exfalso ; congruence).
													destruct v ; try(exfalso ; congruence).
												** (* pdinsertion <> (CPaddr (newBlockEntryAddr - blockidx)) *)
													destruct (beqAddr newBlockEntryAddr (CPaddr (newBlockEntryAddr - blockidx))) eqn:beqnewks ; try(exfalso ; congruence).
													*** (* newBlockEntryAddr = (CPaddr (newBlockEntryAddr - blockidx)) *)
															rewrite <- DependentTypeLemmas.beqAddrTrue in beqnewks.
															rewrite <- beqnewks in *.
															intuition.
															unfold isKS in *. rewrite HlookupnewBs. rewrite HlookupnewBs0 in *.
															rewrite HblockidxEq. rewrite Hblockidx. intuition.
													*** (* newBlockEntryAddr <> (CPaddr (newBlockEntryAddr - blockidx)) *)
															destruct (beqAddr sh1eaddr (CPaddr (newBlockEntryAddr - blockidx))) eqn:beqsh1ks ; try(exfalso ; congruence).
															**** (* sh1eaddr = (CPaddr (newBlockEntryAddr - blockidx)) *)
																		rewrite <- DependentTypeLemmas.beqAddrTrue in beqsh1ks.
																		rewrite <- beqsh1ks in *.
																		unfold isSHE in *.
																		unfold isKS in *.
																		destruct (lookup sh1eaddr (memory s0) beqAddr) ; try(exfalso ; congruence).
																		destruct v ; try(exfalso ; congruence).
															**** (* sh1eaddr <> (CPaddr (newBlockEntryAddr - blockidx)) *)
																	(* true case: KS at s0 is still a KS at s -> leads to s0 *)
																	unfold isKS.
																	rewrite Hs.
																	cbn. rewrite beqAddrTrue.
																	rewrite beqsh1ks.
																	destruct (beqAddr sceaddr sh1eaddr) eqn:scesh1 ; try(exfalso ; congruence).
																	rewrite <- DependentTypeLemmas.beqAddrTrue in scesh1. congruence.
																	cbn.
																	rewrite beqsceks.
																	destruct (beqAddr newBlockEntryAddr sceaddr) eqn:newsce ; try(exfalso ; congruence).
																	rewrite <- DependentTypeLemmas.beqAddrTrue in newsce. congruence.
																	cbn.
																	rewrite beqAddrTrue.
																	destruct (beqAddr newBlockEntryAddr sh1eaddr) eqn:newBsh1 ; try(exfalso ; congruence).
																	rewrite <- DependentTypeLemmas.beqAddrTrue in newBsh1. congruence.
																	cbn.
																	rewrite beqnewks.
																	rewrite <- beqAddrFalse in *.
																	repeat rewrite removeDupIdentity ; intuition.
																	destruct (beqAddr globalIdPDChild newBlockEntryAddr) eqn:pdnew ; try(exfalso ; congruence).
																	rewrite <- DependentTypeLemmas.beqAddrTrue in pdnew. congruence.
																	cbn.
																	destruct (beqAddr globalIdPDChild (CPaddr (newBlockEntryAddr - blockidx))) eqn:pdks'; try(exfalso ; congruence).
																	rewrite <- DependentTypeLemmas.beqAddrTrue in pdks'. congruence.
																	rewrite <- beqAddrFalse in *.
																	repeat rewrite removeDupIdentity ; intuition.
									----	(* newBlockEntryAddr <> bentryaddr *)
												(* leads to s0 *)
												assert(HlookupbentryEq : lookup bentryaddr (memory s) beqAddr = lookup bentryaddr (memory s0) beqAddr).
												{ (* DUP *)
													rewrite Hs.
													cbn. rewrite beqAddrTrue.
													destruct (beqAddr sh1eaddr bentryaddr) eqn:sh1bentry ; try(exfalso ; congruence).
													destruct (beqAddr sceaddr sh1eaddr) eqn:scesh1 ; try(exfalso ; congruence).
													rewrite <- DependentTypeLemmas.beqAddrTrue in scesh1. congruence.
													cbn.
													destruct (beqAddr sceaddr bentryaddr) eqn:scebentry ; try(exfalso ; congruence).
													cbn.
													destruct (beqAddr newBlockEntryAddr sceaddr) eqn:newsce ; try(exfalso ; congruence).
													rewrite <- DependentTypeLemmas.beqAddrTrue in newsce. congruence.
													cbn.
													destruct (beqAddr newBlockEntryAddr sh1eaddr) eqn:newsh1 ; try(exfalso ; congruence).
													rewrite <- DependentTypeLemmas.beqAddrTrue in newsh1. congruence.
													cbn.
													rewrite beqAddrTrue.
													cbn. rewrite newbentry.
													rewrite <- beqAddrFalse in *.
													repeat rewrite removeDupIdentity ; intuition.
													destruct(beqAddr globalIdPDChild newBlockEntryAddr) eqn:pdchildnewB ; try(exfalso ; congruence).
													rewrite <- DependentTypeLemmas.beqAddrTrue in pdchildnewB. congruence.
													cbn.
													destruct (beqAddr globalIdPDChild bentryaddr) eqn:pdchildbentry; try(exfalso ; congruence).
													rewrite <- DependentTypeLemmas.beqAddrTrue in pdchildbentry. congruence.
													rewrite <- beqAddrFalse in *.
													repeat rewrite removeDupIdentity ; intuition.
												}
												assert(Hlookuppdentry : exists entry : BlockEntry,
																lookup bentryaddr (memory s) beqAddr = Some (BE entry))
														by (apply isBELookupEq in Hlookup ; intuition).
												destruct Hlookuppdentry as [bbentry Hlookuppdentry].
												assert(HblockEq : isBE bentryaddr s = isBE bentryaddr s0)
													by (unfold isBE ; rewrite HlookupbentryEq ; intuition) .
												assert(Hblocks0 : isBE bentryaddr s0) by (rewrite HblockEq in * ; intuition).
												apply isBELookupEq in Hlookup. destruct Hlookup as [blockentry Hlookup].
												unfold bentryBlockIndex in *.
												rewrite HlookupbentryEq in *. rewrite Hlookup in *.
												destruct Hblockidx as [Hblockidx Hidxnb].
												specialize(Hcons0 bentryaddr blockidx Hblocks0).
												rewrite Hlookup in *.
												assert(HblockIdx : blockidx = blockindex blockentry /\
    													 blockidx < kernelStructureEntriesNb) by intuition.
												specialize(Hcons0 HblockIdx).
												(* DUP *)
												(* Check all values *)
												destruct (beqAddr sceaddr (CPaddr (bentryaddr - blockidx))) eqn:beqsceks; try(exfalso ; congruence).
												*	(* sceaddr = (CPaddr (bentryaddr - blockidx)) *)
													rewrite <- DependentTypeLemmas.beqAddrTrue in beqsceks.
													rewrite <- beqsceks in *.
													unfold isSCE in *.
													unfold isKS in *.
													destruct (lookup sceaddr (memory s0) beqAddr) ; try(exfalso ; congruence).
													destruct v ; try(exfalso ; congruence).
												*	(* sceaddr <> (CPaddr (bentryaddr - blockidx)) *)
													destruct (beqAddr globalIdPDChild (CPaddr (bentryaddr - blockidx))) eqn:beqpdks; try(exfalso ; congruence).
													** (* globalIdPDChild = (CPaddr (bentryaddr - blockidx)) *)
														rewrite <- DependentTypeLemmas.beqAddrTrue in beqpdks.
														rewrite <- beqpdks in *.
														unfold isPDT in *.
														unfold isKS in *.
														destruct (lookup globalIdPDChild (memory s0) beqAddr) ; try(exfalso ; congruence).
														destruct v ; try(exfalso ; congruence).
													** (* globalIdPDChild <> (CPaddr (bentryaddr - blockidx)) *)
														destruct (beqAddr newBlockEntryAddr (CPaddr (bentryaddr - blockidx))) eqn:beqnewks ; try(exfalso ; congruence).
														*** (* newBlockEntryAddr = (CPaddr (blockToShareInCurrPartAddr - blockidx)) *)
																rewrite <- DependentTypeLemmas.beqAddrTrue in beqnewks.
																rewrite <- beqnewks in *.
																intuition.
																assert(HlookupnewBs : lookup newBlockEntryAddr (memory s) beqAddr = Some (BE bentry6))
																	by intuition.
																assert(HlookupnewBs0 : lookup newBlockEntryAddr (memory s0) beqAddr = Some (BE bentry))
																	by intuition.
																assert(HblockidxEq : blockindex bentry6 = blockindex bentry)
																	by intuition.
																unfold isKS in *.
																rewrite HlookupnewBs. rewrite HlookupnewBs0 in *.
																rewrite HblockidxEq. intuition.
														*** (* newBlockEntryAddr <> (CPaddr (bentryaddr - blockidx)) *)
																destruct (beqAddr sh1eaddr (CPaddr (bentryaddr - blockidx))) eqn:beqsh1ks ; try(exfalso ; congruence).
																**** (* sh1eaddr = (CPaddr (bentryaddr - blockidx)) *)
																			rewrite <- DependentTypeLemmas.beqAddrTrue in beqsh1ks.
																			rewrite <- beqsh1ks in *.
																			unfold isSHE in *.
																			unfold isKS in *.
																			destruct (lookup sh1eaddr (memory s0) beqAddr) ; try(exfalso ; congruence).
																			destruct v ; try(exfalso ; congruence).
																**** 	(* sh1eaddr <> (CPaddr (bentryaddr - blockidx)) *)
																			(* true case: KS at s0 is still a KS at s -> leads to s0 *)
																			unfold isKS.
																			rewrite Hs.
																			cbn. rewrite beqAddrTrue.
																			rewrite beqsh1ks.
																			destruct (beqAddr sceaddr sh1eaddr) eqn:scesh1 ; try(exfalso ; congruence).
																			rewrite <- DependentTypeLemmas.beqAddrTrue in scesh1. congruence.
																			cbn.
																			rewrite beqsceks.
																			destruct (beqAddr newBlockEntryAddr sceaddr) eqn:newsce ; try(exfalso ; congruence).
																			rewrite <- DependentTypeLemmas.beqAddrTrue in newsce. congruence.
																			cbn.
																			rewrite beqAddrTrue.
																			destruct (beqAddr newBlockEntryAddr sh1eaddr) eqn:newBsh1 ; try(exfalso ; congruence).
																			rewrite <- DependentTypeLemmas.beqAddrTrue in newBsh1. congruence.
																			cbn.
																			rewrite beqnewks.
																			rewrite <- beqAddrFalse in *.
																			repeat rewrite removeDupIdentity ; intuition.
																			destruct (beqAddr globalIdPDChild newBlockEntryAddr) eqn:pdnew ; try(exfalso ; congruence).
																			rewrite <- DependentTypeLemmas.beqAddrTrue in pdnew. congruence.
																			cbn.
																			destruct (beqAddr globalIdPDChild (CPaddr (bentryaddr - blockidx))) eqn:pdks'; try(exfalso ; congruence).
																			rewrite <- DependentTypeLemmas.beqAddrTrue in pdks'. congruence.
																			rewrite <- beqAddrFalse in *.
																			repeat rewrite removeDupIdentity ; intuition.
} intros.
	{ (** ret **)
		eapply weaken. apply WP.ret.
		intros. simpl.
		destruct H6 as [s0 Hprops].
		destruct Hprops as [Hprops0 Hprops].
		destruct Hprops as [pdentry (pdentry0 & (pdentry1
												& (bentry & (bentry0 & (bentry1 & (bentry2 & (bentry3 & (bentry4 & (bentry5 & (bentry6
												& (sceaddr & (scentry
												& (newBlockEntryAddr & (newFirstFreeSlotAddr
												& (predCurrentNbFreeSlots
												& (sh1eaddr & (sh1entry & (sh1entry0 &(sh1entry1
												& (Hs & Hprops))))))))))))))))))))].
		(* Global knowledge on current state and at s0 *)
		assert(HbtsNotNull : blockToShareInCurrPartAddr <> nullAddr)
				by (rewrite <- beqAddrFalse in * ; intuition).
		assert(HSh1Offset : sh1eaddr = CPaddr (blockToShareInCurrPartAddr + sh1offset))
								by intuition.
		rewrite <- HSh1Offset in *.
		assert(HBEbtss0 : isBE blockToShareInCurrPartAddr s0) by intuition.
		assert(Hlookupbtss : lookup blockToShareInCurrPartAddr (memory s) beqAddr =
													lookup blockToShareInCurrPartAddr (memory s0) beqAddr)
			by intuition.
		assert(HBEbts : isBE blockToShareInCurrPartAddr s).
		{ unfold isBE. rewrite Hlookupbtss.
			apply isBELookupEq in HBEbtss0. destruct HBEbtss0 as [btsentry0 Hlookupbtss0].
			rewrite Hlookupbtss0. trivial.
		}
		assert(HSHEs : isSHE sh1eaddr s) by intuition.
		apply isSHELookupEq in HSHEs as [sh1entrybts HSHEs].

		assert(Hblockindex : blockindex bentry6 = blockindex bentry) by intuition.

		assert(HBEs0 : isBE newBlockEntryAddr s0) by intuition.
		assert(HBEs : isBE newBlockEntryAddr s) by intuition.
		assert(HlookupnewBs0 : lookup newBlockEntryAddr (memory s0) beqAddr = Some (BE bentry)) by intuition.
		assert(HlookupnewBs : lookup newBlockEntryAddr (memory s) beqAddr = Some (BE bentry6)) by intuition.

		assert(Hpdinsertions0 : lookup globalIdPDChild (memory s0) beqAddr = Some (PDT pdentry)) by intuition.
		assert(Hpdinsertions : lookup globalIdPDChild (memory s) beqAddr = Some (PDT pdentry1)) by intuition.
		assert(HPDTs0 : isPDT globalIdPDChild s0) by intuition.
		assert(HPDTs : isPDT globalIdPDChild s).
		{
			unfold isPDT. rewrite Hpdinsertions. intuition.
		}

		assert(HSceOffset : sceaddr = CPaddr (newBlockEntryAddr + scoffset)) by intuition.
		assert(HSCEs0 : isSCE sceaddr s0) by intuition.

		assert(HSCEs : isSCE sceaddr s).
		{
			unfold isSCE. rewrite Hs. cbn.
			assert (sh1eaddr <> sceaddr) by intuition.
			destruct (beqAddr sh1eaddr sceaddr) eqn:beqscesh1 ; try(exfalso ; congruence).
			rewrite <- DependentTypeLemmas.beqAddrTrue in beqscesh1. congruence.
			rewrite beqAddrTrue.
			rewrite beqAddrSym in beqscesh1.
			rewrite beqscesh1. cbn.
			rewrite beqscesh1. cbn.
			rewrite beqAddrTrue. trivial.
		}

		assert(beqpdnewB : beqAddr globalIdPDChild newBlockEntryAddr = false).
		{
			destruct (beqAddr globalIdPDChild newBlockEntryAddr) eqn:beqpdnewblock; try(exfalso ; congruence).
			rewrite <- DependentTypeLemmas.beqAddrTrue in beqpdnewblock. congruence.
			trivial.
		}

		assert(beqnewBsce : beqAddr newBlockEntryAddr sceaddr = false).
		{
			assert(newBlockEntryAddr <> sceaddr) by intuition.
			destruct (beqAddr newBlockEntryAddr sceaddr) eqn:beqnewblocksce ; try(exfalso ; congruence).
			rewrite <- DependentTypeLemmas.beqAddrTrue in beqnewblocksce. congruence.
			trivial.
		}

		assert(beqscesh1 : beqAddr sceaddr sh1eaddr = false).
		{
			assert(sceaddr <> sh1eaddr) by intuition.
			destruct (beqAddr sceaddr sh1eaddr) eqn:beqscesh1 ; try(exfalso ; congruence).
			rewrite <- DependentTypeLemmas.beqAddrTrue in beqscesh1. congruence.
			trivial.
		}

		assert(beqnewBsh1 : beqAddr newBlockEntryAddr sh1eaddr = false).
		{
			assert(newBlockEntryAddr <> sh1eaddr) by intuition.
			destruct (beqAddr newBlockEntryAddr sh1eaddr) eqn:beqnewBsh1 ; try(exfalso ; congruence).
			rewrite <- DependentTypeLemmas.beqAddrTrue in beqnewBsh1. congruence.
			trivial.
		}

		assert(beqsh1bts : beqAddr sh1eaddr blockToShareInCurrPartAddr = false).
		{
			assert(sh1eaddr <> blockToShareInCurrPartAddr) by intuition.
			destruct (beqAddr sh1eaddr blockToShareInCurrPartAddr) eqn:beqsh1bts ; try(exfalso ; congruence).
			rewrite <- DependentTypeLemmas.beqAddrTrue in beqsh1bts. congruence.
			trivial.
		}

		assert(HnewFirstFree : firstfreeslot pdentry1 = newFirstFreeSlotAddr) by intuition.

		assert(HnewB : newBlockEntryAddr = (firstfreeslot pdentry)) by intuition.

		assert(HnullAddrExists : nullAddrExists s).
		{ (* nullAddrExists s *)
			assert(Hcons0 : nullAddrExists s0) by (unfold consistency in * ; intuition).
			unfold nullAddrExists in Hcons0.
			unfold isPADDR in Hcons0.

			unfold nullAddrExists.
			unfold isPADDR.

			destruct (lookup nullAddr (memory s0) beqAddr) eqn:Hlookup ; try (exfalso ; congruence).
			destruct v eqn:Hv ; try (exfalso ; congruence).

			(* check all possible values of nullAddr in s -> nothing changed a PADDR
					so nullAddrExists at s0 prevales *)
			destruct (beqAddr globalIdPDChild nullAddr) eqn:beqpdnull; try(exfalso ; congruence).
			*	(* globalIdPDChild = nullAddr *)
				rewrite <- DependentTypeLemmas.beqAddrTrue in beqpdnull.
				rewrite beqpdnull in *.
				unfold isPDT in *.
				rewrite Hlookup in *.
				exfalso ; congruence.
			* (* globalIdPDChild <> nullAddr *)
				destruct (beqAddr sceaddr nullAddr) eqn:beqscenull; try(exfalso ; congruence).
				**	(* sceaddr = nullAddr *)
					rewrite <- DependentTypeLemmas.beqAddrTrue in beqscenull.
					unfold isSCE in *.
					rewrite <- beqscenull in *.
					rewrite Hlookup in *.
					exfalso; congruence.
				** (* sceaddr <> nullAddr *)
							destruct (beqAddr newBlockEntryAddr nullAddr) eqn:beqnewnull; try(exfalso ; congruence).
							*** (* newBlockEntryAddr = nullAddr *)
								rewrite <- DependentTypeLemmas.beqAddrTrue in beqnewnull.
								unfold isBE in *.
								rewrite <- beqnewnull in *.
								rewrite Hlookup in *.
								exfalso; congruence.
							*** (* newBlockEntryAddr <> nullAddr *)
									destruct (beqAddr sh1eaddr nullAddr) eqn:beqsh1null; try(exfalso ; congruence).
									**** (* sh1eaddr = nullAddr *)
												rewrite <- DependentTypeLemmas.beqAddrTrue in beqsh1null.
												unfold isSHE in *.
												rewrite <- beqsh1null in *.
												rewrite Hlookup in *.
												intuition ; exfalso; congruence.
									**** (* sh1eaddr <> nullAddr *)
												rewrite Hs.
												simpl. rewrite beqAddrTrue.
												rewrite beqsh1null.
												rewrite beqscesh1.
												simpl.
												rewrite beqscesh1.
												simpl.
												rewrite beqscenull.
												rewrite beqnewBsce.
												rewrite beqAddrTrue.
												simpl.
												rewrite beqnewBsh1.
												rewrite beqpdnewB.
												rewrite beqAddrTrue.
												simpl.
												rewrite beqnewBsh1.
												simpl.
												rewrite beqnewnull.
												simpl.
												rewrite beqpdnewB.
												rewrite <- beqAddrFalse in *.
												repeat rewrite removeDupIdentity ; intuition.
												simpl.
												destruct (beqAddr globalIdPDChild nullAddr) eqn:Hff; try(exfalso ; congruence).
												rewrite <- DependentTypeLemmas.beqAddrTrue in Hff. congruence.
												rewrite <- beqAddrFalse in *.
												repeat rewrite removeDupIdentity ; intuition.
												rewrite Hlookup. trivial.
	} (* end of nullAddrExists *)

		destruct Hprops as [Hprops Hstates].
		destruct Hstates as [s1 (s2 & (s3 & (s4 & (s5 & (s6 & (s7 & (s8 & (s9 & (s10 & (s11 &(s12 & Hstates)))))))))))].
		assert(HsEq : s = s12).
		{ intuition. subst s12. subst s11. subst s10. subst s9. subst s8. subst s7.
			subst s6. subst s5. subst s4.
			subst s3. subst s2. subst s1. simpl. subst s.
			f_equal.
		}
		destruct Hstates as [Hs1 (Hs2 & (Hs3 & (Hs4 & (Hs5 & (Hs6 & (Hs7 & (Hs8 & (Hs9 & (Hs10 & (Hs11 &(Hs12 & Hstates)))))))))))].
		subst s12. subst s11. simpl.
		simpl in HsEq.

		(* by setting s10 as the new base, no need to get down to s0 anymore
				since we have already proven all consistency properties for s10 *)
		assert(HPDTs10 : isPDT globalIdPDChild s10) by intuition.
		assert(HSCEs10 : isSCE sceaddr s10) by intuition.
		assert(HSHEs10 : isSHE sh1eaddr s10) by intuition.
		assert(HBEs10 : isBE newBlockEntryAddr s10) by intuition.
		assert(HSHEs10Eq : isSHE sh1eaddr s10 = isSHE sh1eaddr s0) by intuition.

		assert(HlookupbtscurrpartEq : lookup blockToShareInCurrPartAddr (memory s) beqAddr = lookup blockToShareInCurrPartAddr (memory s10) beqAddr).
		{
			rewrite HsEq.
			cbn.
			rewrite beqAddrTrue.
			rewrite beqsh1bts.
			rewrite <- beqAddrFalse in *.
			repeat rewrite removeDupIdentity; intuition.
		}

	(* Prove ret *)

split.

- (** consistency **)
	unfold consistency.
	split.
	{ (* wellFormedFstShadowIfBlockEntry *)
		(* COPY of previous step *)
		unfold wellFormedFstShadowIfBlockEntry.
		intros pa HBEaddrs. intuition.

		(* check all possible values for pa in the modified state s
					-> only possible are newBlockEntryAddr and blockToShareInCurrPartAddr

			1) if pa == blockToShareInCurrPartAddr :
					so blockToShareInCurrPartAddr+sh1offset = sh1eaddr :
					-> still a SHE at s -> OK
			2) pa <> blockToShareInCurrPartAddr :
					3) if pa == newBlockEntryAddr :
							so pa+sh1offset :
							- is not modified -> leads to s0 -> OK
					4) if pa <> newBlockEntryAddr :
						- relates to another bentry than newBlockentryAddr
							(either in the same structure or another)
							- other entry not modified -> leads to s0 -> OK
		*)

		(* 1) isBE pa s in hypothesis: eliminate impossible values for pa *)
		destruct (beqAddr globalIdPDChild pa) eqn:beqpdpa in HBEaddrs ; try(exfalso ; congruence).
		* (* globalIdPDChild = pa *)
			rewrite <- DependentTypeLemmas.beqAddrTrue in beqpdpa.
			rewrite <- beqpdpa in *.
			unfold isPDT in *. unfold isBE in *.
			destruct (lookup globalIdPDChild (memory s) beqAddr) eqn:Hlookup ; try(exfalso ; congruence).
			destruct v eqn:Hv ; try(exfalso ; congruence).
		* (* globalIdPDChild <> pa *)
			destruct (beqAddr sceaddr pa) eqn:beqpasce ; try(exfalso ; congruence).
			** (* sceaddr <> pa *)
				rewrite <- DependentTypeLemmas.beqAddrTrue in beqpasce.
				rewrite <- beqpasce in *.
				unfold isSCE in *. unfold isBE in *.
				destruct (lookup sceaddr (memory s) beqAddr) eqn:Hlookup ; try(exfalso ; congruence).
				destruct v eqn:Hv ; try(exfalso ; congruence).
			** (* sceaddr = pa *)
				destruct (beqAddr sh1eaddr pa) eqn:beqsh1pa ; try(exfalso ; congruence).
				*** (* sh1eaddr = pa *)
						rewrite <- DependentTypeLemmas.beqAddrTrue in beqsh1pa.
						rewrite <- beqsh1pa in *.
						unfold isSHE in *. unfold isBE in *.
						destruct (lookup sh1eaddr (memory s) beqAddr) eqn:Hlookup ; try(exfalso ; congruence).
						destruct v eqn:Hv ; try(exfalso ; congruence).
				*** (* sh1eaddr <> pa *)
						destruct (beqAddr blockToShareInCurrPartAddr pa) eqn:beqbtspa ; try(exfalso ; congruence).
						**** (* 1) treat special case where blockToShareInCurrPartAddr = pa *)
								rewrite <- DependentTypeLemmas.beqAddrTrue in beqbtspa.
								rewrite <- beqbtspa in *.
								unfold isSHE.
								rewrite Hs. cbn.
								subst sh1eaddr.
								rewrite beqAddrTrue. trivial.
						**** (* 2) blockToShareInCurrPartAddr <> pa *)
									destruct (beqAddr newBlockEntryAddr pa) eqn:beqnewblockpa in HBEaddrs ; try(exfalso ; congruence).
									***** (* 3) treat special case where newBlockEntryAddr = pa *)
												rewrite <- DependentTypeLemmas.beqAddrTrue in beqnewblockpa.
												rewrite <- beqnewblockpa in *.
												assert(Hcons : wellFormedFstShadowIfBlockEntry s0)
																by (unfold consistency in *; intuition).
												unfold wellFormedFstShadowIfBlockEntry in *.
												specialize (Hcons newBlockEntryAddr).
												unfold isBE in Hcons.
												assert(HBE : lookup newBlockEntryAddr (memory s0) beqAddr = Some (BE bentry))
															by intuition.
												rewrite HBE in *.
												apply isSHELookupEq.
												rewrite Hs. cbn.
												rewrite beqAddrTrue.
												(* eliminate impossible values for (CPaddr (newBlockEntryAddr + sh1offset)) *)
												destruct (beqAddr sh1eaddr (CPaddr (newBlockEntryAddr + sh1offset))) eqn:beqsh1newBsh1 ; try(exfalso ; congruence).
												- (* sh1eaddr = (CPaddr (newBlockEntryAddr + scoffset)) *)
													(* can't discriminate by type, must do by showing it must be equal to newBlockEntryAddr and creates a contradiction *)
													subst sh1eaddr.
													rewrite <- DependentTypeLemmas.beqAddrTrue in beqsh1newBsh1.
													rewrite <- beqsh1newBsh1 in *.
													assert(HnullAddrExistss0 : nullAddrExists s0)
															by (unfold consistency in *; intuition).
													unfold nullAddrExists in *. unfold isPADDR in *.
													unfold CPaddr in beqsh1newBsh1.
													destruct (le_dec (blockToShareInCurrPartAddr + sh1offset) maxAddr) eqn:Hj.
													-- destruct (le_dec (newBlockEntryAddr + sh1offset) maxAddr) eqn:Hk.
														--- simpl in *.
															inversion beqsh1newBsh1 as [Heq].
															rewrite PeanoNat.Nat.add_cancel_r in Heq.
															apply CPaddrInjectionNat in Heq.
															repeat rewrite paddrEqId in Heq.
															congruence.
														--- inversion beqsh1newBsh1 as [Heq].
															rewrite Heq in *.
															rewrite <- nullAddrIs0 in *.
															rewrite <- beqAddrFalse in *. (* newBlockEntryAddr <> nullAddr *)
															destruct (lookup nullAddr (memory s0) beqAddr) ; try(exfalso ; congruence).
															destruct v ; try(exfalso ; congruence).
													-- assert(Heq : CPaddr(blockToShareInCurrPartAddr + sh1offset) = nullAddr).
														{ rewrite nullAddrIs0.
															unfold CPaddr. rewrite Hj.
															destruct (le_dec 0 maxAddr) ; intuition.
															f_equal. apply proof_irrelevance.
														}
														rewrite Heq in *.
														destruct (lookup nullAddr (memory s0) beqAddr) ; try(exfalso ; congruence).
														destruct v ; try(exfalso ; congruence).
												- (* sh1eaddr <> (CPaddr (newBlockEntryAddr + sh1offset)) *)
													subst sh1eaddr.
													destruct (beqAddr sceaddr (CPaddr (newBlockEntryAddr + sh1offset))) eqn:beqscenewBsh1 ; try(exfalso ; congruence).
													++++ (* sceaddr = (CPaddr (newBlockEntryAddr + sh1offset)) *)
																rewrite <- DependentTypeLemmas.beqAddrTrue in beqscenewBsh1.
																assert(HwellFormedSHE : wellFormedShadowCutIfBlockEntry s0)
																				by (unfold consistency in *; intuition).
																specialize(HwellFormedSHE newBlockEntryAddr).
																unfold isBE in HwellFormedSHE.
																rewrite HBE in *. destruct HwellFormedSHE ; trivial.
																intuition. subst x.
																unfold isSCE in *. unfold isSHE in *.
																rewrite <- beqscenewBsh1 in *.
																destruct (lookup sceaddr (memory s0) beqAddr) eqn:Hlookup ; try(exfalso ; congruence).
																destruct v eqn:Hv ; try(exfalso ; congruence).
													++++ (*sceaddr <> (CPaddr (newBlockEntryAddr + sh1offset))*)
																repeat rewrite beqAddrTrue.
																rewrite <- beqAddrFalse in *. intuition.
																(*repeat rewrite removeDupIdentity; intuition.*)
																destruct (beqAddr newBlockEntryAddr sceaddr) eqn:Hfalse. (*proved before *)
																rewrite <- DependentTypeLemmas.beqAddrTrue in Hfalse ; congruence.
																destruct (beqAddr newBlockEntryAddr (CPaddr (newBlockEntryAddr + sh1offset))) eqn:newblocksh1offset.
																+++++ (* newBlockEntryAddr = (CPaddr (newBlockEntryAddr + sh1offset))*)
																			rewrite <- DependentTypeLemmas.beqAddrTrue in newblocksh1offset.
																			rewrite <- newblocksh1offset in *.
																			unfold isSHE in *. rewrite HBE in *.
																			exfalso ; congruence.
																+++++ (* newBlockEntryAddr <> (CPaddr (newBlockEntryAddr + sh1offset))*)
																			destruct (beqAddr globalIdPDChild newBlockEntryAddr) eqn:Hffalse. (*proved before *)
																			rewrite <- DependentTypeLemmas.beqAddrTrue in Hffalse ; congruence.
																			destruct (beqAddr globalIdPDChild (CPaddr (newBlockEntryAddr + sh1offset))) eqn:pdsh1offset.
																			++++++ (* globalIdPDChild = (CPaddr (newBlockEntryAddr + sh1offset))*)
																							rewrite <- DependentTypeLemmas.beqAddrTrue in *.
																							rewrite <- pdsh1offset in *.
																							unfold isSHE in *. unfold isPDT in *.
																							destruct (lookup globalIdPDChild (memory s0) beqAddr) eqn:Hlookup ; try(exfalso ; congruence).
																							destruct v eqn:Hv ; try(exfalso ; congruence).
																			++++++ (* globalIdPDChild <> (CPaddr (newBlockEntryAddr + sh1offset))*)
																							destruct (beqAddr sceaddr (CPaddr (blockToShareInCurrPartAddr + sh1offset))) eqn:beqscebtssh1 ; try(exfalso ; congruence).
																							rewrite <- DependentTypeLemmas.beqAddrTrue in beqscebtssh1. congruence.
																							cbn.
																							rewrite beqscebtssh1.
																							cbn.
																							destruct (beqAddr sceaddr (CPaddr (newBlockEntryAddr + sh1offset))) eqn:Hf ; try(exfalso ; congruence).
																							rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
																							cbn.
																							destruct (beqAddr newBlockEntryAddr (CPaddr (blockToShareInCurrPartAddr + sh1offset))) eqn:beqnewsh1 ; try(exfalso ; congruence).
																							rewrite <- DependentTypeLemmas.beqAddrTrue in beqnewsh1. congruence.
																							cbn.
																							rewrite beqnewsh1.
																							cbn.
																							rewrite newblocksh1offset.
																							rewrite <- beqAddrFalse in *.
																							repeat rewrite removeDupIdentity; intuition.
																							destruct (beqAddr globalIdPDChild newBlockEntryAddr) eqn:beqglobalnew ; try(exfalso ; congruence).
																							rewrite <- DependentTypeLemmas.beqAddrTrue in beqglobalnew. congruence.
																							cbn.
																							destruct (beqAddr globalIdPDChild (CPaddr (newBlockEntryAddr + sh1offset))) eqn:beqglobalnewsh1 ; try(exfalso ; congruence).
																							rewrite <- DependentTypeLemmas.beqAddrTrue in beqglobalnewsh1. congruence.
																							rewrite <- beqAddrFalse in *.
																							repeat rewrite removeDupIdentity; intuition.
																							assert(HSHEs0: isSHE (CPaddr (newBlockEntryAddr + sh1offset)) s0)
																								by intuition.
																							apply isSHELookupEq in HSHEs0. destruct HSHEs0 as [shentry HSHEs0].
																							(* leads to s0 *)
																							exists shentry. easy.
									***** (* newBlockEntryAddr <> pa *)
												(* 4) treat special case where pa is not equal to any modified entries*)
												assert(Hcons : wellFormedFstShadowIfBlockEntry s0)
																by (unfold consistency in *; intuition).
												unfold wellFormedFstShadowIfBlockEntry in *.
												specialize (Hcons pa).
												assert(HBEpaEq : isBE pa s = isBE pa s0).
												{	unfold isBE. rewrite Hs.
													cbn. rewrite beqAddrTrue.
													destruct (beqAddr sh1eaddr pa) eqn:Hsh1pa ; try(exfalso ; congruence).
													subst sh1eaddr.
													destruct (beqAddr sceaddr (CPaddr (blockToShareInCurrPartAddr + sh1offset))) eqn:Hscesh1 ; try(exfalso ; congruence).
													cbn.
													rewrite Hscesh1.
													cbn.
													destruct (beqAddr sceaddr pa) eqn:Hscepa ; try(exfalso ; congruence).
													cbn.
													destruct (beqAddr newBlockEntryAddr sceaddr) eqn:HnewBsce ; try(exfalso ; congruence).
													cbn.
													destruct (beqAddr newBlockEntryAddr (CPaddr (blockToShareInCurrPartAddr + sh1offset))) eqn:HnewBsh1 ; try(exfalso ; congruence).
													cbn.
													rewrite beqAddrTrue.
													rewrite HnewBsh1.
													cbn.
													destruct (beqAddr newBlockEntryAddr pa) eqn:HnewBpa ; try(exfalso ; congruence).
													rewrite <- beqAddrFalse in *.
													repeat rewrite removeDupIdentity; intuition.
													destruct (beqAddr globalIdPDChild newBlockEntryAddr) eqn:HpdchildnewB ; try(exfalso ; congruence).
													rewrite <- DependentTypeLemmas.beqAddrTrue in HpdchildnewB. congruence.
													cbn.
													destruct (beqAddr globalIdPDChild pa) eqn:Hpdchildpa ; try(exfalso ; congruence).
													rewrite <- DependentTypeLemmas.beqAddrTrue in Hpdchildpa. congruence.
													rewrite beqAddrTrue.
													rewrite <- beqAddrFalse in *.
													repeat rewrite removeDupIdentity; intuition.
												}
												assert(HBEpas0 : isBE pa s0) by (rewrite HBEpaEq in * ; intuition).
												specialize(Hcons HBEpas0).
												(* no modifications of SHE so what is true at s0 is still true at s *)
												assert(HSHEpaEq : isSHE (CPaddr (pa + sh1offset)) s = isSHE (CPaddr (pa + sh1offset)) s0).
												{
													unfold isSHE. rewrite Hs.
													cbn. rewrite beqAddrTrue.
													destruct (beqAddr sh1eaddr (CPaddr (pa + sh1offset))) eqn:beqsh1pash1 ; try(exfalso ; congruence).
													- (* sh1eaddr = (CPaddr (pa + scoffset)) *)
														(* can't discriminate by type, must do by showing it must be equal to pa and creates a contradiction *)
														subst sh1eaddr.
														rewrite <- DependentTypeLemmas.beqAddrTrue in beqsh1pash1.
														rewrite <- beqsh1pash1 in *.
														assert(HnullAddrExistss0 : nullAddrExists s0)
																by (unfold consistency in *; intuition).
														unfold nullAddrExists in *. unfold isPADDR in *.
														unfold CPaddr in beqsh1pash1.
														destruct (le_dec (blockToShareInCurrPartAddr + sh1offset) maxAddr) eqn:Hj.
														-- destruct (le_dec (pa + sh1offset) maxAddr) eqn:Hk.
															--- simpl in *.
																inversion beqsh1pash1 as [Heq].
																rewrite PeanoNat.Nat.add_cancel_r in Heq.
																apply CPaddrInjectionNat in Heq.
																repeat rewrite paddrEqId in Heq.
																rewrite <- beqAddrFalse in *.
																congruence.
															--- inversion beqsh1pash1 as [Heq].
																rewrite Heq in *.
																rewrite <- nullAddrIs0 in *.
																rewrite <- beqAddrFalse in *. (* newBlockEntryAddr <> nullAddr *)
																destruct (lookup nullAddr (memory s0) beqAddr) ; try(exfalso ; congruence).
																destruct v eqn:Hv ; try(exfalso ; congruence).
														-- assert(Heq : CPaddr(blockToShareInCurrPartAddr + sh1offset) = nullAddr).
															{ rewrite nullAddrIs0.
																unfold CPaddr. rewrite Hj.
																destruct (le_dec 0 maxAddr) ; intuition.
																f_equal. apply proof_irrelevance.
															}
															rewrite Heq in *.
															destruct (lookup nullAddr (memory s0) beqAddr) ; try(exfalso ; congruence).
															destruct v eqn:Hv ; try(exfalso ; congruence).
												- (* sh1eaddr <> (CPaddr (newBlockEntryAddr + sh1offset)) *)
													subst sh1eaddr.
													destruct (beqAddr sceaddr (CPaddr (blockToShareInCurrPartAddr + sh1offset))) eqn:Hscesh1 ; try(exfalso ; congruence).
													cbn.
													destruct (beqAddr sceaddr (CPaddr (pa + sh1offset))) eqn:Hsh1pa ; try(exfalso ; congruence).
													+ (* sceaddr = (CPaddr (pa + sh1offset)) *)
														rewrite <- DependentTypeLemmas.beqAddrTrue in Hsh1pa.
														rewrite <- Hsh1pa in *.
														unfold isSHE in *. unfold isSCE in *.
														destruct (lookup sceaddr (memory s0) beqAddr) eqn:Hlookup ; try(exfalso ; congruence).
														destruct v eqn:Hv ; try(exfalso ; congruence).
													+ (* sceaddr <> (CPaddr (pa + sh1offset)) *)
														destruct (beqAddr sceaddr (CPaddr (blockToShareInCurrPartAddr + sh1offset))) eqn:Hf ; try(exfalso ; congruence).
														cbn. rewrite beqAddrTrue.
														rewrite Hsh1pa.
														destruct (beqAddr newBlockEntryAddr sceaddr) eqn:HnewBsce ; try(exfalso ; congruence).
														cbn.
														destruct (beqAddr newBlockEntryAddr (CPaddr (blockToShareInCurrPartAddr + sh1offset))) eqn:HnewBsh1 ; try(exfalso ; congruence).
														cbn.
														rewrite HnewBsh1.
														cbn.
														destruct (beqAddr newBlockEntryAddr (CPaddr (pa + sh1offset))) eqn:HnewBsh1pa ; try(exfalso ; congruence).
														* (* newBlockEntryAddr = (CPaddr (pa + sh1offset)) *)
															rewrite <- DependentTypeLemmas.beqAddrTrue in HnewBsh1pa.
															rewrite <- HnewBsh1pa in *.
															unfold isSHE in *. unfold isBE in *.
															destruct (lookup newBlockEntryAddr (memory s0) beqAddr) eqn:Hlookup ; try(exfalso ; congruence).
															destruct v eqn:Hv ; try(exfalso ; congruence).
														* (* newBlockEntryAddr <> (CPaddr (pa + sh1offset)) *)
															rewrite <- beqAddrFalse in *.
															repeat rewrite removeDupIdentity; intuition.
															destruct (beqAddr globalIdPDChild newBlockEntryAddr) eqn:HpdchildnewB ; try(exfalso ; congruence).
															rewrite <- DependentTypeLemmas.beqAddrTrue in HpdchildnewB. congruence.
															cbn.
															destruct (beqAddr globalIdPDChild (CPaddr (pa + sh1offset))) eqn:Hpdchildsh1pa ; try(exfalso ; congruence).
															** (* globalIdPDChild = (CPaddr (pa + sh1offset)) *)
																	rewrite <- DependentTypeLemmas.beqAddrTrue in Hpdchildsh1pa.
																	rewrite <- Hpdchildsh1pa in *.
																	unfold isSHE in *. unfold isPDT in *.
																	destruct (lookup globalIdPDChild (memory s0) beqAddr) eqn:Hlookup ; try(exfalso ; congruence).
																	destruct v eqn:Hv ; try(exfalso ; congruence).
															** (* globalIdPDChild <> (CPaddr (pa + sh1offset)) *)
																	rewrite beqAddrTrue.
																	rewrite <- beqAddrFalse in *.
																	repeat rewrite removeDupIdentity; intuition.
												}
												(* leads to s0 *)
												rewrite HSHEpaEq. intuition.
	} (* end of wellFormedFstShadowIfBlockEntry *)

	split.
	{ (* PDTIfPDFlag s *)
		assert(Hcons0 : PDTIfPDFlag s0) by (unfold consistency in * ; intuition).
		unfold PDTIfPDFlag.
		intros idpdchild sh1entryaddr HcheckChilds.
		destruct HcheckChilds as [HcheckChilds Hsh1entryaddr].
		(* develop idpdchild *)
		unfold checkChild in HcheckChilds.
		unfold entryPDT.
		unfold bentryStartAddr.

		(* Force BE type for idpdchild*)
		destruct(lookup idpdchild (memory s) beqAddr) eqn:Hlookup in HcheckChilds ; try(exfalso ; congruence).
		destruct v eqn:Hv ; try(exfalso ; congruence).
		rewrite Hlookup.
		(* check all possible values of pdchild in s with the baseline at s10
				-> no possible values -> leads to s10 -> OK
		 *)

		(* PDflag is untouched, even for sh1eaddr so equal to s10 (s0) *)

		unfold sh1entryAddr in *. rewrite Hlookup in *.
		destruct (beqAddr sh1eaddr idpdchild) eqn:beqsh1idpd; try(exfalso ; congruence).
		*	(* sh1eaddr = pdchild *)
			rewrite <- DependentTypeLemmas.beqAddrTrue in beqsh1idpd.
			rewrite <- beqsh1idpd in *.
			congruence.
		* (* sh1eaddr <> pdchild *)
			assert(HidPDs0 : isBE idpdchild s10).
			{ rewrite HsEq in Hlookup. cbn in Hlookup.
				rewrite beqAddrTrue in Hlookup.
				rewrite beqsh1idpd in Hlookup.
				rewrite <- beqAddrFalse in *.
				do 2 rewrite removeDupIdentity in Hlookup; intuition.
				unfold isBE. rewrite Hlookup. trivial.
			}
			assert(HlookupidpdchildEq : lookup idpdchild (memory s) beqAddr = lookup idpdchild (memory s10) beqAddr).
			{
				rewrite HsEq.
				cbn.
				rewrite beqAddrTrue.
				rewrite beqsh1idpd.
				rewrite <- beqAddrFalse in *.
				repeat rewrite removeDupIdentity; intuition.
			}

			assert(beqsh1sh1idpdchild : beqAddr sh1eaddr sh1entryaddr = false).
			{
				rewrite HsEq in HcheckChilds.
				cbn in HcheckChilds.
				rewrite beqAddrTrue in HcheckChilds.
				destruct (beqAddr sh1eaddr sh1entryaddr) eqn:beqsh1pdsh1 ; try(exfalso ; congruence).
				- (* sh1eaddr = sh1entryaddr *)
					subst sh1eaddr. subst sh1entryaddr.
					rewrite <- DependentTypeLemmas.beqAddrTrue in beqsh1pdsh1.
					(*rewrite <- beqsh1pdsh1 in *.*)
					assert(HnullAddrExistss0 : nullAddrExists s0)
							by (unfold consistency in *; intuition).
					unfold nullAddrExists in *. unfold isPADDR in *.
					unfold CPaddr in beqsh1pdsh1.
					destruct (le_dec (blockToShareInCurrPartAddr + sh1offset) maxAddr) eqn:Hj.
					-- destruct (le_dec (idpdchild + sh1offset) maxAddr) eqn:Hk.
						--- simpl in *.
							inversion beqsh1pdsh1 as [Heq].
							rewrite PeanoNat.Nat.add_cancel_r in Heq.
							apply CPaddrInjectionNat in Heq.
							repeat rewrite paddrEqId in Heq.
							(* can't be equal because at s0 bts is accessible
									while idpdchild is not since our hypothesis states PDflag is true *)
							unfold PDTIfPDFlag in *.
							specialize (Hcons0 blockToShareInCurrPartAddr (CPaddr (blockToShareInCurrPartAddr + sh1offset))).
							unfold checkChild in Hcons0.
							unfold sh1entryAddr in *.
							apply isBELookupEq in HBEbtss0. destruct HBEbtss0 as [btscurrentry Hlookupbtscurrs0].
							rewrite Hlookupbtscurrs0 in *.
							assert(HSHEbtscurrs0 : isSHE (CPaddr (blockToShareInCurrPartAddr + sh1offset)) s0) by intuition.
							apply isSHELookupEq in HSHEbtscurrs0. destruct HSHEbtscurrs0 as [sh1btscurrentry Hlookupsh1btscurrs0].
							rewrite Hlookupsh1btscurrs0 in *.
							assert(HSomesh1Eq : Some (SHE sh1btscurrentry) = Some (SHE sh1entry)) by intuition.
							inversion HSomesh1Eq as [Hsh1Eq].
							rewrite Hsh1Eq in *.
							destruct Hcons0 as [HAFlag (HPflag & (startaddr & Hcons0))]. intuition.
							subst sh1entry0. simpl in *. intuition.
							unfold bentryAFlag in *.
							rewrite Hlookupbtscurrs0 in *.
							assert(HAflag : addrIsAccessible = true).
							{ rewrite negb_false_iff in *. intuition. }
							assert(HAflagEq : addrIsAccessible = accessible btscurrentry) by intuition.
							congruence.
						--- inversion beqsh1pdsh1 as [Heq].
								rewrite Heq in *.
								rewrite <- nullAddrIs0 in *.
								rewrite <- beqAddrFalse in *. (* sh1eaddr <> nullAddr *)
								unfold isSHE in *.
								destruct (lookup nullAddr (memory s0) beqAddr) ; try(exfalso ; congruence).
								destruct v0 ; try(exfalso ; congruence).
					-- assert(Heq : CPaddr(blockToShareInCurrPartAddr + sh1offset) = nullAddr).
						{ rewrite nullAddrIs0.
							unfold CPaddr. rewrite Hj.
							destruct (le_dec 0 maxAddr) ; intuition.
							f_equal. apply proof_irrelevance.
						}
						rewrite Heq in *.
						unfold isSHE in *.
						destruct (lookup nullAddr (memory s0) beqAddr) ; try(exfalso ; congruence).
						destruct v0 ; try(exfalso ; congruence).
				- (* sh1eaddr <> sh1entryaddr *)
					reflexivity.
				}
			(* pull hypotheses to s10 *)
			assert(Hchilds10 : true = StateLib.checkChild idpdchild s10 sh1entryaddr /\
						sh1entryAddr idpdchild sh1entryaddr s10).
			{
				rewrite HsEq in HcheckChilds.
				cbn in HcheckChilds.
				rewrite beqAddrTrue in HcheckChilds.
				rewrite beqsh1sh1idpdchild in HcheckChilds.
				subst sh1eaddr. subst sh1entryaddr.
				assert(HwellformedFstShadows10 : wellFormedFstShadowIfBlockEntry s10)
					by (unfold consistency in * ; intuition).
				specialize(HwellformedFstShadows10 idpdchild HidPDs0).
				apply isSHELookupEq in HwellformedFstShadows10 as [sh1pdchild Hlookupsh1pdchilds10].
				unfold checkChild.
				rewrite Hlookupsh1pdchilds10 in *.
				assert(Hlookupidpdchilds10  : isBE idpdchild s10) by intuition.
				apply isBELookupEq in Hlookupidpdchilds10. destruct Hlookupidpdchilds10 as [idpdchilds10 Hlookupidpdchilds10].
				unfold sh1entryAddr.
				rewrite Hlookupidpdchilds10 in *.
				rewrite <- beqAddrFalse in *.
				do 2 rewrite removeDupIdentity in HcheckChilds; intuition.
				rewrite Hlookupsh1pdchilds10 in *.
				intuition.
			}
			assert(Hcons10 : PDTIfPDFlag s10) by (unfold consistency in * ; intuition).
			unfold PDTIfPDFlag in *.
			specialize(Hcons10 idpdchild sh1entryaddr Hchilds10).

			(* A & P flags *)
			unfold bentryAFlag in *.
			unfold bentryPFlag in *.
			rewrite HlookupidpdchildEq.
			destruct (lookup idpdchild (memory s10) beqAddr) eqn:Hlookups10 ; try(exfalso ; congruence).
			destruct v0 ; try(exfalso ; congruence).
			destruct Hcons10 as [HAflag (HPflag & (startaddr & Hcons10))].
			split. assumption.
			split. assumption.

			(* PDflag *)
			eexists. intuition.
			unfold bentryStartAddr in *. unfold entryPDT in *.
			rewrite Hlookups10 in *.
			assert(HbentryEq : b = b0).
			{
				rewrite HlookupidpdchildEq in *.
				inversion Hlookup ; intuition.
			}
			subst b.
			assert(HstartaddrEq : startaddr = startAddr (blockrange b0)) by intuition.
			rewrite <- HstartaddrEq in *.
			assert(HlookupstartaddrEq : lookup startaddr (memory s) beqAddr = lookup startaddr (memory s10) beqAddr).
			{
				rewrite HsEq.
				cbn.
				rewrite beqAddrTrue.
				destruct (beqAddr sh1eaddr startaddr) eqn:beqsh1start ; try(exfalso ; congruence).
				- (* sh1eaddr = startaddr *)
					rewrite <- DependentTypeLemmas.beqAddrTrue in beqsh1start.
					rewrite <- beqsh1start in *.
					unfold isSHE in *. unfold isBE in *.
					destruct (lookup sh1eaddr (memory s10) beqAddr) ; try(exfalso ; congruence).
					destruct v0 ; try(exfalso ; congruence).
				- (* sh1eaddr <> startaddr *)
					rewrite <- beqAddrFalse in *.
					repeat rewrite removeDupIdentity; intuition.
			}
			rewrite HlookupstartaddrEq.

			destruct (lookup startaddr (memory s10) beqAddr) eqn:Hlookupstart ; try(exfalso ; congruence).
			destruct v0 ; try (exfalso ; congruence).
			reflexivity.
	} (* end of PDTIfPDFlag *)

	split. intuition. (* nullAddrExists *)

	(* Prove outside in order to use the proven properties to prove other ones *)
	assert(HFirstFreeIsBEAndFreeSlots : FirstFreeSlotPointerIsBEAndFreeSlot s).
	{ (* FirstFreeSlotPointerIsBEAndFreeSlot s *)
		assert(Hcons10 : FirstFreeSlotPointerIsBEAndFreeSlot s10) by (unfold consistency in * ; intuition).
		unfold FirstFreeSlotPointerIsBEAndFreeSlot in Hcons10.

		unfold FirstFreeSlotPointerIsBEAndFreeSlot.
		intros entryaddrpd entrypd Hentrypd Hfirstfreeslotentrypd.

		(* check all possible values for entryaddrpd in the modified state s
				with baseline s10
				-> no possible values -> leads to s10 -> OK

				must check first free slot, which uses its sh1offset:
					1) if sh1eaddr = (firstfreeslot + sh1offset)
							then firstfreeslot must be equal to blockToShareInCurrPartAddr
								BUT 2) blockToShareInCurrPartAddr is not a free slot, in particular its
									present flag is not set, so leads to a contradiction
					3) if sh1eaddr <> (firstfreeslot + sh1offset) :
								then it relates to another entry than sh1eaddr
									-> leads to s10 -> OK
		*)
		destruct (beqAddr sh1eaddr entryaddrpd) eqn:beqsh1pd; try(exfalso ; congruence).
		*	(* sh1eaddr = entryaddrpd *)
			rewrite <- DependentTypeLemmas.beqAddrTrue in beqsh1pd.
			rewrite <- beqsh1pd in *.
			congruence.
		* (* sh1eaddr <> pdchild *)
			assert(HlookuppdEq : lookup entryaddrpd (memory s) beqAddr = lookup entryaddrpd (memory s10) beqAddr).
			{
				rewrite HsEq.
				cbn.
				rewrite beqAddrTrue.
				rewrite beqsh1pd.
				rewrite <- beqAddrFalse in *.
				repeat rewrite removeDupIdentity; intuition.
			}
			assert(Hlookuppds10 : lookup entryaddrpd (memory s10) beqAddr = Some (PDT entrypd))
				by (rewrite <- HlookuppdEq ; intuition).
			specialize (Hcons10 entryaddrpd entrypd Hlookuppds10 Hfirstfreeslotentrypd).
			destruct Hcons10 as [HisBEs10 HisFreeSlots10].

			(* check all values *)
			destruct (beqAddr sh1eaddr (firstfreeslot entrypd)) eqn:beqsh1first; try(exfalso ; congruence).
			**	(* sh1eaddr = (firstfreeslot entrypd) *)
					rewrite <- DependentTypeLemmas.beqAddrTrue in beqsh1first.
					rewrite <- beqsh1first in *.
					unfold isSHE in *. unfold isBE in *.
					destruct (lookup sh1eaddr (memory s10) beqAddr) eqn:Hsh1 ; try(exfalso ; congruence).
					destruct v ; try(exfalso ; congruence).
			** (* sh1eaddr <> (firstfreeslot entrypd) *)
					destruct (beqAddr blockToShareInCurrPartAddr (firstfreeslot entrypd)) eqn:beqbtfirst ; try(exfalso ; congruence).
						**** (* 2) treat special case where blockToShareInCurrPartAddr = (firstfreeslot entrypd) *)
								(* blockToShare is not a free slot (present) at s10,
										while (firstfreeslot entrypd) is not present as it is a free slot,
										so can't be possible *)
								rewrite <- DependentTypeLemmas.beqAddrTrue in beqbtfirst.
								rewrite <- beqbtfirst in *.
								assert(HwellFormedFstShadowFirsts : wellFormedFstShadowIfBlockEntry s10)
									by (unfold consistency in * ; intuition).
								assert(HwellFormedShadowCutFirsts : wellFormedShadowCutIfBlockEntry s10)
									by (unfold consistency in * ; intuition).
								Search blockToShareInCurrPartAddr.
								specialize(HwellFormedFstShadowFirsts blockToShareInCurrPartAddr HisBEs10).
								specialize(HwellFormedShadowCutFirsts blockToShareInCurrPartAddr HisBEs10).
								destruct HwellFormedShadowCutFirsts as [scefirst HwellFormedShadowCutFirsts].
								apply isBELookupEq in HisBEs10. destruct HisBEs10 as [befirst Hlookupfirsts10].
								apply isSHELookupEq in HwellFormedFstShadowFirsts.
								destruct HwellFormedFstShadowFirsts as [sh1first Hlookupsh1firsts10].
								destruct HwellFormedShadowCutFirsts as [HwellFormedShadowCutFirsts scefirstEq].
								subst scefirst.
								apply isSCELookupEq in HwellFormedShadowCutFirsts.
								destruct HwellFormedShadowCutFirsts as [scefirst Hlookupscefirsts10].
								unfold isFreeSlot in HisFreeSlots10.
								rewrite Hlookupfirsts10 in *.
								rewrite Hlookupsh1firsts10 in *.
								rewrite Hlookupscefirsts10 in *.
								assert(HPflag : bentryPFlag blockToShareInCurrPartAddr addrIsPresent s0) by intuition.
								unfold bentryPFlag in HPflag.
								rewrite Hlookupbtss in *.
								rewrite HlookupbtscurrpartEq in *.
								subst addrIsPresent.
								assert(Hfalse : present befirst = false) by intuition.
								assert(Htrue : negb (present befirst) = false) by intuition.
								rewrite Hfalse in *. simpl in Htrue. congruence.
						**** (* blockToShareInCurrPartAddr <> (firstfreeslot entrypd) *)
								split.
								(* isBE *)
								unfold isBE.
								rewrite HsEq.
								cbn.
								rewrite beqAddrTrue.
								rewrite beqsh1first.
								rewrite <- beqAddrFalse in *.
								repeat rewrite removeDupIdentity; intuition.

								(* isFreeSlot *)
								unfold isFreeSlot.
								assert(HlookupfirstEq : lookup (firstfreeslot entrypd) (memory s) beqAddr = lookup (firstfreeslot entrypd) (memory s10) beqAddr ).
								{
				 					rewrite HsEq.
									simpl. rewrite beqAddrTrue.
									rewrite beqsh1first.
									rewrite <- beqAddrFalse in *.
									repeat rewrite removeDupIdentity; intuition.
								}
								rewrite HlookupfirstEq.

								unfold isFreeSlot in HisFreeSlots10.

								destruct (lookup (firstfreeslot entrypd) (memory s10) beqAddr) eqn:Hlookupfirst ; try(exfalso ; congruence).
								destruct v ; try(exfalso ; congruence).

								assert(Hlookupfirstsh1Eq : lookup (CPaddr (firstfreeslot entrypd + sh1offset)) (memory s) beqAddr = lookup (CPaddr (firstfreeslot entrypd + sh1offset)) (memory s10) beqAddr).
								{
									destruct (beqAddr sh1eaddr (CPaddr (firstfreeslot entrypd + sh1offset))) eqn:beqssh1newsh1 ; try(exfalso ; congruence).
									- (* 1) sh1eaddr = (CPaddr (firstfreeslot entrypd + sh1offset)) *)
										(* can't discriminate by type, must do by showing blockToShareInCurrPartAddr
												must be equal to (firstfreeslot entrypd) -> contradiction since we are not in this case *)
										subst sh1eaddr.
										rewrite <- DependentTypeLemmas.beqAddrTrue in beqssh1newsh1.
										rewrite <- beqssh1newsh1 in *.
										assert(HnullAddrExistss10 : nullAddrExists s10)
												by (unfold consistency in *; intuition).
										unfold nullAddrExists in *. unfold isPADDR in *.
										unfold CPaddr in beqssh1newsh1.
										destruct (le_dec (blockToShareInCurrPartAddr + sh1offset) maxAddr) eqn:Hj.
										-- destruct (le_dec (firstfreeslot entrypd + sh1offset) maxAddr) eqn:Hk.
											--- simpl in *.
													inversion beqssh1newsh1 as [Heq].
													rewrite PeanoNat.Nat.add_cancel_r in Heq.
													apply CPaddrInjectionNat in Heq.
													repeat rewrite paddrEqId in Heq.
													rewrite <- beqAddrFalse in *.
													congruence.
											--- inversion beqssh1newsh1 as [Heq].
												rewrite Heq in *.
												rewrite <- nullAddrIs0 in *.
												rewrite <- beqAddrFalse in *.
												destruct (lookup nullAddr (memory s10) beqAddr) ; try(exfalso ; congruence).
												destruct v ; try(exfalso ; congruence).
										-- assert(Heq : CPaddr(blockToShareInCurrPartAddr + sh1offset) = nullAddr).
											{ rewrite nullAddrIs0.
												unfold CPaddr. rewrite Hj.
												destruct (le_dec 0 maxAddr) ; intuition.
												f_equal. apply proof_irrelevance.
											}
											rewrite Heq in *.
											destruct (lookup nullAddr (memory s10) beqAddr) ; try(exfalso ; congruence).
											destruct v ; try(exfalso ; congruence).
								- (* 3) sh1eaddr <> (CPaddr (newBlockEntryAddr + sh1offset)) *)
									rewrite HsEq.
									simpl. rewrite beqAddrTrue.
									rewrite beqssh1newsh1.
									rewrite <- beqAddrFalse in *.
									repeat rewrite removeDupIdentity; intuition.
								}
								rewrite Hlookupfirstsh1Eq.

								destruct (lookup (CPaddr (firstfreeslot entrypd + sh1offset)) (memory s10) beqAddr) eqn:Hlookupsh1first ; try(exfalso ; congruence).
								destruct v ; try(exfalso ; congruence).

								assert(HlookupfirstsceEq : lookup (CPaddr (firstfreeslot entrypd + scoffset)) (memory s) beqAddr = lookup (CPaddr (firstfreeslot entrypd + scoffset)) (memory s10) beqAddr).
								{
									destruct (beqAddr sh1eaddr (CPaddr (firstfreeslot entrypd + scoffset))) eqn:beqssh1newsce ; try(exfalso ; congruence).
									- (* sh1eaddr = (CPaddr (firstfreeslot entrypd + scoffset)) *)
										rewrite <- DependentTypeLemmas.beqAddrTrue in beqssh1newsce.
										rewrite <- beqssh1newsce in *.
										unfold isSHE in *.
										destruct (lookup sh1eaddr (memory s10) beqAddr) ; try(exfalso ; congruence).
										destruct v ; try(exfalso ; congruence).
								- (* sh1eaddr <> (CPaddr (newBlockEntryAddr + scoffset)) *)
									rewrite HsEq.
									simpl. rewrite beqAddrTrue.
									rewrite beqssh1newsce.
									rewrite <- beqAddrFalse in *.
									repeat rewrite removeDupIdentity; intuition.
								}
								rewrite HlookupfirstsceEq.

								destruct (lookup (CPaddr (firstfreeslot entrypd + scoffset)) (memory s10) beqAddr) eqn:Hlookupscefirst ; try(exfalso ; congruence).
								destruct v ; try(exfalso ; congruence).

								intuition.
	} (* end of FirstFreeSlotPointerIsBEAndFreeSlot *)

	split. intuition.

	split.

	{ (* CurrentPartIsPDT s *)
	assert(Hcons10 : CurrentPartIsPDT s10) by (unfold consistency in * ; intuition).
	unfold CurrentPartIsPDT in Hcons10.

	intros entryaddrpd HcurrentPart.
	rewrite HsEq in HcurrentPart.
	cbn in HcurrentPart.
	unfold isPDT.

	(* check all possible values for entryaddrpd in the modified state s
			-> no entries match -> leads to s10 -> OK
	*)
	specialize(Hcons10 entryaddrpd HcurrentPart).

	(* Check all values *)
	destruct (beqAddr sh1eaddr entryaddrpd) eqn:beqsh1pd; try(exfalso ; congruence).
	*	(* sh1eaddr = entryaddrpd *)
		rewrite <- DependentTypeLemmas.beqAddrTrue in beqsh1pd.
		rewrite <- beqsh1pd in *.
		unfold isPDT in *. unfold isSHE in *.
		destruct (lookup sh1eaddr (memory s10) beqAddr) eqn:Hlookupscefirst ; try(exfalso ; congruence).
		destruct v ; try(exfalso ; congruence).
	* (* sh1eaddr <> entryaddrpd *)
		rewrite HsEq.
		simpl. rewrite beqAddrTrue.
		rewrite beqsh1pd.
		rewrite <- beqAddrFalse in *.
		repeat rewrite removeDupIdentity; intuition.
	} (* end of CurrentPartIsPDT *)

	split.

	{ (* wellFormedShadowCutIfBlockEntry s*)
	intros pa HBEaddrs.

	assert(Hcons10 : wellFormedShadowCutIfBlockEntry s10) by (unfold consistency in * ; intuition).
	unfold wellFormedShadowCutIfBlockEntry in Hcons10.

	(* Check all possible values
			-> no entry matches for pa or for its scentry -> leads to s10 -> OK
	*)

	destruct (beqAddr sh1eaddr pa) eqn:beqsh1pa; try(exfalso ; congruence).
	*	(* sh1eaddr = pa *)
		rewrite <- DependentTypeLemmas.beqAddrTrue in beqsh1pa.
		rewrite <- beqsh1pa in *.
		unfold isSHE in *. unfold isBE in *.
		destruct (lookup sh1eaddr (memory s) beqAddr) eqn:Hlookupscefirst ; try(exfalso ; congruence).
		destruct v ; try(exfalso ; congruence).
	* (* sh1eaddr <> pa *)
		assert(HlookuppdEq : lookup pa (memory s) beqAddr = lookup pa (memory s10) beqAddr).
		{
			rewrite HsEq.
			cbn.
			rewrite beqAddrTrue.
			rewrite beqsh1pa.
			rewrite <- beqAddrFalse in *.
			repeat rewrite removeDupIdentity; intuition.
		}
		assert(HBEpas10Eq : isBE pa s = isBE pa s10)
			by (unfold isBE ; rewrite <- HlookuppdEq ; intuition).
		assert(HBEpas10 : isBE pa s10) by (rewrite <- HBEpas10Eq ; intuition).
		specialize (Hcons10 pa HBEpas10).
		destruct Hcons10 as [scentryaddr (HisSCEs10 & Hscentryaddr)].
		exists scentryaddr. intuition.

		(* check all values for scentryaddr *)
		destruct (beqAddr sh1eaddr scentryaddr) eqn:beqsh1scentry; try(exfalso ; congruence).
		**	(* sh1eaddr = scentryaddr *)
				rewrite <- DependentTypeLemmas.beqAddrTrue in beqsh1scentry.
				rewrite <- beqsh1scentry in *.
				unfold isSHE in *. unfold isSCE in *.
				destruct (lookup sh1eaddr (memory s10) beqAddr) eqn:Hsh1 ; try(exfalso ; congruence).
				destruct v ; try(exfalso ; congruence).
		** (* sh1eaddr <> scentryaddr *)
			unfold isSCE in *.
			rewrite HsEq.
			cbn.
			rewrite beqAddrTrue.
			rewrite beqsh1scentry.
			rewrite <- beqAddrFalse in *.
			repeat rewrite removeDupIdentity; intuition.
	} (* end of wellFormedShadowCutIfBlockEntry *)

	split.

	{ (* BlocksRangeFromKernelStartIsBE s*)
		unfold BlocksRangeFromKernelStartIsBE.
		intros kernelentryaddr blockidx HKSs Hblockidx.

		assert(Hcons10 : BlocksRangeFromKernelStartIsBE s10) by (unfold consistency in * ; intuition).
		unfold BlocksRangeFromKernelStartIsBE in Hcons10.

		(* check all possible values for kernelentryaddr in the modified state s
				-> no entry matches -> leads to s10 -> OK

			same for the BE range, no entry matches -> leads to s10 -> OK
		*)

		destruct (beqAddr sh1eaddr kernelentryaddr) eqn:beqsh1ks; try(exfalso ; congruence).
		*	(* sh1eaddr = kernelentryaddr *)
			rewrite <- DependentTypeLemmas.beqAddrTrue in beqsh1ks.
			rewrite <- beqsh1ks in *.
			unfold isSHE in *. unfold isKS in *.
			destruct (lookup sh1eaddr (memory s) beqAddr) eqn:Hlookupscefirst ; try(exfalso ; congruence).
			destruct v ; try(exfalso ; congruence).
		* (* sh1eaddr <> kernelentryaddr *)
			assert(HlookupksEq : lookup kernelentryaddr (memory s) beqAddr = lookup kernelentryaddr (memory s10) beqAddr).
			{
				rewrite HsEq.
				cbn.
				rewrite beqAddrTrue.
				rewrite beqsh1ks.
				rewrite <- beqAddrFalse in *.
				repeat rewrite removeDupIdentity; intuition.
			}
			assert(HKSkss10Eq : isKS kernelentryaddr s = isKS kernelentryaddr s10)
				by (unfold isKS ; rewrite <- HlookupksEq ; intuition).
			assert(HKSkss10 : isKS kernelentryaddr s10) by (rewrite <- HKSkss10Eq ; intuition).
			specialize (Hcons10 kernelentryaddr blockidx HKSkss10 Hblockidx).

			(* check all values for ks + blockidx *)
			destruct (beqAddr sh1eaddr (CPaddr (kernelentryaddr + blockidx))) eqn:beqsh1berange; try(exfalso ; congruence).
			**	(* sh1eaddr = scentryaddr *)
					rewrite <- DependentTypeLemmas.beqAddrTrue in beqsh1berange.
					rewrite <- beqsh1berange in *.
					unfold isSHE in *. unfold isBE in *.
					destruct (lookup sh1eaddr (memory s10) beqAddr) eqn:Hsh1 ; try(exfalso ; congruence).
					destruct v ; try(exfalso ; congruence).
			** (* sh1eaddr <> scentryaddr *)
					unfold isBE in *.
					rewrite HsEq.
					cbn.
					rewrite beqAddrTrue.
					rewrite beqsh1berange.
					rewrite <- beqAddrFalse in *.
					repeat rewrite removeDupIdentity; intuition.
	} (* end of BlocksRangeFromKernelStartIsBE *)

	split.

{ (* KernelStructureStartFromBlockEntryAddrIsKS s *)
	unfold KernelStructureStartFromBlockEntryAddrIsKS.
	intros bentryaddr blockidx Hlookup Hblockidx.

	assert(Hcons0 : KernelStructureStartFromBlockEntryAddrIsKS s0) by (unfold consistency in * ; intuition).
	unfold KernelStructureStartFromBlockEntryAddrIsKS in Hcons0.

	(* check all possible values for bentryaddr in the modified state s
			-> only possible is newBlockEntryAddr
		1) if bentryaddr == newBlockEntryAddr :
				- still a BlockEntry in s, index not modified
					- kernelStart is newBlock -> still a BE
					- kernelStart is not modified -> leads to s0 -> OK
		2) if bentryaddr <> newBlockEntryAddr :
				- relates to another bentry than newBlockentryAddr
					(either in the same structure or another)
					- kernelStart is newBlock -> still a BE
					- kernelStart is not modified -> leads to s0 -> OK
*)
	(* Check all values except newBlockEntryAddr *)
	destruct (beqAddr sceaddr bentryaddr) eqn:beqscebentry; try(exfalso ; congruence).
	-	(* sceaddr = bentryaddr *)
		rewrite <- DependentTypeLemmas.beqAddrTrue in beqscebentry.
		rewrite <- beqscebentry in *.
		unfold isSCE in *.
		unfold isBE in *.
		destruct (lookup sceaddr (memory s) beqAddr) ; try(exfalso ; congruence).
		destruct v ; try(exfalso ; congruence).
	-	(* sceaddr <> bentryaddr *)
		destruct (beqAddr pdinsertion bentryaddr) eqn:beqpdbentry; try(exfalso ; congruence).
		-- (* pdinsertion = bentryaddr *)
			rewrite <- DependentTypeLemmas.beqAddrTrue in beqpdbentry.
			rewrite <- beqpdbentry in *.
			unfold isPDT in *.
			unfold isBE in *.
			destruct (lookup pdinsertion (memory s) beqAddr) ; try(exfalso ; congruence).
			destruct v ; try(exfalso ; congruence).
		-- (* pdinsertion <> bentryaddr *)
			destruct (beqAddr newBlockEntryAddr bentryaddr) eqn:newbentry ; try(exfalso ; congruence).
			--- (* newBlockEntryAddr = bentryaddr *)
					rewrite <- DependentTypeLemmas.beqAddrTrue in newbentry.
					rewrite <- newbentry in *.
					unfold bentryBlockIndex in *. rewrite HlookupnewBs in *.
					destruct Hblockidx as [Hblockidx Hidxnb].
					specialize(Hcons0 newBlockEntryAddr blockidx HBEs0).
					rewrite HlookupnewBs0 in *. intuition. rewrite Hblockindex in *.
					intuition.

					(* Check all possible values for CPaddr (newBlockEntryAddr - blockidx)
							-> only possible is newBlockEntryAddr
							1) if CPaddr (newBlockEntryAddr - blockidx) == newBlockEntryAddr :
									- still a BlockEntry in s with blockindex newBlockEntryAddr = 0 -> OK
							2) if CPaddr (newBlockEntryAddr - blockidx) <> newBlockEntryAddr :
									- relates to another bentry than newBlockentryAddr
										that was not modified
										(either in the same structure or another)
									- -> leads to s0 -> OK
					*)

					(* Check all values except newBlockEntryAddr *)
					destruct (beqAddr sceaddr (CPaddr (newBlockEntryAddr - blockidx))) eqn:beqsceks; try(exfalso ; congruence).
					*	(* sceaddr = (CPaddr (newBlockEntryAddr - blockidx)) *)
						rewrite <- DependentTypeLemmas.beqAddrTrue in beqsceks.
						rewrite <- beqsceks in *.
						unfold isSCE in *.
						unfold isKS in *.
						destruct (lookup sceaddr (memory s0) beqAddr) ; try(exfalso ; congruence).
						destruct v ; try(exfalso ; congruence).
					*	(* sceaddr <> kernelstarts0 *)
						destruct (beqAddr pdinsertion (CPaddr (newBlockEntryAddr - blockidx))) eqn:beqpdks; try(exfalso ; congruence).
						** (* pdinsertion = (CPaddr (newBlockEntryAddr - blockidx)) *)
							rewrite <- DependentTypeLemmas.beqAddrTrue in beqpdks.
							rewrite <- beqpdks in *.
							unfold isPDT in *.
							unfold isKS in *.
							destruct (lookup pdinsertion (memory s0) beqAddr) ; try(exfalso ; congruence).
							destruct v ; try(exfalso ; congruence).
						** (* pdinsertion <> (CPaddr (newBlockEntryAddr - blockidx)) *)
							destruct (beqAddr newBlockEntryAddr (CPaddr (newBlockEntryAddr - blockidx))) eqn:beqnewks ; try(exfalso ; congruence).
							*** (* newBlockEntryAddr = (CPaddr (newBlockEntryAddr - blockidx)) *)
									rewrite <- DependentTypeLemmas.beqAddrTrue in beqnewks.
									rewrite <- beqnewks in *.
									intuition.
									unfold isKS in *. rewrite HlookupnewBs. rewrite HlookupnewBs0 in *.
									rewrite Hblockindex. intuition.
							*** (* newBlockEntryAddr <> (CPaddr (newBlockEntryAddr - blockidx)) *)
									unfold isKS.
									rewrite Hs.
									cbn. rewrite beqAddrTrue.
									destruct (beqAddr sceaddr (CPaddr (newBlockEntryAddr - blockidx))) eqn:sceks ; try(exfalso ; congruence).
									destruct (beqAddr newBlockEntryAddr sceaddr) eqn:newsce ; try(exfalso ; congruence).
									rewrite beqAddrTrue.
									cbn.
									destruct (beqAddr newBlockEntryAddr (CPaddr (newBlockEntryAddr - blockidx))) eqn:newks ; try(exfalso ; congruence).
									destruct (beqAddr pdinsertion newBlockEntryAddr) eqn:pdks ; try(exfalso ; congruence).
									cbn.
									rewrite <- beqAddrFalse in *.
									repeat rewrite removeDupIdentity ; intuition.
									destruct (beqAddr pdinsertion newBlockEntryAddr) eqn:pdnew ; try(exfalso ; congruence).
									rewrite <- DependentTypeLemmas.beqAddrTrue in pdnew. congruence.
									cbn.
									destruct (beqAddr pdinsertion (CPaddr (newBlockEntryAddr - blockidx))) eqn:pdks'; try(exfalso ; congruence).
									rewrite <- DependentTypeLemmas.beqAddrTrue in pdks'. congruence.
									rewrite <- beqAddrFalse in *.
									repeat rewrite removeDupIdentity ; intuition.
			---	(* newBlockEntryAddr <> bentryaddr *)
					assert(HblockEq : isBE bentryaddr s = isBE bentryaddr s0).
					{ (* DUP *)
						unfold isBE.
						rewrite Hs.
						cbn. rewrite beqAddrTrue.
						destruct (beqAddr sceaddr bentryaddr) eqn:scebentry ; try(exfalso ; congruence).
						destruct (beqAddr newBlockEntryAddr sceaddr) eqn:newsce ; try(exfalso ; congruence).
						rewrite beqAddrTrue.
						cbn. rewrite newbentry.
						assert(HpdnewBNotEq : beqAddr pdinsertion newBlockEntryAddr = false) by intuition.
						rewrite HpdnewBNotEq. (*pd <> newblock*)
						rewrite <- beqAddrFalse in *.
						repeat rewrite removeDupIdentity ; intuition.
						cbn.
						destruct (beqAddr pdinsertion bentryaddr) eqn:pdbentry; try(exfalso ; congruence).
						rewrite <- DependentTypeLemmas.beqAddrTrue in pdbentry. congruence.
						rewrite <- beqAddrFalse in *.
						repeat rewrite removeDupIdentity ; intuition.
					}
					assert(Hblocks0 : isBE bentryaddr s0) by (rewrite HblockEq in * ; intuition).
					apply isBELookupEq in Hlookup. destruct Hlookup as [blockentry Hlookup].
					unfold bentryBlockIndex in *. rewrite Hlookup in *.
					destruct Hblockidx as [Hblockidx Hidxnb].
					specialize(Hcons0 bentryaddr blockidx Hblocks0).
					apply isBELookupEq in Hblocks0. destruct Hblocks0 as [blockentrys0 Hblocks0].
					rewrite Hblocks0 in *. intuition.
					assert(HlookupEq : lookup bentryaddr (memory s) beqAddr = lookup bentryaddr (memory s0) beqAddr).
					{ (* DUP *)
						rewrite Hs.
						cbn. rewrite beqAddrTrue.
						destruct (beqAddr sceaddr bentryaddr) eqn:scebentry ; try(exfalso ; congruence).
						destruct (beqAddr newBlockEntryAddr sceaddr) eqn:newsce ; try(exfalso ; congruence).
						rewrite beqAddrTrue.
						cbn. rewrite newbentry.
						assert(HpdnewBNotEq : beqAddr pdinsertion newBlockEntryAddr = false) by intuition.
						rewrite HpdnewBNotEq. (*pd <> newblock*)
						rewrite <- beqAddrFalse in *.
						repeat rewrite removeDupIdentity ; intuition.
						cbn.
						destruct (beqAddr pdinsertion bentryaddr) eqn:pdbentry; try(exfalso ; congruence).
						rewrite <- DependentTypeLemmas.beqAddrTrue in pdbentry. congruence.
						rewrite <- beqAddrFalse in *.
						repeat rewrite removeDupIdentity ; intuition.
					}
					assert(HlookupEq' : lookup bentryaddr (memory s0) beqAddr = Some (BE blockentry)).
					{ rewrite <- HlookupEq. intuition. }
					rewrite HlookupEq' in *. inversion Hblocks0.
					subst blockentrys0. intuition.
					(* DUP *)
					(* Check all values except newBlockEntryAddr *)
					destruct (beqAddr sceaddr (CPaddr (bentryaddr - blockidx))) eqn:beqsceks; try(exfalso ; congruence).
					*	(* sceaddr = (CPaddr (bentryaddr - blockidx)) *)
						rewrite <- DependentTypeLemmas.beqAddrTrue in beqsceks.
						rewrite <- beqsceks in *.
						unfold isSCE in *.
						unfold isKS in *.
						destruct (lookup sceaddr (memory s0) beqAddr) ; try(exfalso ; congruence).
						destruct v ; try(exfalso ; congruence).
					*	(* sceaddr <> (CPaddr (bentryaddr - blockidx)) *)
						destruct (beqAddr pdinsertion (CPaddr (bentryaddr - blockidx))) eqn:beqpdks; try(exfalso ; congruence).
						** (* pdinsertion = (CPaddr (bentryaddr - blockidx)) *)
							rewrite <- DependentTypeLemmas.beqAddrTrue in beqpdks.
							rewrite <- beqpdks in *.
							unfold isPDT in *.
							unfold isKS in *.
							destruct (lookup pdinsertion (memory s0) beqAddr) ; try(exfalso ; congruence).
							destruct v ; try(exfalso ; congruence).
					** (* pdinsertion <> (CPaddr (bentryaddr - blockidx)) *)
							destruct (beqAddr newBlockEntryAddr (CPaddr (bentryaddr - blockidx))) eqn:beqnewks ; try(exfalso ; congruence).
							*** (* newBlockEntryAddr = (CPaddr (bentryaddr - blockidx)) *)
									rewrite <- DependentTypeLemmas.beqAddrTrue in beqnewks.
									rewrite <- beqnewks in *.
									unfold isKS in *. rewrite HlookupnewBs. rewrite HlookupnewBs0 in *.
									rewrite Hblockindex. intuition.
							*** (* newBlockEntryAddr <> kernelstarts0 *)
									unfold isKS.
									rewrite Hs.
									cbn. rewrite beqAddrTrue.
									rewrite beqsceks.
									destruct (beqAddr newBlockEntryAddr sceaddr) eqn:newsce ; try(exfalso ; congruence).
									rewrite beqAddrTrue.
									cbn. rewrite beqnewks.
									rewrite <- beqAddrFalse in *.
									repeat rewrite removeDupIdentity ; intuition.
									destruct (beqAddr pdinsertion newBlockEntryAddr) eqn:pdnew ; try(exfalso ; congruence).
									rewrite <- DependentTypeLemmas.beqAddrTrue in pdnew. congruence.
									cbn.
									destruct (beqAddr pdinsertion (CPaddr (bentryaddr - blockidx))) eqn:pdks'; try(exfalso ; congruence).
									rewrite <- DependentTypeLemmas.beqAddrTrue in pdks'. congruence.
									rewrite <- beqAddrFalse in *.
									repeat rewrite removeDupIdentity ; intuition.
} (* end of KernelStructureStartFromBlockEntryAddrIsKS *)
split.
{ (* sh1InChildLocationIsBE s *)
	unfold sh1InChildLocationIsBE.
	intros sh1entryaddr sh1entry Hlookup Hsh1entryNotNull.

	assert(Hcons0 : sh1InChildLocationIsBE s0) by (unfold consistency in * ; intuition).
	unfold sh1InChildLocationIsBE in Hcons0.

	(* check all possible values for sh1entryaddr in the modified state s
			-> no entry modifications correspond to SH1Entry type
			(inChildLocation sh1entry) only possible value is NewBlockEntryAddr
			- = NewBlockEntryAddr -> isBE at s so OK
			- <> NewBlockEntryAddr -> leads to s0 -> OK
*)
	(* Check all values *)
	destruct (beqAddr sceaddr sh1entryaddr) eqn:beqscesh1entry; try(exfalso ; congruence).
	-	(* sceaddr = sh1entryaddr *)
		rewrite <- DependentTypeLemmas.beqAddrTrue in beqscesh1entry.
		rewrite <- beqscesh1entry in *.
		unfold isSCE in *.
		destruct (lookup sceaddr (memory s) beqAddr) ; try(exfalso ; congruence).
		destruct v ; try(exfalso ; congruence).
	-	(* sceaddr <> sh1entryaddr *)
		destruct (beqAddr pdinsertion sh1entryaddr) eqn:beqpdsh1entry; try(exfalso ; congruence).
		-- (* pdinsertion = sh1entryaddr *)
			rewrite <- DependentTypeLemmas.beqAddrTrue in beqpdsh1entry.
			rewrite <- beqpdsh1entry in *.
			destruct (lookup pdinsertion (memory s) beqAddr) ; try(exfalso ; congruence).
		-- (* pdinsertion <> sh1entryaddr *)
			destruct (beqAddr newBlockEntryAddr sh1entryaddr) eqn:newsh1entry ; try(exfalso ; congruence).
			--- (* newBlockEntryAddr = sh1entryaddr *)
					rewrite <- DependentTypeLemmas.beqAddrTrue in newsh1entry.
					rewrite <- newsh1entry in *.
					destruct (lookup newBlockEntryAddr (memory s) beqAddr) ; try(exfalso ; congruence).
			--- (* newBlockEntryAddr <> sh1entryaddr *)
					assert(HSHEEq : lookup sh1entryaddr (memory s) beqAddr = lookup sh1entryaddr (memory s0) beqAddr).
					{
						rewrite Hs.
						cbn. rewrite beqAddrTrue.
						rewrite beqscesh1entry.
						destruct (beqAddr newBlockEntryAddr sceaddr) eqn:newsce ; try(exfalso ; congruence).
						rewrite beqAddrTrue.
						cbn. rewrite newsh1entry.
						rewrite <- beqAddrFalse in *.
						repeat rewrite removeDupIdentity ; intuition.
						destruct (beqAddr pdinsertion newBlockEntryAddr) eqn:pdnew ; try(exfalso ; congruence).
						rewrite <- DependentTypeLemmas.beqAddrTrue in pdnew. congruence.
						cbn.
						destruct (beqAddr pdinsertion sh1entryaddr) eqn:pdsh1entry; try(exfalso ; congruence).
						rewrite <- DependentTypeLemmas.beqAddrTrue in pdsh1entry. congruence.
						rewrite <- beqAddrFalse in *.
						repeat rewrite removeDupIdentity ; intuition.
					}
					assert(Hlookups0 : lookup sh1entryaddr (memory s0) beqAddr = Some (SHE sh1entry))
						by (rewrite HSHEEq in * ; intuition).
					specialize(Hcons0 sh1entryaddr sh1entry Hlookups0 Hsh1entryNotNull).
					(* DUP *)
					(* Check all values *)
					destruct (beqAddr sceaddr (inChildLocation sh1entry)) eqn:beqscesh1; try(exfalso ; congruence).
					*	(* sceaddr = (inChildLocation sh1entry) *)
						rewrite <- DependentTypeLemmas.beqAddrTrue in beqscesh1.
						rewrite <- beqscesh1 in *.
						unfold isSCE in *.
						unfold isBE in *.
						destruct (lookup sceaddr (memory s0) beqAddr) ; try(exfalso ; congruence).
						destruct v ; try(exfalso ; congruence).
					*	(* sceaddr <> (inChildLocation sh1entry) *)
						destruct (beqAddr pdinsertion (inChildLocation sh1entry)) eqn:beqpdsh1; try(exfalso ; congruence).
						** (* pdinsertion = (inChildLocation sh1entry) *)
							rewrite <- DependentTypeLemmas.beqAddrTrue in beqpdsh1.
							rewrite <- beqpdsh1 in *.
							unfold isPDT in *.
							unfold isBE in *.
							destruct (lookup pdinsertion (memory s0) beqAddr) ; try(exfalso ; congruence).
							destruct v ; try(exfalso ; congruence).
					** (* pdinsertion <> (inChildLocation sh1entry) *)
							destruct (beqAddr newBlockEntryAddr (inChildLocation sh1entry)) eqn:beqnewsh1 ; try(exfalso ; congruence).
							*** (* newBlockEntryAddr = (inChildLocation sh1entry) *)
									rewrite <- DependentTypeLemmas.beqAddrTrue in beqnewsh1.
									rewrite <- beqnewsh1 in *.
									intuition.
							*** (* newBlockEntryAddr <> (inChildLocation sh1entry) *)
									unfold isBE.
									rewrite Hs.
									cbn. rewrite beqAddrTrue.
									rewrite beqscesh1.
									destruct (beqAddr newBlockEntryAddr sceaddr) eqn:newsce ; try(exfalso ; congruence).
									rewrite beqAddrTrue.
									cbn. rewrite beqnewsh1.
									rewrite <- beqAddrFalse in *.
									repeat rewrite removeDupIdentity ; intuition.
									destruct (beqAddr pdinsertion newBlockEntryAddr) eqn:pdnew ; try(exfalso ; congruence).
									rewrite <- DependentTypeLemmas.beqAddrTrue in pdnew. congruence.
									cbn.
									destruct (beqAddr pdinsertion (inChildLocation sh1entry)) eqn:pdks'; try(exfalso ; congruence).
									rewrite <- DependentTypeLemmas.beqAddrTrue in pdks'. congruence.
									rewrite <- beqAddrFalse in *.
									repeat rewrite removeDupIdentity ; intuition.
} (* end of sh1InChildLocationIsBE *)
split.
{ (* StructurePointerIsKS s *)
	unfold StructurePointerIsKS.
	intros pdentryaddr pdentry' Hlookup.

	assert(Hcons0 : StructurePointerIsKS s0) by (unfold consistency in * ; intuition).
	unfold StructurePointerIsKS in Hcons0.

(* check all possible values for pdentryaddr in the modified state s
			-> only possible is pdinsertion
		1) if pdentryaddr == pdinsertion :
				- the structure pointer can only be modified through NewBlockEntryAddr
					- structure pointer is newBlock -> still a KS at s0 -> OK
					- structure pointer is not modified -> leads to s0 -> OK
		2) if pdentryaddr <> pdinsertion :
				- relates to another PD than pdinsertion,
					the structure pointer can only be modified through NewBlockEntryAddr
					- structure pointer is newBlock
							- same proof as before -> still a KS at s0 -> OK
								but it means another PD can point to the same structure
								which shouldn't be possible (but may not be an issue for security)
					- structure pointer is not modified -> leads to s0 -> OK
*)
	(* Check all values except pdinsertion*)
	destruct (beqAddr sceaddr pdentryaddr) eqn:beqscepdentry; try(exfalso ; congruence).
	-	(* sceaddr = pdentryaddr *)
		rewrite <- DependentTypeLemmas.beqAddrTrue in beqscepdentry.
		rewrite <- beqscepdentry in *.
		unfold isSCE in *.
		rewrite Hlookup in *.
		exfalso ; congruence.
	-	(* sceaddr <> pdentryaddr *)
			destruct (beqAddr newBlockEntryAddr pdentryaddr) eqn:newpdentry ; try(exfalso ; congruence).
			-- (* newBlockEntryAddr = pdentryaddr *)
					rewrite <- DependentTypeLemmas.beqAddrTrue in newpdentry.
					rewrite <- newpdentry in *.
					unfold isBE in *.
					rewrite Hlookup in *.
					exfalso ; congruence.
			-- (* newBlockEntryAddr <> pdentryaddr *)
				destruct (beqAddr pdinsertion pdentryaddr) eqn:beqpdpdentry; try(exfalso ; congruence).
				--- (* pdinsertion = pdentryaddr *)
					rewrite <- DependentTypeLemmas.beqAddrTrue in beqpdpdentry.
					rewrite <- beqpdpdentry in *.
					assert(HpdentryEq : pdentry1 = pdentry').
					{ rewrite Hpdinsertions in Hlookup. inversion Hlookup. trivial. }
					subst pdentry'.
					specialize(Hcons0 pdinsertion pdentry Hpdinsertions0).
					assert(HstructureEq : (structure pdentry1) = (structure pdentry)).
					{ subst pdentry1. subst pdentry0.  simpl. trivial. }
					rewrite HstructureEq.
					(* Check all values for structure pdentry except newBlockEntryAddr *)
					destruct (beqAddr sceaddr (structure pdentry)) eqn:beqsceptn; try(exfalso ; congruence).
					*	(* sceaddr = (structure pdentry) *)
						rewrite <- DependentTypeLemmas.beqAddrTrue in beqsceptn.
						rewrite <- beqsceptn in *.
						unfold isSCE in *.
						unfold isKS in *.
						destruct (lookup sceaddr (memory s0) beqAddr) ; try(exfalso ; congruence).
						destruct v ; try(exfalso ; congruence).
					*	(* sceaddr <> (structure pdentry) *)
						destruct (beqAddr pdinsertion (structure pdentry)) eqn:beqpdptn; try(exfalso ; congruence).
						** (* pdinsertion = (structure pdentry) *)
							rewrite <- DependentTypeLemmas.beqAddrTrue in beqpdptn.
							rewrite <- beqpdptn in *.
							unfold isPDT in *.
							unfold isKS in *.
							destruct (lookup pdinsertion (memory s0) beqAddr) ; try(exfalso ; congruence).
							destruct v ; try(exfalso ; congruence).
						** (* pdinsertion <> (structure pdentry) *)
							destruct (beqAddr newBlockEntryAddr (structure pdentry)) eqn:beqnewptn ; try(exfalso ; congruence).
							*** (* newBlockEntryAddr = (structure pdentry) *)
									rewrite <- DependentTypeLemmas.beqAddrTrue in beqnewptn.
									rewrite <- beqnewptn in *.
									unfold isKS in *.
									rewrite HlookupnewBs. rewrite HlookupnewBs0 in *.
									rewrite Hblockindex. trivial.
							*** (* newBlockEntryAddr <> (structure pdentry) *)
									unfold isKS.
									rewrite Hs.
									cbn. rewrite beqAddrTrue.
									rewrite beqsceptn.
									destruct (beqAddr newBlockEntryAddr sceaddr) eqn:newsce ; try(exfalso ; congruence).
									rewrite beqAddrTrue.
									cbn. rewrite beqnewptn.
									rewrite <- beqAddrFalse in *.
									repeat rewrite removeDupIdentity ; intuition.
									destruct (beqAddr pdinsertion newBlockEntryAddr) eqn:pdnew ; try(exfalso ; congruence).
									rewrite <- DependentTypeLemmas.beqAddrTrue in pdnew. congruence.
									cbn.
									destruct (beqAddr pdinsertion (structure pdentry)) eqn:pdks'; try(exfalso ; congruence).
									rewrite <- DependentTypeLemmas.beqAddrTrue in pdks'. congruence.
									rewrite <- beqAddrFalse in *.
									repeat rewrite removeDupIdentity ; intuition.
				--- (* pdinsertion <> pdentryaddr *)
						(* DUP *)
						assert(HPDEq : lookup pdentryaddr (memory s) beqAddr = lookup pdentryaddr (memory s0) beqAddr).
						{
							rewrite Hs.
							cbn. rewrite beqAddrTrue.
							rewrite beqscepdentry.
							destruct (beqAddr newBlockEntryAddr sceaddr) eqn:newsce ; try(exfalso ; congruence).
							rewrite beqAddrTrue.
							cbn. rewrite newpdentry.
							rewrite <- beqAddrFalse in *.
							repeat rewrite removeDupIdentity ; intuition.
							destruct (beqAddr pdinsertion newBlockEntryAddr) eqn:pdnew ; try(exfalso ; congruence).
							rewrite <- DependentTypeLemmas.beqAddrTrue in pdnew. congruence.
							cbn.
							destruct (beqAddr pdinsertion pdentryaddr) eqn:pdpdentry; try(exfalso ; congruence).
							rewrite <- DependentTypeLemmas.beqAddrTrue in pdpdentry. congruence.
							rewrite <- beqAddrFalse in *.
							repeat rewrite removeDupIdentity ; intuition.
						}
						assert(Hlookups0 : lookup pdentryaddr (memory s0) beqAddr = Some (PDT pdentry'))
							by (rewrite HPDEq in * ; intuition).
						specialize(Hcons0 pdentryaddr pdentry' Hlookups0).
						(* Check all values *)
						destruct (beqAddr sceaddr (structure pdentry')) eqn:beqsceptn; try(exfalso ; congruence).
						*	(* sceaddr = (inChildLocation sh1entry) *)
							rewrite <- DependentTypeLemmas.beqAddrTrue in beqsceptn.
							rewrite <- beqsceptn in *.
							unfold isSCE in *.
							unfold isKS in *.
							destruct (lookup sceaddr (memory s0) beqAddr) ; try(exfalso ; congruence).
							destruct v ; try(exfalso ; congruence).
						*	(* sceaddr <> (structure pdentry') *)
							destruct (beqAddr pdinsertion (structure pdentry')) eqn:beqpdptn ; try(exfalso ; congruence).
							** (* pdinsertion = (inChildLocation sh1entry) *)
								rewrite <- DependentTypeLemmas.beqAddrTrue in beqpdptn.
								rewrite <- beqpdptn in *.
								unfold isPDT in *.
								unfold isKS in *.
								destruct (lookup pdinsertion (memory s0) beqAddr) ; try(exfalso ; congruence).
								destruct v ; try(exfalso ; congruence).
						** (* pdinsertion <> (structure pdentry') *)
								destruct (beqAddr newBlockEntryAddr (structure pdentry')) eqn:beqnewptn ; try(exfalso ; congruence).
								*** (* newBlockEntryAddr = (structure pdentry') *)
										rewrite <- DependentTypeLemmas.beqAddrTrue in beqnewptn.
										rewrite <- beqnewptn in *.
										unfold isKS in *.
										rewrite HlookupnewBs. rewrite HlookupnewBs0 in *.
										rewrite Hblockindex. trivial.
								*** (* newBlockEntryAddr <> (inChildLocation sh1entry) *)
										unfold isKS.
										rewrite Hs.
										cbn. rewrite beqAddrTrue.
										rewrite beqsceptn.
										destruct (beqAddr newBlockEntryAddr sceaddr) eqn:newsce ; try(exfalso ; congruence).
										rewrite beqAddrTrue.
										cbn. rewrite beqnewptn.
										rewrite <- beqAddrFalse in *.
										repeat rewrite removeDupIdentity ; intuition.
										destruct (beqAddr pdinsertion newBlockEntryAddr) eqn:pdnew ; try(exfalso ; congruence).
										rewrite <- DependentTypeLemmas.beqAddrTrue in pdnew. congruence.
										cbn.
										destruct (beqAddr pdinsertion (structure pdentry')) eqn:pdpd; try(exfalso ; congruence).
										rewrite <- DependentTypeLemmas.beqAddrTrue in pdpd. congruence.
										rewrite <- beqAddrFalse in *.
										repeat rewrite removeDupIdentity ; intuition.
} (* end of StructurePointerIsKS *)
split.
{ (* NextKSIsKS s *)
	unfold NextKSIsKS.
	intros ksaddr nextksaddr next HKS Hnextksaddr Hnext HnextNotNull.

	assert(Hcons0 : NextKSIsKS s0) by (unfold consistency in * ; intuition).
	unfold NextKSIsKS in Hcons0.

	(* check all possible values for ksaddr in the modified state s
			-> only possible is newBlockEntryAddr
		but nextks and nextksaddr never modified
			-> leads to s0, even if nextksaddr == newB -> OK
*)
	(* Check all values except newBlockEntryAddr *)
	destruct (beqAddr sceaddr ksaddr) eqn:beqsceks; try(exfalso ; congruence).
	-	(* sceaddr = ksaddr *)
		rewrite <- DependentTypeLemmas.beqAddrTrue in beqsceks.
		rewrite <- beqsceks in *.
		unfold isSCE in *.
		unfold isKS in *.
		destruct (lookup sceaddr (memory s) beqAddr) ; try(exfalso ; congruence).
		destruct v ; try(exfalso ; congruence).
	-	(* sceaddr <> ksaddr *)
		destruct (beqAddr pdinsertion ksaddr) eqn:beqpdks; try(exfalso ; congruence).
		-- (* pdinsertion = ksaddr *)
			rewrite <- DependentTypeLemmas.beqAddrTrue in beqpdks.
			rewrite <- beqpdks in *.
			unfold isPDT in *.
			unfold isKS in *.
			destruct (lookup pdinsertion (memory s) beqAddr) ; try(exfalso ; congruence).
			destruct v ; try(exfalso ; congruence).
		-- (* pdinsertion <> ksaddr *)
				(* COPY from BlocksRangeFromKernelStartIsBE *)
				assert(HKSEq : isKS ksaddr s = isKS ksaddr s0).
				{
					unfold isKS.
					destruct (beqAddr newBlockEntryAddr ksaddr) eqn:newks ; try(exfalso ; congruence).
					--- (* newBlockEntryAddr = ksaddr *)
							rewrite <- DependentTypeLemmas.beqAddrTrue in newks.
							rewrite <- newks in *.
							rewrite HlookupnewBs0. rewrite Hs.
							cbn. rewrite beqAddrTrue.
							rewrite beqsceks.
							rewrite beqAddrSym in beqsceks.
							rewrite beqsceks.
							cbn. rewrite beqAddrTrue.
							f_equal. rewrite <- Hblockindex7. rewrite <- Hblockindex6.
							rewrite <- Hblockindex5. rewrite <- Hblockindex4.
							rewrite <- Hblockindex3. rewrite <- Hblockindex2.
							unfold CBlockEntry.
							destruct(lt_dec (blockindex bentry5) kernelStructureEntriesNb) eqn:Hdec ; try(exfalso ; congruence).
							intuition.
							destruct blockentry_d. destruct bentry5.
							intuition.
					--- (* newBlockEntryAddr <> ksaddr *)
							rewrite Hs. cbn.
							rewrite beqAddrTrue.
							rewrite beqsceks.
							assert(HnewBsceNotEq : beqAddr newBlockEntryAddr sceaddr = false) by intuition.
							rewrite HnewBsceNotEq. (*newBlock <> sce *)
							assert(HpdnewBNotEq : beqAddr pdinsertion newBlockEntryAddr = false) by intuition.
							rewrite HpdnewBNotEq. (*pd <> newblock*)
							cbn. rewrite beqAddrTrue.
							rewrite newks. rewrite HpdnewBNotEq.
							rewrite <- beqAddrFalse in *.
							repeat rewrite removeDupIdentity; intuition.
							cbn.
							destruct (beqAddr pdinsertion ksaddr) eqn:Hf ; try (exfalso ; congruence).
							rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
							repeat rewrite removeDupIdentity; intuition.
					}
				assert(HKSs0 : isKS ksaddr s0) by (rewrite HKSEq in * ; intuition).
				assert(HnextaddrEq : nextKSAddr ksaddr nextksaddr s = nextKSAddr ksaddr nextksaddr s0).
				{
					unfold nextKSAddr.
					destruct (beqAddr newBlockEntryAddr ksaddr) eqn:newks ; try(exfalso ; congruence).
					--- (* newBlockEntryAddr = ksaddr *)
							rewrite <- DependentTypeLemmas.beqAddrTrue in newks.
							rewrite <- newks in *.
							rewrite HlookupnewBs0. rewrite Hs.
							cbn. rewrite beqAddrTrue.
							rewrite beqsceks.
							rewrite beqAddrSym in beqsceks.
							rewrite beqsceks.
							cbn. rewrite beqAddrTrue. reflexivity.
					--- (* newBlockEntryAddr <> ksaddr *)
							rewrite Hs. cbn.
							rewrite beqAddrTrue.
							rewrite beqsceks.
							assert(HnewBsceNotEq : beqAddr newBlockEntryAddr sceaddr = false) by intuition.
							rewrite HnewBsceNotEq. (*newBlock <> sce *)
							assert(HpdnewBNotEq : beqAddr pdinsertion newBlockEntryAddr = false) by intuition.
							rewrite HpdnewBNotEq. (*pd <> newblock*)
							cbn. rewrite beqAddrTrue.
							rewrite newks. rewrite HpdnewBNotEq.
							rewrite <- beqAddrFalse in *.
							repeat rewrite removeDupIdentity; intuition.
							cbn.
							destruct (beqAddr pdinsertion ksaddr) eqn:Hf ; try (exfalso ; congruence).
							rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
							repeat rewrite removeDupIdentity; intuition.
				}
				assert(Hnextaddrs0 : nextKSAddr ksaddr nextksaddr s0) by (rewrite HnextaddrEq in * ; intuition).
				assert(Hnextaddr : nextksaddr = CPaddr (ksaddr + nextoffset)).
				{
					unfold nextKSAddr in *. unfold isKS in *.
					destruct (lookup ksaddr (memory s) beqAddr) eqn:Hks ; try(exfalso ; congruence).
					destruct v eqn:Hv ; try(exfalso ; congruence).
					intuition.
				}
				assert(HnextEq : nextKSentry nextksaddr next s = nextKSentry nextksaddr next s0).
				{
					unfold nextKSentry.
					destruct (beqAddr newBlockEntryAddr nextksaddr) eqn:newks ; try(exfalso ; congruence).
					--- (* newBlockEntryAddr = nextksaddr *)
							rewrite <- DependentTypeLemmas.beqAddrTrue in newks.
							rewrite <- newks in *.
							rewrite HlookupnewBs0. rewrite Hs.
							cbn. rewrite beqAddrTrue.
							assert(HnewBsceNotEq : beqAddr newBlockEntryAddr sceaddr = false) by intuition.
							rewrite HnewBsceNotEq. (*newBlock <> sce *)
							rewrite beqAddrSym in HnewBsceNotEq.
							rewrite HnewBsceNotEq.
							cbn. rewrite beqAddrTrue.
							reflexivity.
					--- (* newBlockEntryAddr <> ksaddr *)
							rewrite Hs. cbn.
							rewrite beqAddrTrue.
							assert(Hcons1 : NextKSOffsetIsPADDR s0) by (unfold consistency in * ; intuition).
							unfold NextKSOffsetIsPADDR in *.
							specialize(Hcons1 ksaddr nextksaddr HKSs0 Hnextaddrs0).
							destruct (beqAddr sceaddr nextksaddr) eqn:beqscenextaddr ; try(exfalso;congruence).
							* rewrite <- DependentTypeLemmas.beqAddrTrue in beqscenextaddr.
								rewrite beqscenextaddr in *.
								unfold isSCE in *.
								unfold isPADDR in *.
								destruct(lookup nextksaddr (memory s0) beqAddr) eqn:Hf ; try(exfalso ; congruence).
								destruct v eqn:Hv ; try(exfalso ; congruence).
							* assert(HnewBsceNotEq : beqAddr newBlockEntryAddr sceaddr = false) by intuition.
								rewrite HnewBsceNotEq. (*newBlock <> sce *)
								assert(HpdnewBNotEq : beqAddr pdinsertion newBlockEntryAddr = false) by intuition.
								rewrite HpdnewBNotEq. (*pd <> newblock*)
								cbn. rewrite beqAddrTrue.
								rewrite newks. rewrite HpdnewBNotEq.
								rewrite <- beqAddrFalse in *.
								repeat rewrite removeDupIdentity; intuition.
								cbn.
								destruct (beqAddr pdinsertion nextksaddr) eqn:beqpdnextaddr ; try(exfalso;congruence).
								**	rewrite <- DependentTypeLemmas.beqAddrTrue in beqpdnextaddr.
										rewrite beqpdnextaddr in *.
										unfold isPDT in *.
										unfold isPADDR in *.
										destruct(lookup nextksaddr (memory s0) beqAddr) eqn:Hf ; try(exfalso ; congruence).
										destruct v eqn:Hv ; try(exfalso ; congruence).
								** 	rewrite <- beqAddrFalse in *.
										repeat rewrite removeDupIdentity; intuition.
				}
				assert(Hnexts0 : nextKSentry nextksaddr next s0) by (rewrite HnextEq in * ; intuition).
				(* specialize for ksaddr *)
				specialize(Hcons0 ksaddr nextksaddr next HKSs0 Hnextaddrs0 Hnexts0 HnextNotNull).
				(* check all values *)
				destruct (beqAddr sceaddr next) eqn:beqscenext; try(exfalso ; congruence).
				+ (* sceaddr = nextksaddr *)
					rewrite <- DependentTypeLemmas.beqAddrTrue in beqscenext.
					rewrite <- beqscenext in *.
					unfold isSCE in *.
					unfold isKS in *.
					destruct (lookup sceaddr (memory s0) beqAddr) ; try(exfalso ; congruence).
					destruct v ; try(exfalso ; congruence).
				+ (* sceaddr <> nextksaddr *)
					destruct (beqAddr pdinsertion next) eqn:beqpdnext; try(exfalso ; congruence).
					++ (* pdinsertion = nextksaddr *)
							rewrite <- DependentTypeLemmas.beqAddrTrue in beqpdnext.
							rewrite <- beqpdnext in *.
							unfold isPDT in *.
							unfold isKS in *.
							destruct (lookup pdinsertion (memory s0) beqAddr) ; try(exfalso ; congruence).
							destruct v ; try(exfalso ; congruence).
					++ (* pdinsertion <> nextksaddr *)
						destruct (beqAddr newBlockEntryAddr next) eqn:beqnewnext; try(exfalso ; congruence).
						+++ (* pdinsertion = nextksaddr *)
								rewrite <- DependentTypeLemmas.beqAddrTrue in beqnewnext.
								rewrite <- beqnewnext in *.
								unfold isKS in *. rewrite HlookupnewBs0 in *. rewrite HlookupnewBs in *.
								rewrite Hblockindex. intuition.
						+++ (* pdinsertion <> nextksaddr *)
									unfold isKS.
									rewrite Hs.
									cbn. rewrite beqAddrTrue.
									rewrite beqscenext.
									assert(HnewBsceNotEq : beqAddr newBlockEntryAddr sceaddr = false) by intuition.
									rewrite HnewBsceNotEq. (*newBlock <> sce *)
									assert(HpdnewBNotEq : beqAddr pdinsertion newBlockEntryAddr = false) by intuition.
									rewrite HpdnewBNotEq. (*pd <> newblock*)
									cbn.
									rewrite beqnewnext.
									rewrite beqAddrTrue.
									rewrite <- beqAddrFalse in *.
									repeat rewrite removeDupIdentity ; intuition.
									destruct (beqAddr pdinsertion newBlockEntryAddr) eqn:Hf ; try(exfalso ; congruence).
									rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
									cbn.
									destruct (beqAddr pdinsertion next) eqn:Hff ; try(exfalso ; congruence).
									rewrite <- DependentTypeLemmas.beqAddrTrue in Hff. congruence.
									rewrite <- beqAddrFalse in *.
									repeat rewrite removeDupIdentity ; intuition.
} (* end of NextKSIsKS *)
split.
{ (* NextKSOffsetIsPADDR s *)
	unfold NextKSOffsetIsPADDR.
	intros ksaddr nextksaddr HKS Hnextksaddr.

	assert(Hcons0 : NextKSOffsetIsPADDR s0) by (unfold consistency in * ; intuition).
	unfold NextKSOffsetIsPADDR in Hcons0.

	(* check all possible values for ksaddr in the modified state s
			-> only possible is newBlockEntryAddr
		but nextks and nextksaddr never modified
			-> values for nextksaddr leads to s0 cause nothing matches -> OK
*)
	(* DUP of NextKSIsKS *)
	(* Check all values except newBlockEntryAddr *)
	destruct (beqAddr sceaddr ksaddr) eqn:beqsceks; try(exfalso ; congruence).
	-	(* sceaddr = ksaddr *)
		rewrite <- DependentTypeLemmas.beqAddrTrue in beqsceks.
		rewrite <- beqsceks in *.
		unfold isSCE in *.
		unfold isKS in *.
		destruct (lookup sceaddr (memory s) beqAddr) ; try(exfalso ; congruence).
		destruct v ; try(exfalso ; congruence).
	-	(* sceaddr <> ksaddr *)
		destruct (beqAddr pdinsertion ksaddr) eqn:beqpdks; try(exfalso ; congruence).
		-- (* pdinsertion = ksaddr *)
			rewrite <- DependentTypeLemmas.beqAddrTrue in beqpdks.
			rewrite <- beqpdks in *.
			unfold isPDT in *.
			unfold isKS in *.
			destruct (lookup pdinsertion (memory s) beqAddr) ; try(exfalso ; congruence).
			destruct v ; try(exfalso ; congruence).
		-- (* pdinsertion <> ksaddr *)
				(* COPY from BlocksRangeFromKernelStartIsBE *)
				assert(HKSEq : isKS ksaddr s = isKS ksaddr s0).
				{
					unfold isKS.
					destruct (beqAddr newBlockEntryAddr ksaddr) eqn:newks ; try(exfalso ; congruence).
					--- (* newBlockEntryAddr = ksaddr *)
							rewrite <- DependentTypeLemmas.beqAddrTrue in newks.
							rewrite <- newks in *.
							rewrite HlookupnewBs0. rewrite Hs.
							cbn. rewrite beqAddrTrue.
							rewrite beqsceks.
							rewrite beqAddrSym in beqsceks.
							rewrite beqsceks.
							cbn. rewrite beqAddrTrue.
							f_equal. rewrite <- Hblockindex7. rewrite <- Hblockindex6.
							rewrite <- Hblockindex5. rewrite <- Hblockindex4.
							rewrite <- Hblockindex3. rewrite <- Hblockindex2.
							unfold CBlockEntry.
							destruct(lt_dec (blockindex bentry5) kernelStructureEntriesNb) eqn:Hdec ; try(exfalso ; congruence).
							intuition.
							destruct blockentry_d. destruct bentry5.
							intuition.
					--- (* newBlockEntryAddr <> ksaddr *)
							rewrite Hs. cbn.
							rewrite beqAddrTrue.
							rewrite beqsceks.
							assert(HnewBsceNotEq : beqAddr newBlockEntryAddr sceaddr = false) by intuition.
							rewrite HnewBsceNotEq. (*newBlock <> sce *)
							assert(HpdnewBNotEq : beqAddr pdinsertion newBlockEntryAddr = false) by intuition.
							rewrite HpdnewBNotEq. (*pd <> newblock*)
							cbn. rewrite beqAddrTrue.
							rewrite newks. rewrite HpdnewBNotEq.
							rewrite <- beqAddrFalse in *.
							repeat rewrite removeDupIdentity; intuition.
							cbn.
							destruct (beqAddr pdinsertion ksaddr) eqn:Hf ; try (exfalso ; congruence).
							rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
							repeat rewrite removeDupIdentity; intuition.
					}
				assert(HKSs0 : isKS ksaddr s0) by (rewrite HKSEq in * ; intuition).
				assert(HnextaddrEq : nextKSAddr ksaddr nextksaddr s = nextKSAddr ksaddr nextksaddr s0).
				{
					unfold nextKSAddr.
					destruct (beqAddr newBlockEntryAddr ksaddr) eqn:newks ; try(exfalso ; congruence).
					--- (* newBlockEntryAddr = ksaddr *)
							rewrite <- DependentTypeLemmas.beqAddrTrue in newks.
							rewrite <- newks in *.
							rewrite HlookupnewBs0. rewrite Hs.
							cbn. rewrite beqAddrTrue.
							rewrite beqsceks.
							rewrite beqAddrSym in beqsceks.
							rewrite beqsceks.
							cbn. rewrite beqAddrTrue. reflexivity.
					--- (* newBlockEntryAddr <> ksaddr *)
							rewrite Hs. cbn.
							rewrite beqAddrTrue.
							rewrite beqsceks.
							assert(HnewBsceNotEq : beqAddr newBlockEntryAddr sceaddr = false) by intuition.
							rewrite HnewBsceNotEq. (*newBlock <> sce *)
							assert(HpdnewBNotEq : beqAddr pdinsertion newBlockEntryAddr = false) by intuition.
							rewrite HpdnewBNotEq. (*pd <> newblock*)
							cbn. rewrite beqAddrTrue.
							rewrite newks. rewrite HpdnewBNotEq.
							rewrite <- beqAddrFalse in *.
							repeat rewrite removeDupIdentity; intuition.
							cbn.
							destruct (beqAddr pdinsertion ksaddr) eqn:Hf ; try (exfalso ; congruence).
							rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
							repeat rewrite removeDupIdentity; intuition.
				}
				assert(Hnextaddrs0 : nextKSAddr ksaddr nextksaddr s0) by (rewrite HnextaddrEq in * ; intuition).
				assert(Hnextaddr : nextksaddr = CPaddr (ksaddr + nextoffset)).
				{
					unfold nextKSAddr in *. unfold isKS in *.
					destruct (lookup ksaddr (memory s) beqAddr) eqn:Hks ; try(exfalso ; congruence).
					destruct v eqn:Hv ; try(exfalso ; congruence).
					intuition.
				}
				(* specialize for ksaddr *)
				specialize(Hcons0 ksaddr nextksaddr HKSs0 Hnextaddrs0).
				(* check all values *)
				destruct (beqAddr sceaddr nextksaddr) eqn:beqscenext; try(exfalso ; congruence).
				+ (* sceaddr = nextksaddr *)
					rewrite <- DependentTypeLemmas.beqAddrTrue in beqscenext.
					rewrite <- beqscenext in *.
					unfold isSCE in *.
					unfold isPADDR in *.
					destruct (lookup sceaddr (memory s0) beqAddr) ; try(exfalso ; congruence).
					destruct v ; try(exfalso ; congruence).
				+ (* sceaddr <> nextksaddr *)
					destruct (beqAddr pdinsertion nextksaddr) eqn:beqpdnext; try(exfalso ; congruence).
					++ (* pdinsertion = nextksaddr *)
							rewrite <- DependentTypeLemmas.beqAddrTrue in beqpdnext.
							rewrite <- beqpdnext in *.
							unfold isPDT in *.
							unfold isPADDR in *.
							destruct (lookup pdinsertion (memory s0) beqAddr) ; try(exfalso ; congruence).
							destruct v ; try(exfalso ; congruence).
					++ (* pdinsertion <> nextksaddr *)
						destruct (beqAddr newBlockEntryAddr nextksaddr) eqn:beqnewnext; try(exfalso ; congruence).
						+++ (* pdinsertion = nextksaddr *)
								rewrite <- DependentTypeLemmas.beqAddrTrue in beqnewnext.
								rewrite <- beqnewnext in *.
								unfold isPADDR in *.
								destruct (lookup newBlockEntryAddr (memory s0) beqAddr) ; try(exfalso ; congruence).
								destruct v ; try(exfalso ; congruence).
						+++ (* pdinsertion <> nextksaddr *)
									unfold isPADDR.
									rewrite Hs.
									cbn. rewrite beqAddrTrue.
									rewrite beqscenext.
									assert(HnewBsceNotEq : beqAddr newBlockEntryAddr sceaddr = false) by intuition.
									rewrite HnewBsceNotEq. (*newBlock <> sce *)
									assert(HpdnewBNotEq : beqAddr pdinsertion newBlockEntryAddr = false) by intuition.
									rewrite HpdnewBNotEq. (*pd <> newblock*)
									cbn.
									rewrite beqnewnext.
									rewrite beqAddrTrue.
									rewrite <- beqAddrFalse in *.
									repeat rewrite removeDupIdentity ; intuition.
									destruct (beqAddr pdinsertion newBlockEntryAddr) eqn:Hf ; try(exfalso ; congruence).
									rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
									cbn.
									destruct (beqAddr pdinsertion nextksaddr) eqn:Hff ; try(exfalso ; congruence).
									rewrite <- DependentTypeLemmas.beqAddrTrue in Hff. congruence.
									rewrite <- beqAddrFalse in *.
									repeat rewrite removeDupIdentity ; intuition.
} (* end of NextKSOffsetIsPADDR *)
split.
{ (* NoDupInFreeSlotsList s *)
	unfold NoDupInFreeSlotsList.
	intros pd entrypd Hlookuppd.

	assert(Hcons0 : NoDupInFreeSlotsList s0) by (unfold consistency in * ; intuition).
	unfold NoDupInFreeSlotsList in Hcons0.

	(* check all possible values for pd in the modified state s
			-> only possible is pdinsertion, we already proved we had no Dup
		if it is another pd, we must prove there are still noDup in that list
			by showing this list was never modified
			-> compute the list at each modified state and check not changed from s0 -> OK
*)
	(* Check all values except pdinsertion *)
	destruct (beqAddr sceaddr pd) eqn:beqscepd; try(exfalso ; congruence).
	-	(* sceaddr = pd *)
		rewrite <- DependentTypeLemmas.beqAddrTrue in beqscepd.
		rewrite <- beqscepd in *.
		unfold isSCE in *.
		destruct (lookup sceaddr (memory s) beqAddr) ; try(exfalso ; congruence).
		destruct v ; try(exfalso ; congruence).
	-	(* sceaddr <> pd *)
		destruct (beqAddr newBlockEntryAddr pd) eqn:beqnewpd ; try(exfalso ; congruence).
		-- (* newBlockEntryAddr = pd *)
				rewrite <- DependentTypeLemmas.beqAddrTrue in beqnewpd.
				rewrite <- beqnewpd in *.
				unfold isBE in *.
				destruct (lookup newBlockEntryAddr (memory s) beqAddr) ; try(exfalso ; congruence).
		-- (* newBlockEntryAddr <> pd *)
				destruct (beqAddr pdinsertion pd) eqn:beqpdpd; try(exfalso ; congruence).
				--- (* pdinsertion = pd *)
						(* case already proved step by step *)
						rewrite <- DependentTypeLemmas.beqAddrTrue in beqpdpd.
						rewrite <- beqpdpd in *.
						specialize(Hcons0 pdinsertion pdentry Hpdinsertions0).
						destruct Hcons0 as [listoption (Hoptionlist & (Hwellformed & HNoDup))].
						unfold getFreeSlotsList in *. rewrite Hpdinsertions0 in *.
						rewrite Hpdinsertions.
						rewrite HnewFirstFree.
						rewrite <- HnewB in *.
						destruct(beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
						rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
						destruct H31 as [Hoptionlists (olds & (n0 & (n1 & (n2 & (nbleft & Hfreeslotsolds)))))].
						exists Hoptionlists.
						destruct (beqAddr newFirstFreeSlotAddr nullAddr) eqn:beqfirstnull; try(exfalso ; congruence).
							---- (* newFirstFreeSlotAddr = nullAddr *)
										rewrite <- DependentTypeLemmas.beqAddrTrue in beqfirstnull.
										rewrite beqfirstnull in *.
										intuition.
										assert(Hoption :  Hoptionlists = getFreeSlotsListRec n0 nullAddr s0 nbleft) by intuition.
										rewrite FreeSlotsListRec_unroll in Hoption.
										unfold getFreeSlotsListAux in Hoption.
										destruct n0.
										rewrite Hoption in *. cbn in *. congruence.
										destruct (StateLib.Index.ltb nbleft zero).
										rewrite Hoption in *. cbn in *. congruence.
										assert(HNullAddrExistss0 : nullAddrExists s0)
												by (unfold consistency in * ; intuition).
										unfold nullAddrExists in *.
										unfold isPADDR in *.
										destruct (lookup nullAddr (memory s0) beqAddr) ; try(exfalso ; congruence).
										destruct v ; try(exfalso ; congruence).
										destruct (beqAddr p nullAddr).
										rewrite Hoption in *. cbn in *. congruence.
										rewrite Hoption in *. cbn in *. congruence.
							---- (* newFirstFreeSlotAddr <> nullAddr *)
										intuition. subst pdentry1. (* pdentry1 *) cbn.
										assert(HpredNbLeftEq : predCurrentNbFreeSlots = nbleft).
										{ subst nbleft. unfold StateLib.Index.pred in *.
											destruct (gt_dec currnbfreeslots 0) ; intuition.
											inversion H1. (* Some ... = Some predCurrentNbFreeSlots *)
											unfold CIndex.
											assert(HnbLtmaxIdx : currnbfreeslots - 1 < maxIdx).
											{ 
												assert(HcurrLtmaxIdx : currnbfreeslots <= maxIdx).
												{ intuition. apply IdxLtMaxIdx. }
												lia.
											}
											destruct (le_dec (currnbfreeslots - 1) maxIdx) ; intuition.
											f_equal. apply proof_irrelevance.
										}
										rewrite HpredNbLeftEq.
										rewrite <- H34. (* n2 s = Hoptionlist *)
										eapply getFreeSlotsListRecEqN ; intuition.
					--- (* pdinsertion <> pd *)
							(* similarly, we must prove the list has not changed by recomputing each
									intermediate steps and check at that time *)
							specialize(Hcons0 pd).
							unfold getFreeSlotsList.
							destruct (lookup pd (memory s) beqAddr) eqn:Hpdentry ; try(exfalso ; congruence).
							destruct v eqn:Hv ; try(exfalso ; congruence).
							assert(HlookupEq : lookup pd (memory s) beqAddr = lookup pd (memory s0) beqAddr).
							{	(* check all values *)
								destruct (beqAddr sceaddr pd) eqn:beqscepdentry; try(exfalso ; congruence).
								(* sceaddr <> pd *)
								destruct (beqAddr newBlockEntryAddr pd) eqn:newpdentry ; try(exfalso ; congruence).
								(* newBlockEntryAddr <> pd *)
								destruct (beqAddr pdinsertion pd) eqn:beqpdpdentry; try(exfalso ; congruence).
								(* pdinsertion <> pd *)
								rewrite Hs.
								cbn. rewrite beqAddrTrue.
								rewrite beqscepdentry.
								assert(HnewBsceNotEq : beqAddr newBlockEntryAddr sceaddr = false) by intuition.
								rewrite HnewBsceNotEq. (*newBlock <> sce *)
								assert(HpdnewBNotEq : beqAddr pdinsertion newBlockEntryAddr = false) by intuition.
								rewrite HpdnewBNotEq. (*pd <> newblock*)
								cbn.
								rewrite newpdentry.
								rewrite beqAddrTrue.
								rewrite <- beqAddrFalse in *.
								repeat rewrite removeDupIdentity ; intuition.
								destruct (beqAddr pdinsertion newBlockEntryAddr) eqn:Hf ; try(exfalso ; congruence).
								rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
								cbn.
								destruct (beqAddr pdinsertion pd) eqn:Hff ; try(exfalso ; congruence).
								rewrite <- DependentTypeLemmas.beqAddrTrue in Hff. congruence.
								rewrite <- beqAddrFalse in *.
								repeat rewrite removeDupIdentity ; intuition.
							}
							assert(Hlookups0: lookup pd (memory s0) beqAddr = Some (PDT p)).
							rewrite <- HlookupEq. intuition.
							specialize (Hcons0 p Hlookups0).
							unfold getFreeSlotsList in *. rewrite Hlookups0 in *.
							destruct (beqAddr (firstfreeslot p) nullAddr) ; try(exfalso ; congruence).
							---- (* optionfreeslotslist = NIL *) 
										destruct Hcons0 as [optionfreeslotslist (Hnil & HwellFormed & HNoDup)].
										exists optionfreeslotslist. intuition.
							---- (* optionfreeslotslist <> NIL *)
										(* show list equality between s0 and s*)
										assert(exists s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 n1 nbleft,
nbleft = (nbfreeslots p) /\
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
                     vidtBlock := vidtBlock pdentry
                   |}) (memory s0) beqAddr |} /\
getFreeSlotsListRec n1 (firstfreeslot p) s1 nbleft =
getFreeSlotsListRec (maxIdx+1) (firstfreeslot p) s0 nbleft
			 /\
	n1 <= maxIdx+1 /\ nbleft < n1
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
		                vidtBlock := vidtBlock pdentry0
		              |}
                 ) (memory s1) beqAddr |} /\
getFreeSlotsListRec n1 (firstfreeslot p) s2 nbleft =
			getFreeSlotsListRec n1 (firstfreeslot p) s1 nbleft
/\ s3 = {|
     currentPartition := currentPartition s2;
     memory := add newBlockEntryAddr
	            (BE
	               (CBlockEntry (read bentry) 
	                  (write bentry) (exec bentry) 
	                  (present bentry) (accessible bentry)
	                  (blockindex bentry)
	                  (CBlock startaddr (endAddr (blockrange bentry))))
                 ) (memory s2) beqAddr |} /\
getFreeSlotsListRec n1 (firstfreeslot p) s3 nbleft =
			getFreeSlotsListRec n1 (firstfreeslot p) s2 nbleft
/\ s4 = {|
     currentPartition := currentPartition s3;
     memory := add newBlockEntryAddr
               (BE
                  (CBlockEntry (read bentry0) 
                     (write bentry0) (exec bentry0) 
                     (present bentry0) (accessible bentry0)
                     (blockindex bentry0)
                     (CBlock (startAddr (blockrange bentry0)) endaddr))
                 ) (memory s3) beqAddr |} /\
getFreeSlotsListRec n1 (firstfreeslot p) s4 nbleft =
			getFreeSlotsListRec n1 (firstfreeslot p) s3 nbleft
/\ s5 = {|
     currentPartition := currentPartition s4;
     memory := add newBlockEntryAddr
              (BE
                 (CBlockEntry (read bentry1) 
                    (write bentry1) (exec bentry1) 
                    (present bentry1) true (blockindex bentry1)
                    (blockrange bentry1))
                 ) (memory s4) beqAddr |} /\
getFreeSlotsListRec n1 (firstfreeslot p) s5 nbleft =
			getFreeSlotsListRec n1 (firstfreeslot p) s4 nbleft
/\ s6 = {|
     currentPartition := currentPartition s5;
     memory := add newBlockEntryAddr
               (BE
                  (CBlockEntry (read bentry2) (write bentry2) 
                     (exec bentry2) true (accessible bentry2)
                     (blockindex bentry2) (blockrange bentry2))
                 ) (memory s5) beqAddr |} /\
getFreeSlotsListRec n1 (firstfreeslot p) s6 nbleft =
			getFreeSlotsListRec n1 (firstfreeslot p) s5 nbleft
/\ s7 = {|
     currentPartition := currentPartition s6;
     memory := add newBlockEntryAddr
              (BE
                 (CBlockEntry r (write bentry3) (exec bentry3)
                    (present bentry3) (accessible bentry3) 
                    (blockindex bentry3) (blockrange bentry3))
                 ) (memory s6) beqAddr |} /\
getFreeSlotsListRec n1 (firstfreeslot p) s7 nbleft =
			getFreeSlotsListRec n1 (firstfreeslot p) s6 nbleft
/\ s8 = {|
     currentPartition := currentPartition s7;
     memory := add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry4) w (exec bentry4) 
                       (present bentry4) (accessible bentry4) 
                       (blockindex bentry4) (blockrange bentry4))
                 ) (memory s7) beqAddr |} /\
getFreeSlotsListRec n1(firstfreeslot p) s8 nbleft =
			getFreeSlotsListRec n1 (firstfreeslot p) s7 nbleft
/\ s9 = {|
     currentPartition := currentPartition s8;
     memory := add newBlockEntryAddr
              (BE
                 (CBlockEntry (read bentry5) (write bentry5) e 
                    (present bentry5) (accessible bentry5) 
                    (blockindex bentry5) (blockrange bentry5))
                 ) (memory s8) beqAddr |} /\
getFreeSlotsListRec n1 (firstfreeslot p) s9 nbleft =
			getFreeSlotsListRec n1 (firstfreeslot p) s8 nbleft
/\ s10 = {|
     currentPartition := currentPartition s9;
     memory := add sceaddr 
								(SCE {| origin := origin; next := next scentry |}
                 ) (memory s9) beqAddr |} /\
getFreeSlotsListRec n1 (firstfreeslot p) s10 nbleft =
			getFreeSlotsListRec n1 (firstfreeslot p) s9 nbleft
).
{
	eexists ?[s1]. eexists ?[s2]. eexists ?[s3]. eexists ?[s4]. eexists ?[s5].
	eexists ?[s6]. eexists ?[s7]. eexists ?[s8]. eexists ?[s9].
	eexists ?[s10]. eexists ?[n1]. eexists.
	split. intuition.
	split. intuition.
	set (s1 := {| currentPartition := _ |}).
	(* prove outside *)
	assert(Hfreeslotss1 : getFreeSlotsListRec ?n1 (firstfreeslot p) s1 (nbfreeslots p) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s0 (nbfreeslots p)).
	{
		apply getFreeSlotsListRecEqPDT.
		-- 	intro Hfirstpdeq.
				assert(HFirstFreeSlotPointerIsBEAndFreeSlots0 : FirstFreeSlotPointerIsBEAndFreeSlot s0)
					by (unfold consistency in * ; intuition).
				unfold FirstFreeSlotPointerIsBEAndFreeSlot in *.
				specialize (HFirstFreeSlotPointerIsBEAndFreeSlots0 pd p Hlookups0).
				destruct HFirstFreeSlotPointerIsBEAndFreeSlots0.
				--- intro HfirstfreeNull.
						assert(HnullAddrExistss0 : nullAddrExists s0)
							by (unfold consistency in * ; intuition).
						unfold nullAddrExists in *.
						unfold isPADDR in *.
						rewrite HfirstfreeNull in *. rewrite <- Hfirstpdeq in *.
						destruct (lookup nullAddr (memory s0) beqAddr) ; try(exfalso ; congruence).
						destruct v0 ; try(exfalso ; congruence).
				--- rewrite Hfirstpdeq in *.
						unfold isBE in *.
						destruct (lookup pdinsertion (memory s0) beqAddr) ; try (exfalso ; congruence).
						destruct v0 ; try(exfalso ; congruence).
		-- unfold isBE. rewrite Hpdinsertions0. intuition.
		-- unfold isPADDR. rewrite Hpdinsertions0. intuition.
	}
	set (s2 := {| currentPartition := _ |}).
	assert(Hfreeslotss2 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s2 (nbfreeslots p) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s1 (nbfreeslots p)).
	{
				apply getFreeSlotsListRecEqPDT.
				--- 	intro Hfirstpdeq.
						assert(HFirstFreeSlotPointerIsBEAndFreeSlots0 : FirstFreeSlotPointerIsBEAndFreeSlot s0)
							by (unfold consistency in * ; intuition).
						unfold FirstFreeSlotPointerIsBEAndFreeSlot in *.
						specialize (HFirstFreeSlotPointerIsBEAndFreeSlots0 pd p Hlookups0).
						destruct HFirstFreeSlotPointerIsBEAndFreeSlots0.
						---- intro HfirstfreeNull.
								assert(HnullAddrExistss0 : nullAddrExists s0)
									by (unfold consistency in * ; intuition).
								unfold nullAddrExists in *.
								unfold isPADDR in *.
								rewrite HfirstfreeNull in *. rewrite <- Hfirstpdeq in *.
								destruct (lookup nullAddr (memory s0) beqAddr) ; try(exfalso ; congruence).
								destruct v0 ; try(exfalso ; congruence).
						---- rewrite Hfirstpdeq in *.
								unfold isBE in *.
								destruct (lookup pdinsertion (memory s0) beqAddr) ; try (exfalso ; congruence).
								destruct v0 ; try(exfalso ; congruence).
				--- unfold isBE. unfold s1. cbn. rewrite beqAddrTrue. intuition.
				--- unfold isPADDR. unfold s1. cbn. rewrite beqAddrTrue. intuition.
	}
	set (s3 := {| currentPartition := _ |}).
	assert(Hfreeslotss3 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s3 (nbfreeslots p) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s2 (nbfreeslots p)).
	{
				apply getFreeSlotsListRecEqBE ; intuition.
				---	(* Lists are disjoint at s0, so newB <> firstfreeslot p *)
							assert(Hfreeslotsdisjoints0 : DisjointFreeSlotsLists s0)
								by (unfold consistency in *; intuition).
							unfold DisjointFreeSlotsLists in *.
							assert(HPDTentrypds0 : isPDT pd s0).
							{ unfold isPDT. rewrite Hlookups0. trivial. }
							rewrite <- beqAddrFalse in beqpdpd.
							pose (H_Disjoints0 := Hfreeslotsdisjoints0 pdinsertion pd HPDTs0 HPDTentrypds0 beqpdpd).
							destruct H_Disjoints0 as [listoption1 (listoption2 & H_Disjoints0)].
							destruct H_Disjoints0 as [Hlistoption1 (HwellFormedList1 & (Hlistoption2 & (HwellFormedList2 & H_Disjoints0)))].
							unfold getFreeSlotsList in Hlistoption1.
							unfold getFreeSlotsList in Hlistoption2.
							rewrite Hpdinsertions0 in *.
							rewrite Hlookups0 in *.
							assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
							{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
							assert(HnewBFirstFrees0P : firstfreeslot p = newBlockEntryAddr) by intuition.
								rewrite HnewBFirstFrees0PDT in *.
								rewrite HnewBFirstFrees0P in *.
							destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
							rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
								rewrite FreeSlotsListRec_unroll in Hlistoption1.
								rewrite FreeSlotsListRec_unroll in Hlistoption2.
								unfold getFreeSlotsListAux in *.
								induction (maxIdx+1). (* false induction because of fixpoint constraints *)
								** (* N=0 -> NotWellFormed *)
									rewrite Hlistoption1 in *.
									cbn in HwellFormedList1.
									congruence.
								** (* N>0 *)
									clear IHn.
									cbn in *.
									rewrite HlookupnewBs0 in *.
									destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred1 ; try(exfalso ; congruence).
									*** destruct (StateLib.Index.pred (nbfreeslots p)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
											rewrite Hlistoption1 in *.
											cbn in *.
											unfold Lib.disjoint in H_Disjoints0.
											specialize(H_Disjoints0 newBlockEntryAddr).
											simpl in H_Disjoints0.
											intuition.
									*** rewrite Hlistoption1 in *.
											cbn in HwellFormedList1.
											exfalso ; congruence.
			--- unfold isBE. unfold s3. cbn.
					destruct (beqAddr pdinsertion newBlockEntryAddr) ; try(exfalso ; congruence).
					rewrite beqAddrTrue.
					cbn.
					repeat rewrite removeDupIdentity ; intuition.
			--- destruct Hcons0 as [Hoptionlist Hfreeslotss0].
					assert(HwellFormed : wellFormedFreeSlotsList Hoptionlist = False -> False) by intuition.
					apply HwellFormed. intuition. subst Hoptionlist.
					rewrite <- Hfreeslotss1 in *. rewrite <- Hfreeslotss2 in *. intuition.
			--- destruct Hcons0 as [Hoptionlist Hfreeslotss0].
					assert(HwellFormed : NoDup (filterOption  Hoptionlist)) by intuition.
					intuition. subst Hoptionlist.
					rewrite <- Hfreeslotss1 in *. rewrite <- Hfreeslotss2 in *. intuition.
			--- rewrite Hfreeslotss2 in *. rewrite Hfreeslotss1 in *.
					(* newB is in freeslots list of pdinsertion, so can't be in other list
							because of Disjoint *)
					(* DUP from previous step *)
					assert(Hfreeslotsdisjoints0 : DisjointFreeSlotsLists s0)
						by (unfold consistency in *; intuition).
					unfold DisjointFreeSlotsLists in *.
					assert(HPDTentrypds0 : isPDT pd s0).
					{ unfold isPDT. rewrite Hlookups0. trivial. }
					rewrite <- beqAddrFalse in beqpdpd.
					pose (H_Disjoints0 := Hfreeslotsdisjoints0 pdinsertion pd HPDTs0 HPDTentrypds0 beqpdpd).
					destruct H_Disjoints0 as [listoption1 (listoption2 & H_Disjoints0)].
					destruct H_Disjoints0 as [Hlistoption1 (HwellFormedList1 & (Hlistoption2 & (HwellFormedList2 & H_Disjoints0)))].
					unfold getFreeSlotsList in Hlistoption1.
					unfold getFreeSlotsList in Hlistoption2.
					rewrite Hpdinsertions0 in *.
					rewrite Hlookups0 in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					rewrite HnewBFirstFrees0PDT in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
					rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
					destruct (beqAddr (firstfreeslot p) nullAddr) eqn:HfirstfreeNull ; try(exfalso ; congruence).
					---- (* firstfreeslot p = NULL *)
								(* if first free of other PD is NULL, then newB can't be in NIL -> False *)
								rewrite <- DependentTypeLemmas.beqAddrTrue in HfirstfreeNull.
								contradict H30. (*  In newBlockEntryAddr (filterOption
           												(getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s0 (nbfreeslots p))) *)
								induction (maxIdx+1). (* false induction because of fixpoint constraints *)
								** (* N=0 -> NotWellFormed *)
									rewrite Hlistoption1 in *.
									cbn in HwellFormedList1.
									congruence.
								** (* N>0 *)
									clear IHn.
									assert(HnullAddrExistss0 : nullAddrExists s0)
										by (unfold consistency in * ; intuition).
									unfold nullAddrExists in *.
									unfold isPADDR in *.
									rewrite HfirstfreeNull in *.
									simpl.
									destruct (lookup nullAddr (memory s0) beqAddr) ; try(exfalso ; congruence).
									destruct v0 ; try(exfalso ; congruence).
									destruct (beqAddr p0 nullAddr) eqn:HfirstfreeNullFinal ; intuition.
					---- (* firstfreeslot p <> NULL *)
								(* if first free of other PD is NOT NULL,
								then newB can't be in the two lists at s0 because of Disjoint -> False *)
								subst listoption2. subst listoption1.
								unfold Lib.disjoint in H_Disjoints0.
								specialize(H_Disjoints0 newBlockEntryAddr).
								destruct (H_Disjoints0).
								* induction (maxIdx+1). (* false induction because of fixpoint constraints *)
									** (* N=0 -> NotWellFormed *)
											cbn in *.
											congruence.
									** (* N>0 *)
											clear IHn.
											simpl. rewrite HlookupnewBs0.
											assert(HcurrNb : currnbfreeslots = nbfreeslots pdentry).
											{ unfold pdentryNbFreeSlots in *. rewrite Hpdinsertions0 in *. intuition. }
											rewrite <- HcurrNb in *.
											destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred ; try(exfalso ; congruence).
											rewrite <- HcurrNb in *. rewrite Hpred. cbn. intuition.
								* intuition.
}
	set (s4 := {| currentPartition := currentPartition ?s3; memory := _ |}). simpl in s4. simpl in s3.
	assert(Hfreeslotss4 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s4 (nbfreeslots p) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s3 (nbfreeslots p)).
	{
		(* DUP *)
				apply getFreeSlotsListRecEqBE ; intuition.
				---	(* Lists are disjoint at s0, so newB <> firstfreeslot p *)
							assert(Hfreeslotsdisjoints0 : DisjointFreeSlotsLists s0)
								by (unfold consistency in *; intuition).
							unfold DisjointFreeSlotsLists in *.
							assert(HPDTentrypds0 : isPDT pd s0).
							{ unfold isPDT. rewrite Hlookups0. trivial. }
							rewrite <- beqAddrFalse in beqpdpd.
							pose (H_Disjoints0 := Hfreeslotsdisjoints0 pdinsertion pd HPDTs0 HPDTentrypds0 beqpdpd).
							destruct H_Disjoints0 as [listoption1 (listoption2 & H_Disjoints0)].
							destruct H_Disjoints0 as [Hlistoption1 (HwellFormedList1 & (Hlistoption2 & (HwellFormedList2 & H_Disjoints0)))].
							unfold getFreeSlotsList in Hlistoption1.
							unfold getFreeSlotsList in Hlistoption2.
							rewrite Hpdinsertions0 in *.
							rewrite Hlookups0 in *.
							assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
							{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
							assert(HnewBFirstFrees0P : firstfreeslot p = newBlockEntryAddr) by intuition.
								rewrite HnewBFirstFrees0PDT in *.
								rewrite HnewBFirstFrees0P in *.
							destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
							rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
								rewrite FreeSlotsListRec_unroll in Hlistoption1.
								rewrite FreeSlotsListRec_unroll in Hlistoption2.
								unfold getFreeSlotsListAux in *.
								induction (maxIdx+1). (* false induction because of fixpoint constraints *)
								** (* N=0 -> NotWellFormed *)
									rewrite Hlistoption1 in *.
									cbn in HwellFormedList1.
									congruence.
								** (* N>0 *)
									clear IHn.
									cbn in *.
									rewrite HlookupnewBs0 in *.
									destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred1 ; try(exfalso ; congruence).
									*** destruct (StateLib.Index.pred (nbfreeslots p)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
											rewrite Hlistoption1 in *.
											cbn in *.
											unfold Lib.disjoint in H_Disjoints0.
											specialize(H_Disjoints0 newBlockEntryAddr).
											simpl in H_Disjoints0.
											intuition.
									*** rewrite Hlistoption1 in *.
											cbn in HwellFormedList1.
											exfalso ; congruence.
			--- unfold isBE. unfold s4. cbn.
					destruct (beqAddr pdinsertion newBlockEntryAddr) ; try(exfalso ; congruence).
					rewrite beqAddrTrue.
					cbn.
					repeat rewrite removeDupIdentity ; intuition.
			--- destruct Hcons0 as [Hoptionlist Hfreeslotss0].
					assert(HwellFormed : wellFormedFreeSlotsList Hoptionlist = False -> False) by intuition.
					apply HwellFormed. intuition. subst Hoptionlist.
					rewrite <- Hfreeslotss1 in *. rewrite <- Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. intuition.
			--- destruct Hcons0 as [Hoptionlist Hfreeslotss0].
					assert(HwellFormed : NoDup (filterOption  Hoptionlist)) by intuition.
					intuition. subst Hoptionlist.
					rewrite <- Hfreeslotss1 in *. rewrite <- Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. intuition.
			--- rewrite <- Hfreeslotss3 in *.
					rewrite Hfreeslotss2 in *. rewrite Hfreeslotss1 in *.
					(* newB is in freeslots list of pdinsertion, so can't be in other list
							because of Disjoint *)
					(* DUP from previous step *)
					assert(Hfreeslotsdisjoints0 : DisjointFreeSlotsLists s0)
						by (unfold consistency in *; intuition).
					unfold DisjointFreeSlotsLists in *.
					assert(HPDTentrypds0 : isPDT pd s0).
					{ unfold isPDT. rewrite Hlookups0. trivial. }
					rewrite <- beqAddrFalse in beqpdpd.
					pose (H_Disjoints0 := Hfreeslotsdisjoints0 pdinsertion pd HPDTs0 HPDTentrypds0 beqpdpd).
					destruct H_Disjoints0 as [listoption1 (listoption2 & H_Disjoints0)].
					destruct H_Disjoints0 as [Hlistoption1 (HwellFormedList1 & (Hlistoption2 & (HwellFormedList2 & H_Disjoints0)))].
					unfold getFreeSlotsList in Hlistoption1.
					unfold getFreeSlotsList in Hlistoption2.
					rewrite Hpdinsertions0 in *.
					rewrite Hlookups0 in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					rewrite HnewBFirstFrees0PDT in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
					rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
					destruct (beqAddr (firstfreeslot p) nullAddr) eqn:HfirstfreeNull ; try(exfalso ; congruence).
					---- (* firstfreeslot p = NULL *)
								(* if first free of other PD is NULL, then newB can't be in NIL -> False *)
								rewrite <- DependentTypeLemmas.beqAddrTrue in HfirstfreeNull.
								contradict H30. (*  In newBlockEntryAddr (filterOption
           												(getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s0 (nbfreeslots p))) *)
								induction (maxIdx+1). (* false induction because of fixpoint constraints *)
								** (* N=0 -> NotWellFormed *)
									rewrite Hlistoption1 in *.
									cbn in HwellFormedList1.
									congruence.
								** (* N>0 *)
									clear IHn.
									assert(HnullAddrExistss0 : nullAddrExists s0)
										by (unfold consistency in * ; intuition).
									unfold nullAddrExists in *.
									unfold isPADDR in *.
									rewrite HfirstfreeNull in *.
									simpl.
									destruct (lookup nullAddr (memory s0) beqAddr) ; try(exfalso ; congruence).
									destruct v0 ; try(exfalso ; congruence).
									destruct (beqAddr p0 nullAddr) eqn:HfirstfreeNullFinal ; intuition.
					---- (* firstfreeslot p <> NULL *)
								(* if first free of other PD is NOT NULL,
								then newB can't be in the two lists at s0 because of Disjoint -> False *)
								subst listoption2. subst listoption1.
								unfold Lib.disjoint in H_Disjoints0.
								specialize(H_Disjoints0 newBlockEntryAddr).
								destruct (H_Disjoints0).
								* induction (maxIdx+1). (* false induction because of fixpoint constraints *)
									** (* N=0 -> NotWellFormed *)
											cbn in *.
											congruence.
									** (* N>0 *)
											clear IHn.
											simpl. rewrite HlookupnewBs0.
											assert(HcurrNb : currnbfreeslots = nbfreeslots pdentry).
											{ unfold pdentryNbFreeSlots in *. rewrite Hpdinsertions0 in *. intuition. }
											rewrite <- HcurrNb in *.
											destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred ; try(exfalso ; congruence).
											rewrite <- HcurrNb in *. rewrite Hpred. cbn. intuition.
								* intuition.
} fold s1. fold s2. fold s3. fold s4.
	set (s5 := {| currentPartition := currentPartition ?s4; memory := _ |}).
	simpl in s4.
	assert(Hfreeslotss5 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s5 (nbfreeslots p) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s4 (nbfreeslots p)).
	{
		(* DUP *)
				apply getFreeSlotsListRecEqBE ; intuition.
				---	(* Lists are disjoint at s0, so newB <> firstfreeslot p *)
							assert(Hfreeslotsdisjoints0 : DisjointFreeSlotsLists s0)
								by (unfold consistency in *; intuition).
							unfold DisjointFreeSlotsLists in *.
							assert(HPDTentrypds0 : isPDT pd s0).
							{ unfold isPDT. rewrite Hlookups0. trivial. }
							rewrite <- beqAddrFalse in beqpdpd.
							pose (H_Disjoints0 := Hfreeslotsdisjoints0 pdinsertion pd HPDTs0 HPDTentrypds0 beqpdpd).
							destruct H_Disjoints0 as [listoption1 (listoption2 & H_Disjoints0)].
							destruct H_Disjoints0 as [Hlistoption1 (HwellFormedList1 & (Hlistoption2 & (HwellFormedList2 & H_Disjoints0)))].
							unfold getFreeSlotsList in Hlistoption1.
							unfold getFreeSlotsList in Hlistoption2.
							rewrite Hpdinsertions0 in *.
							rewrite Hlookups0 in *.
							assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
							{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
							assert(HnewBFirstFrees0P : firstfreeslot p = newBlockEntryAddr) by intuition.
								rewrite HnewBFirstFrees0PDT in *.
								rewrite HnewBFirstFrees0P in *.
							destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
							rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
								rewrite FreeSlotsListRec_unroll in Hlistoption1.
								rewrite FreeSlotsListRec_unroll in Hlistoption2.
								unfold getFreeSlotsListAux in *.
								induction (maxIdx+1). (* false induction because of fixpoint constraints *)
								** (* N=0 -> NotWellFormed *)
									rewrite Hlistoption1 in *.
									cbn in HwellFormedList1.
									congruence.
								** (* N>0 *)
									clear IHn.
									cbn in *.
									rewrite HlookupnewBs0 in *.
									destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred1 ; try(exfalso ; congruence).
									*** destruct (StateLib.Index.pred (nbfreeslots p)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
											rewrite Hlistoption1 in *.
											cbn in *.
											unfold Lib.disjoint in H_Disjoints0.
											specialize(H_Disjoints0 newBlockEntryAddr).
											simpl in H_Disjoints0.
											intuition.
									*** rewrite Hlistoption1 in *.
											cbn in HwellFormedList1.
											exfalso ; congruence.
			--- unfold isBE. unfold s5. cbn.
					destruct (beqAddr pdinsertion newBlockEntryAddr) ; try(exfalso ; congruence).
					rewrite beqAddrTrue.
					cbn.
					repeat rewrite removeDupIdentity ; intuition.
			--- destruct Hcons0 as [Hoptionlist Hfreeslotss0].
					assert(HwellFormed : wellFormedFreeSlotsList Hoptionlist = False -> False) by intuition.
					apply HwellFormed. intuition. subst Hoptionlist.
					rewrite <- Hfreeslotss1 in *. rewrite <- Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *. intuition.
			--- destruct Hcons0 as [Hoptionlist Hfreeslotss0].
					assert(HwellFormed : NoDup (filterOption  Hoptionlist)) by intuition.
					intuition. subst Hoptionlist.
					rewrite <- Hfreeslotss1 in *. rewrite <- Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *. intuition.
			--- rewrite <- Hfreeslotss4 in *. rewrite <- Hfreeslotss3 in *.
					rewrite Hfreeslotss2 in *. rewrite Hfreeslotss1 in *.
					(* newB is in freeslots list of pdinsertion, so can't be in other list
							because of Disjoint *)
					(* DUP from previous step *)
					assert(Hfreeslotsdisjoints0 : DisjointFreeSlotsLists s0)
						by (unfold consistency in *; intuition).
					unfold DisjointFreeSlotsLists in *.
					assert(HPDTentrypds0 : isPDT pd s0).
					{ unfold isPDT. rewrite Hlookups0. trivial. }
					rewrite <- beqAddrFalse in beqpdpd.
					pose (H_Disjoints0 := Hfreeslotsdisjoints0 pdinsertion pd HPDTs0 HPDTentrypds0 beqpdpd).
					destruct H_Disjoints0 as [listoption1 (listoption2 & H_Disjoints0)].
					destruct H_Disjoints0 as [Hlistoption1 (HwellFormedList1 & (Hlistoption2 & (HwellFormedList2 & H_Disjoints0)))].
					unfold getFreeSlotsList in Hlistoption1.
					unfold getFreeSlotsList in Hlistoption2.
					rewrite Hpdinsertions0 in *.
					rewrite Hlookups0 in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					rewrite HnewBFirstFrees0PDT in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
					rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
					destruct (beqAddr (firstfreeslot p) nullAddr) eqn:HfirstfreeNull ; try(exfalso ; congruence).
					---- (* firstfreeslot p = NULL *)
								(* if first free of other PD is NULL, then newB can't be in NIL -> False *)
								rewrite <- DependentTypeLemmas.beqAddrTrue in HfirstfreeNull.
								contradict H30. (*  In newBlockEntryAddr (filterOption
           												(getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s0 (nbfreeslots p))) *)
								induction (maxIdx+1). (* false induction because of fixpoint constraints *)
								** (* N=0 -> NotWellFormed *)
									rewrite Hlistoption1 in *.
									cbn in HwellFormedList1.
									congruence.
								** (* N>0 *)
									clear IHn.
									assert(HnullAddrExistss0 : nullAddrExists s0)
										by (unfold consistency in * ; intuition).
									unfold nullAddrExists in *.
									unfold isPADDR in *.
									rewrite HfirstfreeNull in *.
									simpl.
									destruct (lookup nullAddr (memory s0) beqAddr) ; try(exfalso ; congruence).
									destruct v0 ; try(exfalso ; congruence).
									destruct (beqAddr p0 nullAddr) eqn:HfirstfreeNullFinal ; intuition.
					---- (* firstfreeslot p <> NULL *)
								(* if first free of other PD is NOT NULL,
								then newB can't be in the two lists at s0 because of Disjoint -> False *)
								subst listoption2. subst listoption1.
								unfold Lib.disjoint in H_Disjoints0.
								specialize(H_Disjoints0 newBlockEntryAddr).
								destruct (H_Disjoints0).
								* induction (maxIdx+1). (* false induction because of fixpoint constraints *)
									** (* N=0 -> NotWellFormed *)
											cbn in *.
											congruence.
									** (* N>0 *)
											clear IHn.
											simpl. rewrite HlookupnewBs0.
											assert(HcurrNb : currnbfreeslots = nbfreeslots pdentry).
											{ unfold pdentryNbFreeSlots in *. rewrite Hpdinsertions0 in *. intuition. }
											rewrite <- HcurrNb in *.
											destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred ; try(exfalso ; congruence).
											rewrite <- HcurrNb in *. rewrite Hpred. cbn. intuition.
								* intuition.
}
	fold s1. fold s2. fold s3. fold s4. fold s5.
	set (s6 := {| currentPartition := currentPartition ?s5; memory := _ |}).
	simpl in s4.
	assert(Hfreeslotss6 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s6 (nbfreeslots p) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s5 (nbfreeslots p)).
	{
		(* DUP *)
				apply getFreeSlotsListRecEqBE ; intuition.
				---	(* Lists are disjoint at s0, so newB <> firstfreeslot p *)
							assert(Hfreeslotsdisjoints0 : DisjointFreeSlotsLists s0)
								by (unfold consistency in *; intuition).
							unfold DisjointFreeSlotsLists in *.
							assert(HPDTentrypds0 : isPDT pd s0).
							{ unfold isPDT. rewrite Hlookups0. trivial. }
							rewrite <- beqAddrFalse in beqpdpd.
							pose (H_Disjoints0 := Hfreeslotsdisjoints0 pdinsertion pd HPDTs0 HPDTentrypds0 beqpdpd).
							destruct H_Disjoints0 as [listoption1 (listoption2 & H_Disjoints0)].
							destruct H_Disjoints0 as [Hlistoption1 (HwellFormedList1 & (Hlistoption2 & (HwellFormedList2 & H_Disjoints0)))].
							unfold getFreeSlotsList in Hlistoption1.
							unfold getFreeSlotsList in Hlistoption2.
							rewrite Hpdinsertions0 in *.
							rewrite Hlookups0 in *.
							assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
							{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
							assert(HnewBFirstFrees0P : firstfreeslot p = newBlockEntryAddr) by intuition.
								rewrite HnewBFirstFrees0PDT in *.
								rewrite HnewBFirstFrees0P in *.
							destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
							rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
								rewrite FreeSlotsListRec_unroll in Hlistoption1.
								rewrite FreeSlotsListRec_unroll in Hlistoption2.
								unfold getFreeSlotsListAux in *.
								induction (maxIdx+1). (* false induction because of fixpoint constraints *)
								** (* N=0 -> NotWellFormed *)
									rewrite Hlistoption1 in *.
									cbn in HwellFormedList1.
									congruence.
								** (* N>0 *)
									clear IHn.
									cbn in *.
									rewrite HlookupnewBs0 in *.
									destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred1 ; try(exfalso ; congruence).
									*** destruct (StateLib.Index.pred (nbfreeslots p)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
											rewrite Hlistoption1 in *.
											cbn in *.
											unfold Lib.disjoint in H_Disjoints0.
											specialize(H_Disjoints0 newBlockEntryAddr).
											simpl in H_Disjoints0.
											intuition.
									*** rewrite Hlistoption1 in *.
											cbn in HwellFormedList1.
											exfalso ; congruence.
			--- unfold isBE. unfold s6. cbn.
					destruct (beqAddr pdinsertion newBlockEntryAddr) ; try(exfalso ; congruence).
					rewrite beqAddrTrue.
					cbn.
					repeat rewrite removeDupIdentity ; intuition.
			--- destruct Hcons0 as [Hoptionlist Hfreeslotss0].
					assert(HwellFormed : wellFormedFreeSlotsList Hoptionlist = False -> False) by intuition.
					apply HwellFormed. intuition. subst Hoptionlist.
					rewrite <- Hfreeslotss1 in *. rewrite <- Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *.
					rewrite <- Hfreeslotss5 in *. intuition.
			--- destruct Hcons0 as [Hoptionlist Hfreeslotss0].
					assert(HwellFormed : NoDup (filterOption  Hoptionlist)) by intuition.
					intuition. subst Hoptionlist.
					rewrite <- Hfreeslotss1 in *. rewrite <- Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *.
					rewrite <- Hfreeslotss5 in *. intuition.
			--- rewrite <- Hfreeslotss5 in *.
					rewrite <- Hfreeslotss4 in *. rewrite <- Hfreeslotss3 in *.
					rewrite Hfreeslotss2 in *. rewrite Hfreeslotss1 in *.
					(* newB is in freeslots list of pdinsertion, so can't be in other list
							because of Disjoint *)
					(* DUP from previous step *)
					assert(Hfreeslotsdisjoints0 : DisjointFreeSlotsLists s0)
						by (unfold consistency in *; intuition).
					unfold DisjointFreeSlotsLists in *.
					assert(HPDTentrypds0 : isPDT pd s0).
					{ unfold isPDT. rewrite Hlookups0. trivial. }
					rewrite <- beqAddrFalse in beqpdpd.
					pose (H_Disjoints0 := Hfreeslotsdisjoints0 pdinsertion pd HPDTs0 HPDTentrypds0 beqpdpd).
					destruct H_Disjoints0 as [listoption1 (listoption2 & H_Disjoints0)].
					destruct H_Disjoints0 as [Hlistoption1 (HwellFormedList1 & (Hlistoption2 & (HwellFormedList2 & H_Disjoints0)))].
					unfold getFreeSlotsList in Hlistoption1.
					unfold getFreeSlotsList in Hlistoption2.
					rewrite Hpdinsertions0 in *.
					rewrite Hlookups0 in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					rewrite HnewBFirstFrees0PDT in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
					rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
					destruct (beqAddr (firstfreeslot p) nullAddr) eqn:HfirstfreeNull ; try(exfalso ; congruence).
					---- (* firstfreeslot p = NULL *)
								(* if first free of other PD is NULL, then newB can't be in NIL -> False *)
								rewrite <- DependentTypeLemmas.beqAddrTrue in HfirstfreeNull.
								contradict H30. (*  In newBlockEntryAddr (filterOption
           												(getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s0 (nbfreeslots p))) *)
								induction (maxIdx+1). (* false induction because of fixpoint constraints *)
								** (* N=0 -> NotWellFormed *)
									rewrite Hlistoption1 in *.
									cbn in HwellFormedList1.
									congruence.
								** (* N>0 *)
									clear IHn.
									assert(HnullAddrExistss0 : nullAddrExists s0)
										by (unfold consistency in * ; intuition).
									unfold nullAddrExists in *.
									unfold isPADDR in *.
									rewrite HfirstfreeNull in *.
									simpl.
									destruct (lookup nullAddr (memory s0) beqAddr) ; try(exfalso ; congruence).
									destruct v0 ; try(exfalso ; congruence).
									destruct (beqAddr p0 nullAddr) eqn:HfirstfreeNullFinal ; intuition.
					---- (* firstfreeslot p <> NULL *)
								(* if first free of other PD is NOT NULL,
								then newB can't be in the two lists at s0 because of Disjoint -> False *)
								subst listoption2. subst listoption1.
								unfold Lib.disjoint in H_Disjoints0.
								specialize(H_Disjoints0 newBlockEntryAddr).
								destruct (H_Disjoints0).
								* induction (maxIdx+1). (* false induction because of fixpoint constraints *)
									** (* N=0 -> NotWellFormed *)
											cbn in *.
											congruence.
									** (* N>0 *)
											clear IHn.
											simpl. rewrite HlookupnewBs0.
											assert(HcurrNb : currnbfreeslots = nbfreeslots pdentry).
											{ unfold pdentryNbFreeSlots in *. rewrite Hpdinsertions0 in *. intuition. }
											rewrite <- HcurrNb in *.
											destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred ; try(exfalso ; congruence).
											rewrite <- HcurrNb in *. rewrite Hpred. cbn. intuition.
								* intuition.
}
	fold s1. fold s2. fold s3. fold s4. fold s5. fold s6.
	set (s7 := {| currentPartition := currentPartition ?s6; memory := _ |}).
	simpl in s5. simpl in s6.
	assert(Hfreeslotss7 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s7 (nbfreeslots p) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s6 (nbfreeslots p)).
	{
		(* DUP *)
				apply getFreeSlotsListRecEqBE ; intuition.
				---	(* Lists are disjoint at s0, so newB <> firstfreeslot p *)
							assert(Hfreeslotsdisjoints0 : DisjointFreeSlotsLists s0)
								by (unfold consistency in *; intuition).
							unfold DisjointFreeSlotsLists in *.
							assert(HPDTentrypds0 : isPDT pd s0).
							{ unfold isPDT. rewrite Hlookups0. trivial. }
							rewrite <- beqAddrFalse in beqpdpd.
							pose (H_Disjoints0 := Hfreeslotsdisjoints0 pdinsertion pd HPDTs0 HPDTentrypds0 beqpdpd).
							destruct H_Disjoints0 as [listoption1 (listoption2 & H_Disjoints0)].
							destruct H_Disjoints0 as [Hlistoption1 (HwellFormedList1 & (Hlistoption2 & (HwellFormedList2 & H_Disjoints0)))].
							unfold getFreeSlotsList in Hlistoption1.
							unfold getFreeSlotsList in Hlistoption2.
							rewrite Hpdinsertions0 in *.
							rewrite Hlookups0 in *.
							assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
							{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
							assert(HnewBFirstFrees0P : firstfreeslot p = newBlockEntryAddr) by intuition.
								rewrite HnewBFirstFrees0PDT in *.
								rewrite HnewBFirstFrees0P in *.
							destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
							rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
								rewrite FreeSlotsListRec_unroll in Hlistoption1.
								rewrite FreeSlotsListRec_unroll in Hlistoption2.
								unfold getFreeSlotsListAux in *.
								induction (maxIdx+1). (* false induction because of fixpoint constraints *)
								** (* N=0 -> NotWellFormed *)
									rewrite Hlistoption1 in *.
									cbn in HwellFormedList1.
									congruence.
								** (* N>0 *)
									clear IHn.
									cbn in *.
									rewrite HlookupnewBs0 in *.
									destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred1 ; try(exfalso ; congruence).
									*** destruct (StateLib.Index.pred (nbfreeslots p)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
											rewrite Hlistoption1 in *.
											cbn in *.
											unfold Lib.disjoint in H_Disjoints0.
											specialize(H_Disjoints0 newBlockEntryAddr).
											simpl in H_Disjoints0.
											intuition.
									*** rewrite Hlistoption1 in *.
											cbn in HwellFormedList1.
											exfalso ; congruence.
			--- unfold isBE. unfold s7. cbn.
					destruct (beqAddr pdinsertion newBlockEntryAddr) ; try(exfalso ; congruence).
					rewrite beqAddrTrue.
					cbn.
					repeat rewrite removeDupIdentity ; intuition.
			--- destruct Hcons0 as [Hoptionlist Hfreeslotss0].
					assert(HwellFormed : wellFormedFreeSlotsList Hoptionlist = False -> False) by intuition.
					apply HwellFormed. intuition. subst Hoptionlist.
					rewrite <- Hfreeslotss1 in *. rewrite <- Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *.
					rewrite <- Hfreeslotss5 in *. rewrite <- Hfreeslotss6 in *. intuition.
			--- destruct Hcons0 as [Hoptionlist Hfreeslotss0].
					assert(HwellFormed : NoDup (filterOption  Hoptionlist)) by intuition.
					intuition. subst Hoptionlist.
					rewrite <- Hfreeslotss1 in *. rewrite <- Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *.
					rewrite <- Hfreeslotss5 in *. rewrite <- Hfreeslotss6 in *. intuition.
			--- rewrite <- Hfreeslotss6 in *. rewrite <- Hfreeslotss5 in *.
					rewrite <- Hfreeslotss4 in *. rewrite <- Hfreeslotss3 in *.
					rewrite Hfreeslotss2 in *. rewrite Hfreeslotss1 in *.
					(* newB is in freeslots list of pdinsertion, so can't be in other list
							because of Disjoint *)
					(* DUP from previous step *)
					assert(Hfreeslotsdisjoints0 : DisjointFreeSlotsLists s0)
						by (unfold consistency in *; intuition).
					unfold DisjointFreeSlotsLists in *.
					assert(HPDTentrypds0 : isPDT pd s0).
					{ unfold isPDT. rewrite Hlookups0. trivial. }
					rewrite <- beqAddrFalse in beqpdpd.
					pose (H_Disjoints0 := Hfreeslotsdisjoints0 pdinsertion pd HPDTs0 HPDTentrypds0 beqpdpd).
					destruct H_Disjoints0 as [listoption1 (listoption2 & H_Disjoints0)].
					destruct H_Disjoints0 as [Hlistoption1 (HwellFormedList1 & (Hlistoption2 & (HwellFormedList2 & H_Disjoints0)))].
					unfold getFreeSlotsList in Hlistoption1.
					unfold getFreeSlotsList in Hlistoption2.
					rewrite Hpdinsertions0 in *.
					rewrite Hlookups0 in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					rewrite HnewBFirstFrees0PDT in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
					rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
					destruct (beqAddr (firstfreeslot p) nullAddr) eqn:HfirstfreeNull ; try(exfalso ; congruence).
					---- (* firstfreeslot p = NULL *)
								(* if first free of other PD is NULL, then newB can't be in NIL -> False *)
								rewrite <- DependentTypeLemmas.beqAddrTrue in HfirstfreeNull.
								contradict H30. (*  In newBlockEntryAddr (filterOption
           												(getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s0 (nbfreeslots p))) *)
								induction (maxIdx+1). (* false induction because of fixpoint constraints *)
								** (* N=0 -> NotWellFormed *)
									rewrite Hlistoption1 in *.
									cbn in HwellFormedList1.
									congruence.
								** (* N>0 *)
									clear IHn.
									assert(HnullAddrExistss0 : nullAddrExists s0)
										by (unfold consistency in * ; intuition).
									unfold nullAddrExists in *.
									unfold isPADDR in *.
									rewrite HfirstfreeNull in *.
									simpl.
									destruct (lookup nullAddr (memory s0) beqAddr) ; try(exfalso ; congruence).
									destruct v0 ; try(exfalso ; congruence).
									destruct (beqAddr p0 nullAddr) eqn:HfirstfreeNullFinal ; intuition.
					---- (* firstfreeslot p <> NULL *)
								(* if first free of other PD is NOT NULL,
								then newB can't be in the two lists at s0 because of Disjoint -> False *)
								subst listoption2. subst listoption1.
								unfold Lib.disjoint in H_Disjoints0.
								specialize(H_Disjoints0 newBlockEntryAddr).
								destruct (H_Disjoints0).
								* induction (maxIdx+1). (* false induction because of fixpoint constraints *)
									** (* N=0 -> NotWellFormed *)
											cbn in *.
											congruence.
									** (* N>0 *)
											clear IHn.
											simpl. rewrite HlookupnewBs0.
											assert(HcurrNb : currnbfreeslots = nbfreeslots pdentry).
											{ unfold pdentryNbFreeSlots in *. rewrite Hpdinsertions0 in *. intuition. }
											rewrite <- HcurrNb in *.
											destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred ; try(exfalso ; congruence).
											rewrite <- HcurrNb in *. rewrite Hpred. cbn. intuition.
								* intuition.
}
	fold s1. fold s2. fold s3. fold s4. fold s5. fold s6. fold s7.
	set (s8 := {| currentPartition := currentPartition ?s7; memory := _ |}).
	simpl in s7.
	assert(Hfreeslotss8 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s8 (nbfreeslots p) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s7 (nbfreeslots p)).
	{
		(* DUP *)
				apply getFreeSlotsListRecEqBE ; intuition.
				---	(* Lists are disjoint at s0, so newB <> firstfreeslot p *)
							assert(Hfreeslotsdisjoints0 : DisjointFreeSlotsLists s0)
								by (unfold consistency in *; intuition).
							unfold DisjointFreeSlotsLists in *.
							assert(HPDTentrypds0 : isPDT pd s0).
							{ unfold isPDT. rewrite Hlookups0. trivial. }
							rewrite <- beqAddrFalse in beqpdpd.
							pose (H_Disjoints0 := Hfreeslotsdisjoints0 pdinsertion pd HPDTs0 HPDTentrypds0 beqpdpd).
							destruct H_Disjoints0 as [listoption1 (listoption2 & H_Disjoints0)].
							destruct H_Disjoints0 as [Hlistoption1 (HwellFormedList1 & (Hlistoption2 & (HwellFormedList2 & H_Disjoints0)))].
							unfold getFreeSlotsList in Hlistoption1.
							unfold getFreeSlotsList in Hlistoption2.
							rewrite Hpdinsertions0 in *.
							rewrite Hlookups0 in *.
							assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
							{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
							assert(HnewBFirstFrees0P : firstfreeslot p = newBlockEntryAddr) by intuition.
								rewrite HnewBFirstFrees0PDT in *.
								rewrite HnewBFirstFrees0P in *.
							destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
							rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
								rewrite FreeSlotsListRec_unroll in Hlistoption1.
								rewrite FreeSlotsListRec_unroll in Hlistoption2.
								unfold getFreeSlotsListAux in *.
								induction (maxIdx+1). (* false induction because of fixpoint constraints *)
								** (* N=0 -> NotWellFormed *)
									rewrite Hlistoption1 in *.
									cbn in HwellFormedList1.
									congruence.
								** (* N>0 *)
									clear IHn.
									cbn in *.
									rewrite HlookupnewBs0 in *.
									destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred1 ; try(exfalso ; congruence).
									*** destruct (StateLib.Index.pred (nbfreeslots p)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
											rewrite Hlistoption1 in *.
											cbn in *.
											unfold Lib.disjoint in H_Disjoints0.
											specialize(H_Disjoints0 newBlockEntryAddr).
											simpl in H_Disjoints0.
											intuition.
									*** rewrite Hlistoption1 in *.
											cbn in HwellFormedList1.
											exfalso ; congruence.
			--- unfold isBE. unfold s8. cbn.
					destruct (beqAddr pdinsertion newBlockEntryAddr) ; try(exfalso ; congruence).
					rewrite beqAddrTrue.
					cbn.
					repeat rewrite removeDupIdentity ; intuition.
			--- destruct Hcons0 as [Hoptionlist Hfreeslotss0].
					assert(HwellFormed : wellFormedFreeSlotsList Hoptionlist = False -> False) by intuition.
					apply HwellFormed. intuition. subst Hoptionlist.
					rewrite <- Hfreeslotss1 in *. rewrite <- Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *.
					rewrite <- Hfreeslotss5 in *. rewrite <- Hfreeslotss6 in *.
					rewrite <- Hfreeslotss7 in *. intuition.
			--- destruct Hcons0 as [Hoptionlist Hfreeslotss0].
					assert(HwellFormed : NoDup (filterOption  Hoptionlist)) by intuition.
					intuition. subst Hoptionlist.
					rewrite <- Hfreeslotss1 in *. rewrite <- Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *.
					rewrite <- Hfreeslotss5 in *. rewrite <- Hfreeslotss6 in *.
					rewrite <- Hfreeslotss7 in *. intuition.
			--- rewrite <- Hfreeslotss7 in *.
					rewrite <- Hfreeslotss6 in *. rewrite <- Hfreeslotss5 in *.
					rewrite <- Hfreeslotss4 in *. rewrite <- Hfreeslotss3 in *.
					rewrite Hfreeslotss2 in *. rewrite Hfreeslotss1 in *.
					(* newB is in freeslots list of pdinsertion, so can't be in other list
							because of Disjoint *)
					(* DUP from previous step *)
					assert(Hfreeslotsdisjoints0 : DisjointFreeSlotsLists s0)
						by (unfold consistency in *; intuition).
					unfold DisjointFreeSlotsLists in *.
					assert(HPDTentrypds0 : isPDT pd s0).
					{ unfold isPDT. rewrite Hlookups0. trivial. }
					rewrite <- beqAddrFalse in beqpdpd.
					pose (H_Disjoints0 := Hfreeslotsdisjoints0 pdinsertion pd HPDTs0 HPDTentrypds0 beqpdpd).
					destruct H_Disjoints0 as [listoption1 (listoption2 & H_Disjoints0)].
					destruct H_Disjoints0 as [Hlistoption1 (HwellFormedList1 & (Hlistoption2 & (HwellFormedList2 & H_Disjoints0)))].
					unfold getFreeSlotsList in Hlistoption1.
					unfold getFreeSlotsList in Hlistoption2.
					rewrite Hpdinsertions0 in *.
					rewrite Hlookups0 in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					rewrite HnewBFirstFrees0PDT in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
					rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
					destruct (beqAddr (firstfreeslot p) nullAddr) eqn:HfirstfreeNull ; try(exfalso ; congruence).
					---- (* firstfreeslot p = NULL *)
								(* if first free of other PD is NULL, then newB can't be in NIL -> False *)
								rewrite <- DependentTypeLemmas.beqAddrTrue in HfirstfreeNull.
								contradict H30. (*  In newBlockEntryAddr (filterOption
           												(getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s0 (nbfreeslots p))) *)
								induction (maxIdx+1). (* false induction because of fixpoint constraints *)
								** (* N=0 -> NotWellFormed *)
									rewrite Hlistoption1 in *.
									cbn in HwellFormedList1.
									congruence.
								** (* N>0 *)
									clear IHn.
									assert(HnullAddrExistss0 : nullAddrExists s0)
										by (unfold consistency in * ; intuition).
									unfold nullAddrExists in *.
									unfold isPADDR in *.
									rewrite HfirstfreeNull in *.
									simpl.
									destruct (lookup nullAddr (memory s0) beqAddr) ; try(exfalso ; congruence).
									destruct v0 ; try(exfalso ; congruence).
									destruct (beqAddr p0 nullAddr) eqn:HfirstfreeNullFinal ; intuition.
					---- (* firstfreeslot p <> NULL *)
								(* if first free of other PD is NOT NULL,
								then newB can't be in the two lists at s0 because of Disjoint -> False *)
								subst listoption2. subst listoption1.
								unfold Lib.disjoint in H_Disjoints0.
								specialize(H_Disjoints0 newBlockEntryAddr).
								destruct (H_Disjoints0).
								* induction (maxIdx+1). (* false induction because of fixpoint constraints *)
									** (* N=0 -> NotWellFormed *)
											cbn in *.
											congruence.
									** (* N>0 *)
											clear IHn.
											simpl. rewrite HlookupnewBs0.
											assert(HcurrNb : currnbfreeslots = nbfreeslots pdentry).
											{ unfold pdentryNbFreeSlots in *. rewrite Hpdinsertions0 in *. intuition. }
											rewrite <- HcurrNb in *.
											destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred ; try(exfalso ; congruence).
											rewrite <- HcurrNb in *. rewrite Hpred. cbn. intuition.
								* intuition.
}
	fold s1. fold s2. fold s3. fold s4. fold s5. fold s6. fold s7. fold s8.
	set (s9 := {| currentPartition := currentPartition ?s8; memory := _ |}).
	simpl in s7.
	assert(Hfreeslotss9 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s9 (nbfreeslots p) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s8 (nbfreeslots p)).
	{
		(* DUP *)
				apply getFreeSlotsListRecEqBE ; intuition.
				---	(* Lists are disjoint at s0, so newB <> firstfreeslot p *)
							assert(Hfreeslotsdisjoints0 : DisjointFreeSlotsLists s0)
								by (unfold consistency in *; intuition).
							unfold DisjointFreeSlotsLists in *.
							assert(HPDTentrypds0 : isPDT pd s0).
							{ unfold isPDT. rewrite Hlookups0. trivial. }
							rewrite <- beqAddrFalse in beqpdpd.
							pose (H_Disjoints0 := Hfreeslotsdisjoints0 pdinsertion pd HPDTs0 HPDTentrypds0 beqpdpd).
							destruct H_Disjoints0 as [listoption1 (listoption2 & H_Disjoints0)].
							destruct H_Disjoints0 as [Hlistoption1 (HwellFormedList1 & (Hlistoption2 & (HwellFormedList2 & H_Disjoints0)))].
							unfold getFreeSlotsList in Hlistoption1.
							unfold getFreeSlotsList in Hlistoption2.
							rewrite Hpdinsertions0 in *.
							rewrite Hlookups0 in *.
							assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
							{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
							assert(HnewBFirstFrees0P : firstfreeslot p = newBlockEntryAddr) by intuition.
								rewrite HnewBFirstFrees0PDT in *.
								rewrite HnewBFirstFrees0P in *.
							destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
							rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
								rewrite FreeSlotsListRec_unroll in Hlistoption1.
								rewrite FreeSlotsListRec_unroll in Hlistoption2.
								unfold getFreeSlotsListAux in *.
								induction (maxIdx+1). (* false induction because of fixpoint constraints *)
								** (* N=0 -> NotWellFormed *)
									rewrite Hlistoption1 in *.
									cbn in HwellFormedList1.
									congruence.
								** (* N>0 *)
									clear IHn.
									cbn in *.
									rewrite HlookupnewBs0 in *.
									destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred1 ; try(exfalso ; congruence).
									*** destruct (StateLib.Index.pred (nbfreeslots p)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
											rewrite Hlistoption1 in *.
											cbn in *.
											unfold Lib.disjoint in H_Disjoints0.
											specialize(H_Disjoints0 newBlockEntryAddr).
											simpl in H_Disjoints0.
											intuition.
									*** rewrite Hlistoption1 in *.
											cbn in HwellFormedList1.
											exfalso ; congruence.
			--- unfold isBE. unfold s9. cbn.
					destruct (beqAddr pdinsertion newBlockEntryAddr) ; try(exfalso ; congruence).
					rewrite beqAddrTrue.
					cbn.
					repeat rewrite removeDupIdentity ; intuition.
			--- destruct Hcons0 as [Hoptionlist Hfreeslotss0].
					assert(HwellFormed : wellFormedFreeSlotsList Hoptionlist = False -> False) by intuition.
					apply HwellFormed. intuition. subst Hoptionlist.
					rewrite <- Hfreeslotss1 in *. rewrite <- Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *.
					rewrite <- Hfreeslotss5 in *. rewrite <- Hfreeslotss6 in *.
					rewrite <- Hfreeslotss7 in *. rewrite <- Hfreeslotss8 in *. intuition.
			--- destruct Hcons0 as [Hoptionlist Hfreeslotss0].
					assert(HwellFormed : NoDup (filterOption  Hoptionlist)) by intuition.
					intuition. subst Hoptionlist.
					rewrite <- Hfreeslotss1 in *. rewrite <- Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *.
					rewrite <- Hfreeslotss5 in *. rewrite <- Hfreeslotss6 in *.
					rewrite <- Hfreeslotss7 in *. rewrite <- Hfreeslotss8 in *. intuition.
			--- rewrite <- Hfreeslotss8 in *. rewrite <- Hfreeslotss7 in *.
					rewrite <- Hfreeslotss6 in *. rewrite <- Hfreeslotss5 in *.
					rewrite <- Hfreeslotss4 in *. rewrite <- Hfreeslotss3 in *.
					rewrite Hfreeslotss2 in *. rewrite Hfreeslotss1 in *.
					(* newB is in freeslots list of pdinsertion, so can't be in other list
							because of Disjoint *)
					(* DUP from previous step *)
					assert(Hfreeslotsdisjoints0 : DisjointFreeSlotsLists s0)
						by (unfold consistency in *; intuition).
					unfold DisjointFreeSlotsLists in *.
					assert(HPDTentrypds0 : isPDT pd s0).
					{ unfold isPDT. rewrite Hlookups0. trivial. }
					rewrite <- beqAddrFalse in beqpdpd.
					pose (H_Disjoints0 := Hfreeslotsdisjoints0 pdinsertion pd HPDTs0 HPDTentrypds0 beqpdpd).
					destruct H_Disjoints0 as [listoption1 (listoption2 & H_Disjoints0)].
					destruct H_Disjoints0 as [Hlistoption1 (HwellFormedList1 & (Hlistoption2 & (HwellFormedList2 & H_Disjoints0)))].
					unfold getFreeSlotsList in Hlistoption1.
					unfold getFreeSlotsList in Hlistoption2.
					rewrite Hpdinsertions0 in *.
					rewrite Hlookups0 in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					rewrite HnewBFirstFrees0PDT in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
					rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
					destruct (beqAddr (firstfreeslot p) nullAddr) eqn:HfirstfreeNull ; try(exfalso ; congruence).
					---- (* firstfreeslot p = NULL *)
								(* if first free of other PD is NULL, then newB can't be in NIL -> False *)
								rewrite <- DependentTypeLemmas.beqAddrTrue in HfirstfreeNull.
								contradict H30. (*  In newBlockEntryAddr (filterOption
           												(getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s0 (nbfreeslots p))) *)
								induction (maxIdx+1). (* false induction because of fixpoint constraints *)
								** (* N=0 -> NotWellFormed *)
									rewrite Hlistoption1 in *.
									cbn in HwellFormedList1.
									congruence.
								** (* N>0 *)
									clear IHn.
									assert(HnullAddrExistss0 : nullAddrExists s0)
										by (unfold consistency in * ; intuition).
									unfold nullAddrExists in *.
									unfold isPADDR in *.
									rewrite HfirstfreeNull in *.
									simpl.
									destruct (lookup nullAddr (memory s0) beqAddr) ; try(exfalso ; congruence).
									destruct v0 ; try(exfalso ; congruence).
									destruct (beqAddr p0 nullAddr) eqn:HfirstfreeNullFinal ; intuition.
					---- (* firstfreeslot p <> NULL *)
								(* if first free of other PD is NOT NULL,
								then newB can't be in the two lists at s0 because of Disjoint -> False *)
								subst listoption2. subst listoption1.
								unfold Lib.disjoint in H_Disjoints0.
								specialize(H_Disjoints0 newBlockEntryAddr).
								destruct (H_Disjoints0).
								* induction (maxIdx+1). (* false induction because of fixpoint constraints *)
									** (* N=0 -> NotWellFormed *)
											cbn in *.
											congruence.
									** (* N>0 *)
											clear IHn.
											simpl. rewrite HlookupnewBs0.
											assert(HcurrNb : currnbfreeslots = nbfreeslots pdentry).
											{ unfold pdentryNbFreeSlots in *. rewrite Hpdinsertions0 in *. intuition. }
											rewrite <- HcurrNb in *.
											destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred ; try(exfalso ; congruence).
											rewrite <- HcurrNb in *. rewrite Hpred. cbn. intuition.
								* intuition.
}
	fold s1. fold s2. fold s3. fold s4. fold s5. fold s6. fold s7. fold s8. fold s9.
	set (s10 := {| currentPartition := currentPartition ?s9; memory := _ |}).
	simpl in s8. simpl in s9.
	assert(Hfreeslotss10 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s10 (nbfreeslots p) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s9 (nbfreeslots p)).
	{			assert(HSCEs9 : isSCE sceaddr s9).
						{ unfold isSCE. unfold s9. cbn. rewrite beqAddrTrue.
							destruct (beqAddr newBlockEntryAddr sceaddr) eqn:Hf ; try(exfalso ; congruence).
							rewrite <- beqAddrFalse in *.
							repeat rewrite removeDupIdentity ; intuition.
							destruct (beqAddr pdinsertion newBlockEntryAddr) eqn:Hff ; try(exfalso ; congruence).
							rewrite <- DependentTypeLemmas.beqAddrTrue in Hff. congruence.
							cbn.
							destruct (beqAddr pdinsertion sceaddr) eqn:Hfff ; try(exfalso ; congruence).
							rewrite <- DependentTypeLemmas.beqAddrTrue in Hfff. congruence.
							rewrite beqAddrTrue.
							rewrite <- beqAddrFalse in *.
							repeat rewrite removeDupIdentity ; intuition.
						}
				apply getFreeSlotsListRecEqSCE.
				--- 	intro Hfirstsceeq.
						assert(HFirstFreeSlotPointerIsBEAndFreeSlots0 : FirstFreeSlotPointerIsBEAndFreeSlot s0)
							by (unfold consistency in * ; intuition).
						unfold FirstFreeSlotPointerIsBEAndFreeSlot in *.
						specialize (HFirstFreeSlotPointerIsBEAndFreeSlots0 pd p Hlookups0).
						destruct HFirstFreeSlotPointerIsBEAndFreeSlots0.
						---- intro HfirstfreeNull.
								assert(HnullAddrExistss0 : nullAddrExists s0)
									by (unfold consistency in * ; intuition).
								unfold nullAddrExists in *.
								unfold isSCE in *.
								unfold isPADDR in *.
								rewrite HfirstfreeNull in *. rewrite <- Hfirstsceeq in *.
								destruct (lookup nullAddr (memory s0) beqAddr) ; try(exfalso ; congruence).
								destruct v0 ; try(exfalso ; congruence).
						---- rewrite Hfirstsceeq in *.
								unfold isSCE in *.
								unfold isBE in *.
								destruct (lookup sceaddr (memory s0) beqAddr) ; try (exfalso ; congruence).
								destruct v0 ; try(exfalso ; congruence).
				--- unfold isBE. unfold isSCE in HSCEs9.
						destruct (lookup sceaddr (memory s9) beqAddr) eqn:Hlookupsces9 ; try(exfalso ; congruence).
						destruct v0 ; try(exfalso ; congruence).
						intuition.
				--- unfold isPADDR. unfold isSCE in HSCEs9.
						destruct (lookup sceaddr (memory s9) beqAddr) eqn:Hlookupsces9 ; try(exfalso ; congruence).
						destruct v0 ; try(exfalso ; congruence).
						intuition.
}
	fold s1. fold s2. fold s3. fold s4. fold s5. fold s6. fold s7. fold s8. fold s9.
	fold s10.

	intuition.
	assert(HcurrLtmaxIdx : nbfreeslots p <= maxIdx).
	{ intuition. apply IdxLtMaxIdx. }
	lia.
}
destruct H30 as [s1 (s2 & (s3 & (s4 & (s5 & (s6 & (s7 & (s8 & (s9 & (s10 &
									(n1 & (nbleft & (Hnbleft & Hstates))))))))))))].
assert(HsEq : s10 = s).
{ intuition. subst s1. subst s2. subst s3. subst s4. subst s5. subst s6.
	subst s7. subst s8. subst s9. subst s10.
	rewrite Hs. f_equal.
}
rewrite HsEq in *.
assert(HfreeslotsEq : getFreeSlotsListRec n1 (firstfreeslot p) s (nbfreeslots p) =
											getFreeSlotsListRec (maxIdx+1) (firstfreeslot p) s0 (nbfreeslots p)).
{
	intuition.
	subst nbleft.
	(* rewrite all previous getFreeSlotsListRec equalities *)
	rewrite <- H33. rewrite <- H36. rewrite <- H38. rewrite <- H40. rewrite <- H42.
	rewrite <- H44. rewrite <- H46. rewrite <- H48. rewrite <- H50. rewrite <- H53.
	reflexivity.
}
assert (HfreeslotsEqn1 : getFreeSlotsListRec n1 (firstfreeslot p) s (nbfreeslots p)
													= getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s (nbfreeslots p)).
{ eapply getFreeSlotsListRecEqN ; intuition.
	subst nbleft. lia.
	assert (HnbLtmaxIdx : nbfreeslots p <= maxIdx) by apply IdxLtMaxIdx.
	lia.
}
rewrite <- HfreeslotsEqn1. rewrite HfreeslotsEq. intuition.
} (* end of NoDupInFreeSlotsList *)
split.
{ (* freeSlotsListIsFreeSlot s*)
	unfold freeSlotsListIsFreeSlot.
	intros pd freeslotaddr optionfreeslotslist freeslotslist HPDTpds.
	intros (HoptionfreeSlotsList&HwellFormedFreeSlots) (HfreeSlotsList & HfreeSlotInList).
	intro HfreeSlotNotNull.

	assert(Hcons0 : freeSlotsListIsFreeSlot s0) by (unfold consistency in * ; intuition).
	unfold freeSlotsListIsFreeSlot in Hcons0.

	(* check all possible values for freeslotaddr in the modified state s
	-> only possible is newBlockEntryAddr
	1) if freeslotaddr == newBlockEntryAddr :
			-> not possible since newBlockEntryAddr doesn't belong to freeslotslist
	2) if freeslotaddr <> newBlockEntryAddr :
		- relates to another free slot than newBlockentryAddr
		(either in the same free slots list or from another pd)
		-> leads to s0 -> OK
	*)
(* Check all values for pd *)
	destruct (beqAddr sceaddr pd) eqn:beqscepd; try(exfalso ; congruence).
	-	(* sceaddr = pd *)
		rewrite <- DependentTypeLemmas.beqAddrTrue in beqscepd.
		rewrite <- beqscepd in *.
		unfold isSCE in *.
		unfold isPDT in *.
		destruct (lookup sceaddr (memory s) beqAddr) ; try(exfalso ; congruence).
		destruct v ; try(exfalso ; congruence).
	-	(* sceaddr <> pd *)
		destruct (beqAddr newBlockEntryAddr pd) eqn:beqnewpd ; try(exfalso ; congruence).
		-- (* newBlockEntryAddr = pd *)
				rewrite <- DependentTypeLemmas.beqAddrTrue in beqnewpd.
				rewrite <- beqnewpd in *.
				unfold isBE in *.
				unfold isPDT in *.
				destruct (lookup newBlockEntryAddr (memory s) beqAddr) ; try(exfalso ; congruence).
				destruct v ; try(exfalso ; congruence).
		-- (* newBlockEntryAddr <> pd *)
				destruct (beqAddr pdinsertion pd) eqn:beqpdpd; try(exfalso ; congruence).
				--- (* pdinsertion = pd *)
						rewrite <- DependentTypeLemmas.beqAddrTrue in beqpdpd.
						rewrite <- beqpdpd in *.
						destruct H31 as [Hoptionlists (olds & (n0 & (n1 & (n2 & (nbleft & Hfreeslotsolds)))))].
						specialize (Hcons0 pdinsertion freeslotaddr (SomePaddr newBlockEntryAddr :: Hoptionlists) (newBlockEntryAddr::freeslotslist) HPDTs0).
						assert(HslotslistEqs0 : SomePaddr newBlockEntryAddr :: Hoptionlists = getFreeSlotsList pdinsertion s0 /\
											 wellFormedFreeSlotsList (SomePaddr newBlockEntryAddr :: Hoptionlists) <> False).
						{ unfold getFreeSlotsList. rewrite Hpdinsertions0.
							rewrite <- HnewB.
							destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
							rewrite <- beqAddrFalse in *.
							rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
							rewrite FreeSlotsListRec_unroll.
							unfold getFreeSlotsListAux in *.
							assert(HMaxIdxNext : maxIdx + 1 = S maxIdx).
							{ lia. }
							rewrite HMaxIdxNext.
							assert(Hnbfreeslots : (nbfreeslots pdentry) = currnbfreeslots).
							{ unfold pdentryNbFreeSlots in *. rewrite Hpdinsertions0 in *. intuition. }
							rewrite Hnbfreeslots.
							destruct (StateLib.Index.ltb currnbfreeslots zero) eqn:Hltb ; try(exfalso ; congruence).
							* unfold StateLib.Index.ltb in Hltb.
								apply PeanoNat.Nat.ltb_lt in Hltb.
								contradict Hltb. apply PeanoNat.Nat.lt_asymm. intuition.
							* rewrite HlookupnewBs0.
								destruct (StateLib.Index.pred currnbfreeslots) eqn:Hpred ; try(exfalso ; congruence).
								split.
								f_equal. intuition.
								rewrite H35. (* Hoptionlists = getFreeSlotsListRec n0 newFirstFreeSlotAddr s0 nbleft *)
								assert(HnewBEndIsNewFirst : (endAddr (blockrange bentry)) = newFirstFreeSlotAddr).
								{ unfold bentryEndAddr in *. rewrite HlookupnewBs0 in *. intuition. }
								rewrite HnewBEndIsNewFirst.
								assert(HnbLtmaxIdx : currnbfreeslots - 1 < maxIdx).
								{
										unfold pdentryNbFreeSlots in *. rewrite Hpdinsertions0 in *.
										destruct currnbfreeslots.
										+ simpl. destruct i0.
											* simpl. apply maxIdxNotZero.
											* cbn. rewrite PeanoNat.Nat.sub_0_r. intuition.
								}
								assert((CIndex (currnbfreeslots - 1)) = i).
								{ unfold CIndex.
									destruct (le_dec (currnbfreeslots - 1) maxIdx) ; simpl in * ; intuition ; try(exfalso ; congruence).
										unfold StateLib.Index.pred in *.
										destruct (gt_dec currnbfreeslots 0) ; try(exfalso ; congruence).
										inversion Hpred. f_equal. apply proof_irrelevance.
								}
								unfold pdentryNbFreeSlots in *. rewrite H5 in *.
								rewrite H8 in *.
								assert(i < maxIdx).
								{	unfold StateLib.Index.pred in *.
									destruct (gt_dec currnbfreeslots 0) ; try(exfalso ; congruence).
									inversion Hpred. simpl. intuition.
								}
								assert(HEq : getFreeSlotsListRec maxIdx newFirstFreeSlotAddr s0 i =
																getFreeSlotsListRec (maxIdx+1) newFirstFreeSlotAddr s0 i).
								{
									eapply getFreeSlotsListRecEqN ; intuition.
								}
								rewrite HEq.
								subst nbleft. subst i.
								eapply getFreeSlotsListRecEqN ; intuition.
								{ lia. }
								intuition.
							}
							specialize (Hcons0 HslotslistEqs0).
							(* continue to break Hcons0 1) sceaddr and podinsertion -> go to s0 show isFreeSlot @ s0 is false
																					2) newB -> show not in free slots list so NOK *)
							assert(HslotsListEqs : newBlockEntryAddr::freeslotslist = filterOption (SomePaddr newBlockEntryAddr :: Hoptionlists) /\
         														In freeslotaddr freeslotslist).
							{ intuition. cbn. f_equal. rewrite HfreeSlotsList.
								rewrite HoptionfreeSlotsList.
								unfold getFreeSlotsList. rewrite Hpdinsertions.
								rewrite HnewFirstFree. rewrite <- H36. (* getFreeSlotsListRec s .. = Hoptionlists *)

								destruct (beqAddr newFirstFreeSlotAddr nullAddr) eqn:HfirstIsNull ; try(exfalso ; congruence).
								rewrite <- DependentTypeLemmas.beqAddrTrue in HfirstIsNull.
								rewrite HfirstIsNull.
								rewrite FreeSlotsListRec_unroll.
								unfold getFreeSlotsListAux.
								destruct n2. cbn. reflexivity.
								destruct (StateLib.Index.ltb nbleft zero) eqn:Hltb ; try(exfalso ; congruence).
								cbn. reflexivity.
								unfold nullAddrExists in *. unfold isPADDR in *.
								destruct (lookup nullAddr (memory s) beqAddr) ; try(exfalso ; congruence).
								destruct v eqn:Hv ; try(exfalso ; congruence).
								destruct (beqAddr p nullAddr) eqn:HpNull ; try(cbn ; reflexivity).
								assert(Hnbleft : nbfreeslots pdentry1 = nbleft).
								{ subst pdentry1. simpl.
									subst nbleft. (* nbleft = CIndex (currnbfreeslots - 1)*)
									destruct predCurrentNbFreeSlots.
									unfold StateLib.Index.pred in H1.
									destruct (gt_dec currnbfreeslots 0); try (exfalso ; congruence).
									unfold CIndex. inversion H1 as [Hpred].
									rewrite Hpred. destruct (le_dec i maxIdx) ; try(exfalso ; congruence).
									f_equal. apply proof_irrelevance.
								}
								rewrite Hnbleft.
								assert (HfreeSlotsEq : getFreeSlotsListRec (maxIdx + 1) newFirstFreeSlotAddr s nbleft =
																getFreeSlotsListRec n2 newFirstFreeSlotAddr s nbleft).
								{ apply eq_sym.
									eapply getFreeSlotsListRecEqN ; intuition.
								}
								rewrite HfreeSlotsEq. reflexivity.
							}
							assert(HInFreeSlotExpand : In freeslotaddr freeslotslist ->
																					In freeslotaddr (newBlockEntryAddr :: freeslotslist)).
							{ intuition. }
							assert(HslotIn : newBlockEntryAddr :: freeslotslist =
																	filterOption (SomePaddr newBlockEntryAddr :: Hoptionlists) /\
																	In freeslotaddr (newBlockEntryAddr :: freeslotslist)) by intuition.
							specialize (Hcons0 HslotIn HfreeSlotNotNull).
							(* 1) dismiss all impossible values for freeslotaddr except newB *)
							destruct (beqAddr sceaddr freeslotaddr) eqn:beqfscefree; try(exfalso ; congruence).
								---- (* sceaddr = freeslotaddr *)
											rewrite <- DependentTypeLemmas.beqAddrTrue in beqfscefree.
											rewrite <- beqfscefree in *.
											unfold isSCE in *.
											unfold isFreeSlot in *.
											destruct (lookup sceaddr (memory s0) beqAddr) ; try(exfalso ; congruence).
											destruct v ; try(exfalso ; congruence).
								---- (* sceaddr <> freeslotaddr *)
											destruct (beqAddr pdinsertion freeslotaddr) eqn:beqfpdfree; try(exfalso ; congruence).
											----- (* pdinsertion = freeslotaddr *)
														rewrite <- DependentTypeLemmas.beqAddrTrue in beqfpdfree.
														rewrite <- beqfpdfree in *.
														unfold isPDT in *.
														unfold isFreeSlot in *.
														destruct (lookup pdinsertion (memory s0) beqAddr) ; try(exfalso ; congruence).
														destruct v ; try(exfalso ; congruence).
											----- (* pdinsertion <> freeslotaddr *)
														destruct (beqAddr newBlockEntryAddr freeslotaddr) eqn:beqfnewBfree; try(exfalso ; congruence).
														------ (* newBlockEntryAddr = freeslotaddr *)
																		rewrite <- DependentTypeLemmas.beqAddrTrue in beqfnewBfree.
																		rewrite <- beqfnewBfree in *.
																		(* 2) we already proved newB is not in the free slots list anymore *)
																		contradict HfreeSlotInList.
																		rewrite HfreeSlotsList. rewrite HoptionfreeSlotsList.
																		unfold getFreeSlotsList. rewrite Hpdinsertions.
																		rewrite HnewFirstFree.
																		destruct (beqAddr newFirstFreeSlotAddr nullAddr) eqn:HnewNotNull ; try(exfalso ; congruence).
																		cbn. intuition.
																		assert(Hnbleft : nbfreeslots pdentry1 = nbleft).
																		{ (* DUP *)
																			subst pdentry1. simpl. intuition.
																			subst nbleft. (* nbleft = CIndex (currnbfreeslots - 1)*)
																			destruct predCurrentNbFreeSlots.
																			unfold StateLib.Index.pred in H1.
																			destruct (gt_dec currnbfreeslots 0); try (exfalso ; congruence).
																			unfold CIndex. inversion H1 as [Hpred].
																			rewrite Hpred. destruct (le_dec i maxIdx) ; try(exfalso ; congruence).
																			f_equal. apply proof_irrelevance.
																		}
																		rewrite Hnbleft.
																		assert(HfreeSlotsListEq : Hoptionlists = getFreeSlotsListRec (maxIdx + 1) newFirstFreeSlotAddr s nbleft).
																		{ intuition.
																			rewrite <- H40. (* getFreeSlotsList s = Hoptionlists *)
																			eapply getFreeSlotsListRecEqN ; intuition.
																		}
																		rewrite <- HfreeSlotsListEq. intuition.
														------ (* newBlockEntryAddr <> freeslotaddr *)
																		(* no entry left to try out -> leads to s0 *)
																		rewrite Hs. unfold isFreeSlot.
																		cbn. rewrite beqAddrTrue.
																		rewrite beqfscefree.
																		destruct (beqAddr newBlockEntryAddr sceaddr) eqn:newsce ; try(exfalso ; congruence).
																		rewrite beqAddrTrue.
																		cbn. rewrite beqfnewBfree.
																		rewrite <- beqAddrFalse in *.
																		rewrite removeDupIdentity ; try congruence.
																		rewrite removeDupIdentity ; try congruence.
																		rewrite removeDupIdentity ; try congruence.
																		rewrite removeDupIdentity ; try congruence.
																		rewrite removeDupIdentity ; try congruence.
																		rewrite removeDupIdentity ; try congruence.
																		rewrite removeDupIdentity ; try congruence.
																		destruct (beqAddr pdinsertion newBlockEntryAddr) eqn:pdnew ; try(exfalso ; congruence).
																		rewrite <- DependentTypeLemmas.beqAddrTrue in pdnew. congruence.
																		cbn.
																		destruct (beqAddr pdinsertion freeslotaddr) eqn:pdffentry; try(exfalso ; congruence).
																		rewrite <- DependentTypeLemmas.beqAddrTrue in pdffentry. congruence.
																		rewrite <- beqAddrFalse in *.
																		rewrite removeDupIdentity ; try congruence.
																		rewrite removeDupIdentity ; try congruence.
																		rewrite removeDupIdentity ; try congruence.
																		unfold isFreeSlot in Hcons0.
																		destruct (lookup freeslotaddr (memory s0) beqAddr) eqn:HfreeSlots0 ; try(exfalso ; congruence).
																		destruct v ; try(exfalso ; congruence).
																		destruct (beqAddr sceaddr (CPaddr (freeslotaddr + sh1offset))) eqn:beqscefreesh1 ; try(exfalso ; congruence).
																		rewrite <- DependentTypeLemmas.beqAddrTrue in beqscefreesh1.
																		rewrite <- beqscefreesh1 in *.
																		unfold isFreeSlot in *.
																		unfold isSCE in *.
																		destruct (lookup sceaddr (memory s0) beqAddr) ; try(exfalso ; congruence).
																		destruct v ; try(exfalso ; congruence).
																		destruct (beqAddr newBlockEntryAddr (CPaddr (freeslotaddr + sh1offset))) eqn:beqscefreesc ; try(exfalso ; congruence).
																		rewrite <- DependentTypeLemmas.beqAddrTrue in beqscefreesc.
																		rewrite <- beqscefreesc in *.
																		unfold isFreeSlot in *.
																		unfold isBE in *.
																		destruct (lookup newBlockEntryAddr (memory s0) beqAddr) ; try(exfalso ; congruence).
																		destruct v ; try(exfalso ; congruence).
																		rewrite <- beqAddrFalse in *.
																		rewrite removeDupIdentity ; try congruence.
																		rewrite removeDupIdentity ; try congruence.
																		rewrite removeDupIdentity ; try congruence.
																		rewrite removeDupIdentity ; try congruence.
																		rewrite removeDupIdentity ; try congruence.
																		rewrite removeDupIdentity ; try congruence.
																		destruct (beqAddr pdinsertion newBlockEntryAddr) eqn:pdnewB; try(exfalso ; congruence).
																		rewrite <- DependentTypeLemmas.beqAddrTrue in pdnewB. congruence.
																		cbn.
																		destruct (beqAddr pdinsertion (CPaddr (freeslotaddr + sh1offset))) eqn:beqpdfreesh1 ; try(exfalso ; congruence).
																		rewrite <- DependentTypeLemmas.beqAddrTrue in beqpdfreesh1.
																		rewrite <- beqpdfreesh1 in *.
																		unfold isFreeSlot in *.
																		unfold isPDT in *.
																		destruct (lookup pdinsertion (memory s0) beqAddr) ; try(exfalso ; congruence).
																		destruct v ; try(exfalso ; congruence).
																		rewrite removeDupIdentity ; try congruence.
																		rewrite removeDupIdentity ; try congruence.
																		rewrite removeDupIdentity ; try congruence.
																		rewrite <- beqAddrFalse in *.
																		rewrite removeDupIdentity ; try congruence.
																		destruct (lookup (CPaddr (freeslotaddr + sh1offset)) (memory s0) beqAddr) ; try(exfalso ; congruence).
																		destruct v ; try(exfalso ; congruence).
																		destruct (beqAddr sceaddr (CPaddr (freeslotaddr + scoffset))) eqn:beqscefssc ; try(exfalso ; congruence).
																		(* show sceaddr must be equal to freeslot which is false *)
																		rewrite <- DependentTypeLemmas.beqAddrTrue in beqscefssc.
																		assert(HSCEOffset : sceaddr = CPaddr (newBlockEntryAddr + scoffset)) by intuition.
																		rewrite HSCEOffset in beqscefssc.
																		contradict beqscefssc.
																		unfold nullAddrExists in *. unfold isPADDR in *.
																		unfold CPaddr.
																		destruct (le_dec (newBlockEntryAddr + scoffset) maxAddr) eqn:Hj.
																		* destruct (le_dec (freeslotaddr + scoffset) maxAddr) eqn:Hk.
																			** simpl in *. intro Hfalse.
																				inversion Hfalse as [Heq].
																				rewrite PeanoNat.Nat.add_cancel_r in Heq.
																				apply CPaddrInjectionNat in Heq.
																				repeat rewrite paddrEqId in Heq.
																				congruence.
																			** 	intro Hfalse.
																					inversion Hfalse as [Heq].
																					assert(HeqNull : CPaddr(newBlockEntryAddr + scoffset) = nullAddr).
																					{ rewrite nullAddrIs0.
																						apply CPaddrInjectionNat in Heq.
																						intuition.
																					}
																					rewrite HeqNull in *.
																					rewrite HSCEOffset in *.
																					unfold isSCE in *.
																					destruct (lookup nullAddr (memory s) beqAddr) ; try(exfalso ; congruence).
																					destruct v ; try(exfalso ; congruence).
																		* assert(Heq : CPaddr(newBlockEntryAddr + scoffset) = nullAddr).
																			{ rewrite nullAddrIs0.
																				unfold CPaddr. rewrite Hj.
																				destruct (le_dec 0 maxAddr) ; intuition.
																				f_equal. apply proof_irrelevance.
																			}
																			rewrite Heq in *.
																			rewrite HSCEOffset in *.
																			unfold isSCE in *.
																			destruct (lookup nullAddr (memory s) beqAddr) ; try(exfalso ; congruence).
																			destruct v ; try(exfalso ; congruence).
																		* destruct (beqAddr newBlockEntryAddr (CPaddr (freeslotaddr + scoffset))) eqn:beqnewBfssc ; try(exfalso ; congruence).
																			------- (* newBlockEntryAddr = (CPaddr (freeslotaddr + scoffset)) *)
																							rewrite <- DependentTypeLemmas.beqAddrTrue in beqnewBfssc.
																							rewrite <- beqnewBfssc in *.
																							destruct (lookup newBlockEntryAddr (memory s0) beqAddr) ; try(exfalso ; congruence).
																							destruct v ; try(exfalso ; congruence).
																			------- (* newBlockEntryAddr <> (CPaddr (freeslotaddr + scoffset)) *)
 																							rewrite <- beqAddrFalse in *.
																							repeat rewrite removeDupIdentity ; try congruence.
																							destruct (beqAddr pdinsertion newBlockEntryAddr) eqn:Hf; try(exfalso ; congruence).
																							rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
																							rewrite <- beqAddrFalse in *.
																							repeat rewrite removeDupIdentity ; try congruence.
																							cbn.
																							destruct (beqAddr pdinsertion (CPaddr (freeslotaddr + scoffset))) eqn:beqpdfssc ; try (exfalso ; congruence).
																							-------- (* pdinsertion = (CPaddr (freeslotaddr + scoffset)) *)
																												rewrite <- DependentTypeLemmas.beqAddrTrue in beqpdfssc.
																												rewrite <- beqpdfssc in *.
																												destruct (lookup pdinsertion (memory s0) beqAddr) ; try(exfalso ; congruence).
																												destruct v ; try(exfalso ; congruence).
																							-------- (* pdinsertion <> (CPaddr (freeslotaddr + scoffset)) *)
																												rewrite <- beqAddrFalse in *.
																												repeat rewrite removeDupIdentity ; try congruence.
																												destruct (lookup (CPaddr (freeslotaddr + scoffset)) (memory s0) beqAddr) eqn:Hlookupsc ; try(exfalso ; congruence).
																												destruct v ; try(exfalso ; congruence).
																												intuition.
																		* intro Hf. rewrite <- beqAddrFalse in *. congruence.
			--- (* pdinsertion <> pd *)
					(* similarly, we must prove the list has not changed by recomputing each
							intermediate steps and check at that time *)
					(* WIP show leads to s0 -> OK *)
					assert(HlookupEq : lookup pd (memory s) beqAddr = lookup pd (memory s0) beqAddr).
					{	(* check all values *)
						destruct (beqAddr sceaddr pd) eqn:beqscepdentry; try(exfalso ; congruence).
						(* sceaddr <> pd *)
						destruct (beqAddr newBlockEntryAddr pd) eqn:newpdentry ; try(exfalso ; congruence).
						(* newBlockEntryAddr <> pd *)
						destruct (beqAddr pdinsertion pd) eqn:beqpdpdentry; try(exfalso ; congruence).
						(* pdinsertion <> pd *)
						rewrite Hs.
						cbn. rewrite beqAddrTrue.
						rewrite beqscepdentry.
						assert(HnewBsceNotEq : beqAddr newBlockEntryAddr sceaddr = false) by intuition.
						rewrite HnewBsceNotEq. (*newBlock <> sce *)
						assert(HpdnewBNotEq : beqAddr pdinsertion newBlockEntryAddr = false) by intuition.
						rewrite HpdnewBNotEq. (*pd <> newblock*)
						cbn.
						rewrite newpdentry.
						rewrite beqAddrTrue.
						rewrite <- beqAddrFalse in *.
						repeat rewrite removeDupIdentity ; intuition.
						destruct (beqAddr pdinsertion newBlockEntryAddr) eqn:Hf ; try(exfalso ; congruence).
						rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
						cbn.
						destruct (beqAddr pdinsertion pd) eqn:Hff ; try(exfalso ; congruence).
						rewrite <- DependentTypeLemmas.beqAddrTrue in Hff. congruence.
						rewrite <- beqAddrFalse in *.
						repeat rewrite removeDupIdentity ; intuition.
					}
					assert(HPDTpds0: isPDT pd s0).
					{ unfold isPDT in *. rewrite <- HlookupEq. intuition. }
					specialize(Hcons0 pd freeslotaddr ). (*optionfreeslotslist freeslotslist HPDTpds0).*)
					assert(HfreeSlotsListEq : optionfreeslotslist = getFreeSlotsList pd s0 /\
         						wellFormedFreeSlotsList optionfreeslotslist <> False).
					{
						unfold getFreeSlotsList.
						assert(Hlookups0: isPDT pd s0) by intuition.
						apply isPDTLookupEq in Hlookups0. destruct Hlookups0 as [p Hlookups0].
						unfold getFreeSlotsList in *. rewrite HlookupEq in *. rewrite Hlookups0 in *.
						destruct (beqAddr (firstfreeslot p) nullAddr) eqn: HpNotNull ; try(exfalso ; congruence).
						---- (* optionfreeslotslist = NIL *)
									intuition.
						---- (* optionfreeslotslist <> NIL *)
									(* show list equality between s0 and s*)
									assert(Hs' : exists s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 n1 nbleft,
nbleft = (nbfreeslots p) /\
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
                     vidtBlock := vidtBlock pdentry
                   |}) (memory s0) beqAddr |} /\
getFreeSlotsListRec n1 (firstfreeslot p) s1 nbleft =
getFreeSlotsListRec (maxIdx+1) (firstfreeslot p) s0 nbleft
			 /\
	n1 <= maxIdx+1 /\ nbleft < n1
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
		                vidtBlock := vidtBlock pdentry0
		              |}
                 ) (memory s1) beqAddr |} /\
getFreeSlotsListRec n1 (firstfreeslot p) s2 nbleft =
			getFreeSlotsListRec n1 (firstfreeslot p) s1 nbleft
/\ s3 = {|
     currentPartition := currentPartition s2;
     memory := add newBlockEntryAddr
	            (BE
	               (CBlockEntry (read bentry) 
	                  (write bentry) (exec bentry) 
	                  (present bentry) (accessible bentry)
	                  (blockindex bentry)
	                  (CBlock startaddr (endAddr (blockrange bentry))))
                 ) (memory s2) beqAddr |} /\
getFreeSlotsListRec n1 (firstfreeslot p) s3 nbleft =
			getFreeSlotsListRec n1 (firstfreeslot p) s2 nbleft
/\ s4 = {|
     currentPartition := currentPartition s3;
     memory := add newBlockEntryAddr
               (BE
                  (CBlockEntry (read bentry0) 
                     (write bentry0) (exec bentry0) 
                     (present bentry0) (accessible bentry0)
                     (blockindex bentry0)
                     (CBlock (startAddr (blockrange bentry0)) endaddr))
                 ) (memory s3) beqAddr |} /\
getFreeSlotsListRec n1 (firstfreeslot p) s4 nbleft =
			getFreeSlotsListRec n1 (firstfreeslot p) s3 nbleft
/\ s5 = {|
     currentPartition := currentPartition s4;
     memory := add newBlockEntryAddr
              (BE
                 (CBlockEntry (read bentry1) 
                    (write bentry1) (exec bentry1) 
                    (present bentry1) true (blockindex bentry1)
                    (blockrange bentry1))
                 ) (memory s4) beqAddr |} /\
getFreeSlotsListRec n1 (firstfreeslot p) s5 nbleft =
			getFreeSlotsListRec n1 (firstfreeslot p) s4 nbleft
/\ s6 = {|
     currentPartition := currentPartition s5;
     memory := add newBlockEntryAddr
               (BE
                  (CBlockEntry (read bentry2) (write bentry2) 
                     (exec bentry2) true (accessible bentry2)
                     (blockindex bentry2) (blockrange bentry2))
                 ) (memory s5) beqAddr |} /\
getFreeSlotsListRec n1 (firstfreeslot p) s6 nbleft =
			getFreeSlotsListRec n1 (firstfreeslot p) s5 nbleft
/\ s7 = {|
     currentPartition := currentPartition s6;
     memory := add newBlockEntryAddr
              (BE
                 (CBlockEntry r (write bentry3) (exec bentry3)
                    (present bentry3) (accessible bentry3) 
                    (blockindex bentry3) (blockrange bentry3))
                 ) (memory s6) beqAddr |} /\
getFreeSlotsListRec n1 (firstfreeslot p) s7 nbleft =
			getFreeSlotsListRec n1 (firstfreeslot p) s6 nbleft
/\ s8 = {|
     currentPartition := currentPartition s7;
     memory := add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry4) w (exec bentry4) 
                       (present bentry4) (accessible bentry4) 
                       (blockindex bentry4) (blockrange bentry4))
                 ) (memory s7) beqAddr |} /\
getFreeSlotsListRec n1(firstfreeslot p) s8 nbleft =
			getFreeSlotsListRec n1 (firstfreeslot p) s7 nbleft
/\ s9 = {|
     currentPartition := currentPartition s8;
     memory := add newBlockEntryAddr
              (BE
                 (CBlockEntry (read bentry5) (write bentry5) e 
                    (present bentry5) (accessible bentry5) 
                    (blockindex bentry5) (blockrange bentry5))
                 ) (memory s8) beqAddr |} /\
getFreeSlotsListRec n1 (firstfreeslot p) s9 nbleft =
			getFreeSlotsListRec n1 (firstfreeslot p) s8 nbleft
/\ s10 = {|
     currentPartition := currentPartition s9;
     memory := add sceaddr 
								(SCE {| origin := origin; next := next scentry |}
                 ) (memory s9) beqAddr |} /\
getFreeSlotsListRec n1 (firstfreeslot p) s10 nbleft =
			getFreeSlotsListRec n1 (firstfreeslot p) s9 nbleft
).
{
	eexists ?[s1]. eexists ?[s2]. eexists ?[s3]. eexists ?[s4]. eexists ?[s5].
	eexists ?[s6]. eexists ?[s7]. eexists ?[s8]. eexists ?[s9].
	eexists ?[s10]. eexists ?[n1]. eexists.
	split. intuition.
	split. intuition.
	set (s1 := {| currentPartition := _ |}).
	(* prove outside *)
	assert(Hfreeslotss1 : getFreeSlotsListRec ?n1 (firstfreeslot p) s1 (nbfreeslots p) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s0 (nbfreeslots p)).
	{
		apply getFreeSlotsListRecEqPDT.
		-- 	intro Hfirstpdeq.
				assert(HFirstFreeSlotPointerIsBEAndFreeSlots0 : FirstFreeSlotPointerIsBEAndFreeSlot s0)
					by (unfold consistency in * ; intuition).
				unfold FirstFreeSlotPointerIsBEAndFreeSlot in *.
				specialize (HFirstFreeSlotPointerIsBEAndFreeSlots0 pd p Hlookups0).
				destruct HFirstFreeSlotPointerIsBEAndFreeSlots0.
				--- intro HfirstfreeNull.
						assert(HnullAddrExistss0 : nullAddrExists s0)
							by (unfold consistency in * ; intuition).
						unfold nullAddrExists in *.
						unfold isPADDR in *.
						rewrite HfirstfreeNull in *. rewrite <- Hfirstpdeq in *.
						destruct (lookup nullAddr (memory s0) beqAddr) ; try(exfalso ; congruence).
						destruct v ; try(exfalso ; congruence).
				--- rewrite Hfirstpdeq in *.
						unfold isBE in *.
						destruct (lookup pdinsertion (memory s0) beqAddr) ; try (exfalso ; congruence).
						destruct v ; try(exfalso ; congruence).
		-- unfold isBE. rewrite Hpdinsertions0. intuition.
		-- unfold isPADDR. rewrite Hpdinsertions0. intuition.
	}
	set (s2 := {| currentPartition := _ |}).
	assert(Hfreeslotss2 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s2 (nbfreeslots p) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s1 (nbfreeslots p)).
	{
				apply getFreeSlotsListRecEqPDT.
				--- 	intro Hfirstpdeq.
						assert(HFirstFreeSlotPointerIsBEAndFreeSlots0 : FirstFreeSlotPointerIsBEAndFreeSlot s0)
							by (unfold consistency in * ; intuition).
						unfold FirstFreeSlotPointerIsBEAndFreeSlot in *.
						specialize (HFirstFreeSlotPointerIsBEAndFreeSlots0 pd p Hlookups0).
						destruct HFirstFreeSlotPointerIsBEAndFreeSlots0.
						---- intro HfirstfreeNull.
								assert(HnullAddrExistss0 : nullAddrExists s0)
									by (unfold consistency in * ; intuition).
								unfold nullAddrExists in *.
								unfold isPADDR in *.
								rewrite HfirstfreeNull in *. rewrite <- Hfirstpdeq in *.
								destruct (lookup nullAddr (memory s0) beqAddr) ; try(exfalso ; congruence).
								destruct v ; try(exfalso ; congruence).
						---- rewrite Hfirstpdeq in *.
								unfold isBE in *.
								destruct (lookup pdinsertion (memory s0) beqAddr) ; try (exfalso ; congruence).
								destruct v ; try(exfalso ; congruence).
				--- unfold isBE. unfold s1. cbn. rewrite beqAddrTrue. intuition.
				--- unfold isPADDR. unfold s1. cbn. rewrite beqAddrTrue. intuition.
	}
	set (s3 := {| currentPartition := _ |}).
	assert(Hfreeslotss3 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s3 (nbfreeslots p) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s2 (nbfreeslots p)).
	{			assert(HwellFormedNoDup : NoDupInFreeSlotsList s0) by (unfold consistency in * ; intuition).
				unfold NoDupInFreeSlotsList in *.
				specialize (HwellFormedNoDup pd p Hlookups0).
				apply getFreeSlotsListRecEqBE ; intuition.
				---	(* Lists are disjoint at s0, so newB <> firstfreeslot p *)
							assert(Hfreeslotsdisjoints0 : DisjointFreeSlotsLists s0)
								by (unfold consistency in *; intuition).
							unfold DisjointFreeSlotsLists in *.
							assert(HPDTentrypds0 : isPDT pd s0).
							{ unfold isPDT. rewrite Hlookups0. trivial. }
							rewrite <- beqAddrFalse in beqpdpd.
							pose (H_Disjoints0 := Hfreeslotsdisjoints0 pdinsertion pd HPDTs0 HPDTentrypds0 beqpdpd).
							destruct H_Disjoints0 as [listoption1 (listoption2 & H_Disjoints0)].
							destruct H_Disjoints0 as [Hlistoption1 (HwellFormedList1 & (Hlistoption2 & (HwellFormedList2 & H_Disjoints0)))].
							unfold getFreeSlotsList in Hlistoption1.
							unfold getFreeSlotsList in Hlistoption2.
							rewrite Hpdinsertions0 in *.
							rewrite Hlookups0 in *.
							assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
							{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
							assert(HnewBFirstFrees0P : firstfreeslot p = newBlockEntryAddr) by intuition.
								rewrite HnewBFirstFrees0PDT in *.
								rewrite HnewBFirstFrees0P in *.
							destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
							(*rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.*)
								rewrite FreeSlotsListRec_unroll in Hlistoption1.
								rewrite FreeSlotsListRec_unroll in Hlistoption2.
								unfold getFreeSlotsListAux in *.
								induction (maxIdx+1). (* false induction because of fixpoint constraints *)
								** (* N=0 -> NotWellFormed *)
									rewrite Hlistoption1 in *.
									cbn in HwellFormedList1.
									congruence.
								** (* N>0 *)
									clear IHn.
									cbn in *.
									rewrite HlookupnewBs0 in *.
									destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred1 ; try(exfalso ; congruence).
									*** destruct (StateLib.Index.pred (nbfreeslots p)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
											rewrite Hlistoption1 in *.
											cbn in *.
											unfold Lib.disjoint in H_Disjoints0.
											specialize(H_Disjoints0 newBlockEntryAddr).
											simpl in H_Disjoints0.
											intuition.
									*** rewrite Hlistoption1 in *.
											cbn in HwellFormedList1.
											exfalso ; congruence.
			--- unfold isBE. cbn. unfold s3. cbn.
					destruct (beqAddr pdinsertion newBlockEntryAddr) ; try(exfalso ; congruence).
					rewrite beqAddrTrue.
					cbn.
					repeat rewrite removeDupIdentity ; intuition.
			--- destruct HwellFormedNoDup as [Hoptionlist Hfreeslotss0].
					assert(HFirstFreeSlotEq : getFreeSlotsList pd s0 = getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s0 (nbfreeslots p)).
					{ unfold getFreeSlotsList. rewrite Hlookups0. rewrite HpNotNull. reflexivity. }
					rewrite HFirstFreeSlotEq in *.
					assert(HwellFormed : wellFormedFreeSlotsList Hoptionlist = False -> False) by intuition.
					apply HwellFormed. intuition. subst Hoptionlist.
					rewrite <- Hfreeslotss1 in *. rewrite <- Hfreeslotss2 in *. intuition.
			--- destruct HwellFormedNoDup as [Hoptionlist Hfreeslotss0].
					assert(HFirstFreeSlotEq : getFreeSlotsList pd s0 = getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s0 (nbfreeslots p)).
					{ unfold getFreeSlotsList. rewrite Hlookups0. rewrite HpNotNull. reflexivity. }
					rewrite HFirstFreeSlotEq in *.
					assert(HwellFormed : NoDup (filterOption  Hoptionlist)) by intuition.
					intuition. subst Hoptionlist.
					rewrite <- Hfreeslotss1 in *. rewrite <- Hfreeslotss2 in *. intuition.
			--- rewrite Hfreeslotss2 in *. rewrite Hfreeslotss1 in *.
					(* newB is in freeslots list of pdinsertion, so can't be in other list
							because of Disjoint *)
					(* DUP from previous step *)
					assert(Hfreeslotsdisjoints0 : DisjointFreeSlotsLists s0)
						by (unfold consistency in *; intuition).
					unfold DisjointFreeSlotsLists in *.
					assert(HPDTentrypds0 : isPDT pd s0).
					{ unfold isPDT. rewrite Hlookups0. trivial. }
					rewrite <- beqAddrFalse in beqpdpd.
					pose (H_Disjoints0 := Hfreeslotsdisjoints0 pdinsertion pd HPDTs0 HPDTentrypds0 beqpdpd).
					destruct H_Disjoints0 as [listoption1 (listoption2 & H_Disjoints0)].
					destruct H_Disjoints0 as [Hlistoption1 (HwellFormedList1 & (Hlistoption2 & (HwellFormedList2 & H_Disjoints0)))].
					unfold getFreeSlotsList in Hlistoption1.
					unfold getFreeSlotsList in Hlistoption2.
					rewrite Hpdinsertions0 in *.
					rewrite Hlookups0 in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					rewrite HnewBFirstFrees0PDT in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
					rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
					destruct (beqAddr (firstfreeslot p) nullAddr) eqn:HfirstfreeNull ; try(exfalso ; congruence).
					(* firstfreeslot p <> NULL *)
					(* if first free of other PD is NOT NULL,
					then newB can't be in the two lists at s0 because of Disjoint -> False *)
					subst listoption2. subst listoption1.
					unfold Lib.disjoint in H_Disjoints0.
					specialize(H_Disjoints0 newBlockEntryAddr).
					destruct (H_Disjoints0).
					* induction (maxIdx+1). (* false induction because of fixpoint constraints *)
						** (* N=0 -> NotWellFormed *)
								cbn in *.
								congruence.
						** (* N>0 *)
								clear IHn.
								simpl. rewrite HlookupnewBs0.
								assert(HcurrNb : currnbfreeslots = nbfreeslots pdentry).
								{ unfold pdentryNbFreeSlots in *. rewrite Hpdinsertions0 in *. intuition. }
								rewrite <- HcurrNb in *.
								destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred ; try(exfalso ; congruence).
								rewrite <- HcurrNb in *. rewrite Hpred. cbn. intuition.
					* intuition.
}
	set (s4 := {| currentPartition := currentPartition ?s3; memory := _ |}). simpl in s4. simpl in s3.
	assert(Hfreeslotss4 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s4 (nbfreeslots p) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s3 (nbfreeslots p)).
	{
		(* DUP *)
		assert(HwellFormedNoDup : NoDupInFreeSlotsList s0) by (unfold consistency in * ; intuition).
		unfold NoDupInFreeSlotsList in *.
		specialize (HwellFormedNoDup pd p Hlookups0).
		apply getFreeSlotsListRecEqBE ; intuition.
		---	(* Lists are disjoint at s0, so newB <> firstfreeslot p *)
					assert(Hfreeslotsdisjoints0 : DisjointFreeSlotsLists s0)
						by (unfold consistency in *; intuition).
					unfold DisjointFreeSlotsLists in *.
					assert(HPDTentrypds0 : isPDT pd s0).
					{ unfold isPDT. rewrite Hlookups0. trivial. }
					rewrite <- beqAddrFalse in beqpdpd.
					pose (H_Disjoints0 := Hfreeslotsdisjoints0 pdinsertion pd HPDTs0 HPDTentrypds0 beqpdpd).
					destruct H_Disjoints0 as [listoption1 (listoption2 & H_Disjoints0)].
					destruct H_Disjoints0 as [Hlistoption1 (HwellFormedList1 & (Hlistoption2 & (HwellFormedList2 & H_Disjoints0)))].
					unfold getFreeSlotsList in Hlistoption1.
					unfold getFreeSlotsList in Hlistoption2.
					rewrite Hpdinsertions0 in *.
					rewrite Hlookups0 in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					assert(HnewBFirstFrees0P : firstfreeslot p = newBlockEntryAddr) by intuition.
						rewrite HnewBFirstFrees0PDT in *.
						rewrite HnewBFirstFrees0P in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
						rewrite FreeSlotsListRec_unroll in Hlistoption1.
						rewrite FreeSlotsListRec_unroll in Hlistoption2.
						unfold getFreeSlotsListAux in *.
						induction (maxIdx+1). (* false induction because of fixpoint constraints *)
						** (* N=0 -> NotWellFormed *)
							rewrite Hlistoption1 in *.
							cbn in HwellFormedList1.
							congruence.
						** (* N>0 *)
							clear IHn.
							cbn in *.
							rewrite HlookupnewBs0 in *.
							destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred1 ; try(exfalso ; congruence).
							*** destruct (StateLib.Index.pred (nbfreeslots p)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
									rewrite Hlistoption1 in *.
									cbn in *.
									unfold Lib.disjoint in H_Disjoints0.
									specialize(H_Disjoints0 newBlockEntryAddr).
									simpl in H_Disjoints0.
									intuition.
							*** rewrite Hlistoption1 in *.
									cbn in HwellFormedList1.
									exfalso ; congruence.
			--- unfold isBE. unfold s4. cbn.
					destruct (beqAddr pdinsertion newBlockEntryAddr) ; try(exfalso ; congruence).
					rewrite beqAddrTrue.
					cbn.
					repeat rewrite removeDupIdentity ; intuition.
			--- destruct HwellFormedNoDup as [Hoptionlist Hfreeslotss0].
					assert(HFirstFreeSlotEq : getFreeSlotsList pd s0 = getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s0 (nbfreeslots p)).
					{ unfold getFreeSlotsList. rewrite Hlookups0. rewrite HpNotNull. reflexivity. }
					rewrite HFirstFreeSlotEq in *.
					assert(HwellFormed : wellFormedFreeSlotsList Hoptionlist = False -> False) by intuition.
					apply HwellFormed. intuition. subst Hoptionlist.
					rewrite <- Hfreeslotss1 in *. rewrite <- Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. intuition.
			--- destruct HwellFormedNoDup as [Hoptionlist Hfreeslotss0].
					assert(HFirstFreeSlotEq : getFreeSlotsList pd s0 = getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s0 (nbfreeslots p)).
					{ unfold getFreeSlotsList. rewrite Hlookups0. rewrite HpNotNull. reflexivity. }
					rewrite HFirstFreeSlotEq in *.
					assert(HwellFormed : NoDup (filterOption  Hoptionlist)) by intuition.
					intuition. subst Hoptionlist.
					rewrite <- Hfreeslotss1 in *. rewrite <- Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. intuition.
			--- rewrite <- Hfreeslotss3 in *.
					rewrite Hfreeslotss2 in *. rewrite Hfreeslotss1 in *.
					(* newB is in freeslots list of pdinsertion, so can't be in other list
							because of Disjoint *)
					(* DUP from previous step *)
					assert(Hfreeslotsdisjoints0 : DisjointFreeSlotsLists s0)
						by (unfold consistency in *; intuition).
					unfold DisjointFreeSlotsLists in *.
					assert(HPDTentrypds0 : isPDT pd s0).
					{ unfold isPDT. rewrite Hlookups0. trivial. }
					rewrite <- beqAddrFalse in beqpdpd.
					pose (H_Disjoints0 := Hfreeslotsdisjoints0 pdinsertion pd HPDTs0 HPDTentrypds0 beqpdpd).
					destruct H_Disjoints0 as [listoption1 (listoption2 & H_Disjoints0)].
					destruct H_Disjoints0 as [Hlistoption1 (HwellFormedList1 & (Hlistoption2 & (HwellFormedList2 & H_Disjoints0)))].
					unfold getFreeSlotsList in Hlistoption1.
					unfold getFreeSlotsList in Hlistoption2.
					rewrite Hpdinsertions0 in *.
					rewrite Hlookups0 in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					rewrite HnewBFirstFrees0PDT in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
					rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
					destruct (beqAddr (firstfreeslot p) nullAddr) eqn:HfirstfreeNull ; try(exfalso ; congruence).
					(* firstfreeslot p <> NULL *)
					(* if first free of other PD is NOT NULL,
					then newB can't be in the two lists at s0 because of Disjoint -> False *)
					subst listoption2. subst listoption1.
					unfold Lib.disjoint in H_Disjoints0.
					specialize(H_Disjoints0 newBlockEntryAddr).
					destruct (H_Disjoints0).
					* induction (maxIdx+1). (* false induction because of fixpoint constraints *)
						** (* N=0 -> NotWellFormed *)
								cbn in *.
								congruence.
						** (* N>0 *)
								clear IHn.
								simpl. rewrite HlookupnewBs0.
								assert(HcurrNb : currnbfreeslots = nbfreeslots pdentry).
								{ unfold pdentryNbFreeSlots in *. rewrite Hpdinsertions0 in *. intuition. }
								rewrite <- HcurrNb in *.
								destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred ; try(exfalso ; congruence).
								rewrite <- HcurrNb in *. rewrite Hpred. cbn. intuition.
					* intuition.
} fold s1. fold s2. fold s3. fold s4.
	set (s5 := {| currentPartition := currentPartition ?s4; memory := _ |}).
	simpl in s4.
	assert(Hfreeslotss5 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s5 (nbfreeslots p) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s4 (nbfreeslots p)).
	{
		(* DUP *)
		assert(HwellFormedNoDup : NoDupInFreeSlotsList s0) by (unfold consistency in * ; intuition).
		unfold NoDupInFreeSlotsList in *.
		specialize (HwellFormedNoDup pd p Hlookups0).
		apply getFreeSlotsListRecEqBE ; intuition.
		---	(* Lists are disjoint at s0, so newB <> firstfreeslot p *)
					assert(Hfreeslotsdisjoints0 : DisjointFreeSlotsLists s0)
						by (unfold consistency in *; intuition).
					unfold DisjointFreeSlotsLists in *.
					assert(HPDTentrypds0 : isPDT pd s0).
					{ unfold isPDT. rewrite Hlookups0. trivial. }
					rewrite <- beqAddrFalse in beqpdpd.
					pose (H_Disjoints0 := Hfreeslotsdisjoints0 pdinsertion pd HPDTs0 HPDTentrypds0 beqpdpd).
					destruct H_Disjoints0 as [listoption1 (listoption2 & H_Disjoints0)].
					destruct H_Disjoints0 as [Hlistoption1 (HwellFormedList1 & (Hlistoption2 & (HwellFormedList2 & H_Disjoints0)))].
					unfold getFreeSlotsList in Hlistoption1.
					unfold getFreeSlotsList in Hlistoption2.
					rewrite Hpdinsertions0 in *.
					rewrite Hlookups0 in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					assert(HnewBFirstFrees0P : firstfreeslot p = newBlockEntryAddr) by intuition.
						rewrite HnewBFirstFrees0PDT in *.
						rewrite HnewBFirstFrees0P in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
						rewrite FreeSlotsListRec_unroll in Hlistoption1.
						rewrite FreeSlotsListRec_unroll in Hlistoption2.
						unfold getFreeSlotsListAux in *.
						induction (maxIdx+1). (* false induction because of fixpoint constraints *)
						** (* N=0 -> NotWellFormed *)
							rewrite Hlistoption1 in *.
							cbn in HwellFormedList1.
							congruence.
						** (* N>0 *)
							clear IHn.
							cbn in *.
							rewrite HlookupnewBs0 in *.
							destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred1 ; try(exfalso ; congruence).
							*** destruct (StateLib.Index.pred (nbfreeslots p)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
									rewrite Hlistoption1 in *.
									cbn in *.
									unfold Lib.disjoint in H_Disjoints0.
									specialize(H_Disjoints0 newBlockEntryAddr).
									simpl in H_Disjoints0.
									intuition.
							*** rewrite Hlistoption1 in *.
									cbn in HwellFormedList1.
									exfalso ; congruence.
			--- unfold isBE. unfold s5. cbn.
					destruct (beqAddr pdinsertion newBlockEntryAddr) ; try(exfalso ; congruence).
					rewrite beqAddrTrue.
					cbn.
					repeat rewrite removeDupIdentity ; intuition.
			--- destruct HwellFormedNoDup as [Hoptionlist Hfreeslotss0].
					assert(HFirstFreeSlotEq : getFreeSlotsList pd s0 = getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s0 (nbfreeslots p)).
					{ unfold getFreeSlotsList. rewrite Hlookups0. rewrite HpNotNull. reflexivity. }
					rewrite HFirstFreeSlotEq in *.
					assert(HwellFormed : wellFormedFreeSlotsList Hoptionlist = False -> False) by intuition.
					apply HwellFormed. intuition. subst Hoptionlist.
					rewrite <- Hfreeslotss1 in *. rewrite <- Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *. intuition.
			--- destruct HwellFormedNoDup as [Hoptionlist Hfreeslotss0].
					assert(HFirstFreeSlotEq : getFreeSlotsList pd s0 = getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s0 (nbfreeslots p)).
					{ unfold getFreeSlotsList. rewrite Hlookups0. rewrite HpNotNull. reflexivity. }
					rewrite HFirstFreeSlotEq in *.
					assert(HwellFormed : NoDup (filterOption  Hoptionlist)) by intuition.
					intuition. subst Hoptionlist.
					rewrite <- Hfreeslotss1 in *. rewrite <- Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *. intuition.
			--- rewrite <- Hfreeslotss4 in *. rewrite <- Hfreeslotss3 in *.
					rewrite Hfreeslotss2 in *. rewrite Hfreeslotss1 in *.
					(* newB is in freeslots list of pdinsertion, so can't be in other list
							because of Disjoint *)
					(* DUP from previous step *)
					assert(Hfreeslotsdisjoints0 : DisjointFreeSlotsLists s0)
						by (unfold consistency in *; intuition).
					unfold DisjointFreeSlotsLists in *.
					assert(HPDTentrypds0 : isPDT pd s0).
					{ unfold isPDT. rewrite Hlookups0. trivial. }
					rewrite <- beqAddrFalse in beqpdpd.
					pose (H_Disjoints0 := Hfreeslotsdisjoints0 pdinsertion pd HPDTs0 HPDTentrypds0 beqpdpd).
					destruct H_Disjoints0 as [listoption1 (listoption2 & H_Disjoints0)].
					destruct H_Disjoints0 as [Hlistoption1 (HwellFormedList1 & (Hlistoption2 & (HwellFormedList2 & H_Disjoints0)))].
					unfold getFreeSlotsList in Hlistoption1.
					unfold getFreeSlotsList in Hlistoption2.
					rewrite Hpdinsertions0 in *.
					rewrite Hlookups0 in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					rewrite HnewBFirstFrees0PDT in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
					rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
					destruct (beqAddr (firstfreeslot p) nullAddr) eqn:HfirstfreeNull ; try(exfalso ; congruence).
					(* firstfreeslot p <> NULL *)
					(* if first free of other PD is NOT NULL,
					then newB can't be in the two lists at s0 because of Disjoint -> False *)
					subst listoption2. subst listoption1.
					unfold Lib.disjoint in H_Disjoints0.
					specialize(H_Disjoints0 newBlockEntryAddr).
					destruct (H_Disjoints0).
					* induction (maxIdx+1). (* false induction because of fixpoint constraints *)
						** (* N=0 -> NotWellFormed *)
								cbn in *.
								congruence.
						** (* N>0 *)
								clear IHn.
								simpl. rewrite HlookupnewBs0.
								assert(HcurrNb : currnbfreeslots = nbfreeslots pdentry).
								{ unfold pdentryNbFreeSlots in *. rewrite Hpdinsertions0 in *. intuition. }
								rewrite <- HcurrNb in *.
								destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred ; try(exfalso ; congruence).
								rewrite <- HcurrNb in *. rewrite Hpred. cbn. intuition.
					* intuition.
}
	fold s1. fold s2. fold s3. fold s4. fold s5.
	set (s6 := {| currentPartition := currentPartition ?s5; memory := _ |}).
	simpl in s4.
	assert(Hfreeslotss6 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s6 (nbfreeslots p) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s5 (nbfreeslots p)).
	{
		(* DUP *)
		assert(HwellFormedNoDup : NoDupInFreeSlotsList s0) by (unfold consistency in * ; intuition).
		unfold NoDupInFreeSlotsList in *.
		specialize (HwellFormedNoDup pd p Hlookups0).
		apply getFreeSlotsListRecEqBE ; intuition.
		---	(* Lists are disjoint at s0, so newB <> firstfreeslot p *)
					assert(Hfreeslotsdisjoints0 : DisjointFreeSlotsLists s0)
						by (unfold consistency in *; intuition).
					unfold DisjointFreeSlotsLists in *.
					assert(HPDTentrypds0 : isPDT pd s0).
					{ unfold isPDT. rewrite Hlookups0. trivial. }
					rewrite <- beqAddrFalse in beqpdpd.
					pose (H_Disjoints0 := Hfreeslotsdisjoints0 pdinsertion pd HPDTs0 HPDTentrypds0 beqpdpd).
					destruct H_Disjoints0 as [listoption1 (listoption2 & H_Disjoints0)].
					destruct H_Disjoints0 as [Hlistoption1 (HwellFormedList1 & (Hlistoption2 & (HwellFormedList2 & H_Disjoints0)))].
					unfold getFreeSlotsList in Hlistoption1.
					unfold getFreeSlotsList in Hlistoption2.
					rewrite Hpdinsertions0 in *.
					rewrite Hlookups0 in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					assert(HnewBFirstFrees0P : firstfreeslot p = newBlockEntryAddr) by intuition.
						rewrite HnewBFirstFrees0PDT in *.
						rewrite HnewBFirstFrees0P in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
						rewrite FreeSlotsListRec_unroll in Hlistoption1.
						rewrite FreeSlotsListRec_unroll in Hlistoption2.
						unfold getFreeSlotsListAux in *.
						induction (maxIdx+1). (* false induction because of fixpoint constraints *)
						** (* N=0 -> NotWellFormed *)
							rewrite Hlistoption1 in *.
							cbn in HwellFormedList1.
							congruence.
						** (* N>0 *)
							clear IHn.
							cbn in *.
							rewrite HlookupnewBs0 in *.
							destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred1 ; try(exfalso ; congruence).
							*** destruct (StateLib.Index.pred (nbfreeslots p)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
									rewrite Hlistoption1 in *.
									cbn in *.
									unfold Lib.disjoint in H_Disjoints0.
									specialize(H_Disjoints0 newBlockEntryAddr).
									simpl in H_Disjoints0.
									intuition.
							*** rewrite Hlistoption1 in *.
									cbn in HwellFormedList1.
									exfalso ; congruence.
			--- unfold isBE. unfold s6. cbn.
					destruct (beqAddr pdinsertion newBlockEntryAddr) ; try(exfalso ; congruence).
					rewrite beqAddrTrue.
					cbn.
					repeat rewrite removeDupIdentity ; intuition.
			--- destruct HwellFormedNoDup as [Hoptionlist Hfreeslotss0].
					assert(HFirstFreeSlotEq : getFreeSlotsList pd s0 = getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s0 (nbfreeslots p)).
					{ unfold getFreeSlotsList. rewrite Hlookups0. rewrite HpNotNull. reflexivity. }
					rewrite HFirstFreeSlotEq in *.
					assert(HwellFormed : wellFormedFreeSlotsList Hoptionlist = False -> False) by intuition.
					apply HwellFormed. intuition. subst Hoptionlist.
					rewrite <- Hfreeslotss1 in *. rewrite <- Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *.
					rewrite <- Hfreeslotss5 in *. intuition.
			--- destruct HwellFormedNoDup as [Hoptionlist Hfreeslotss0].
					assert(HFirstFreeSlotEq : getFreeSlotsList pd s0 = getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s0 (nbfreeslots p)).
					{ unfold getFreeSlotsList. rewrite Hlookups0. rewrite HpNotNull. reflexivity. }
					rewrite HFirstFreeSlotEq in *.
					assert(HwellFormed : NoDup (filterOption  Hoptionlist)) by intuition.
					intuition. subst Hoptionlist.
					rewrite <- Hfreeslotss1 in *. rewrite <- Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *.
					rewrite <- Hfreeslotss5 in *. intuition.
			--- rewrite <- Hfreeslotss5 in *.
					rewrite <- Hfreeslotss4 in *. rewrite <- Hfreeslotss3 in *.
					rewrite Hfreeslotss2 in *. rewrite Hfreeslotss1 in *.
					(* newB is in freeslots list of pdinsertion, so can't be in other list
							because of Disjoint *)
					(* DUP from previous step *)
					assert(Hfreeslotsdisjoints0 : DisjointFreeSlotsLists s0)
						by (unfold consistency in *; intuition).
					unfold DisjointFreeSlotsLists in *.
					assert(HPDTentrypds0 : isPDT pd s0).
					{ unfold isPDT. rewrite Hlookups0. trivial. }
					rewrite <- beqAddrFalse in beqpdpd.
					pose (H_Disjoints0 := Hfreeslotsdisjoints0 pdinsertion pd HPDTs0 HPDTentrypds0 beqpdpd).
					destruct H_Disjoints0 as [listoption1 (listoption2 & H_Disjoints0)].
					destruct H_Disjoints0 as [Hlistoption1 (HwellFormedList1 & (Hlistoption2 & (HwellFormedList2 & H_Disjoints0)))].
					unfold getFreeSlotsList in Hlistoption1.
					unfold getFreeSlotsList in Hlistoption2.
					rewrite Hpdinsertions0 in *.
					rewrite Hlookups0 in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					rewrite HnewBFirstFrees0PDT in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
					rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
					destruct (beqAddr (firstfreeslot p) nullAddr) eqn:HfirstfreeNull ; try(exfalso ; congruence).
					(* firstfreeslot p <> NULL *)
					(* if first free of other PD is NOT NULL,
					then newB can't be in the two lists at s0 because of Disjoint -> False *)
					subst listoption2. subst listoption1.
					unfold Lib.disjoint in H_Disjoints0.
					specialize(H_Disjoints0 newBlockEntryAddr).
					destruct (H_Disjoints0).
					* induction (maxIdx+1). (* false induction because of fixpoint constraints *)
						** (* N=0 -> NotWellFormed *)
								cbn in *.
								congruence.
						** (* N>0 *)
								clear IHn.
								simpl. rewrite HlookupnewBs0.
								assert(HcurrNb : currnbfreeslots = nbfreeslots pdentry).
								{ unfold pdentryNbFreeSlots in *. rewrite Hpdinsertions0 in *. intuition. }
								rewrite <- HcurrNb in *.
								destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred ; try(exfalso ; congruence).
								rewrite <- HcurrNb in *. rewrite Hpred. cbn. intuition.
					* intuition.
}
	fold s1. fold s2. fold s3. fold s4. fold s5. fold s6.
	set (s7 := {| currentPartition := currentPartition ?s6; memory := _ |}).
	simpl in s5. simpl in s6.
	assert(Hfreeslotss7 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s7 (nbfreeslots p) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s6 (nbfreeslots p)).
	{
		(* DUP *)
		assert(HwellFormedNoDup : NoDupInFreeSlotsList s0) by (unfold consistency in * ; intuition).
		unfold NoDupInFreeSlotsList in *.
		specialize (HwellFormedNoDup pd p Hlookups0).
		apply getFreeSlotsListRecEqBE ; intuition.
		---	(* Lists are disjoint at s0, so newB <> firstfreeslot p *)
					assert(Hfreeslotsdisjoints0 : DisjointFreeSlotsLists s0)
						by (unfold consistency in *; intuition).
					unfold DisjointFreeSlotsLists in *.
					assert(HPDTentrypds0 : isPDT pd s0).
					{ unfold isPDT. rewrite Hlookups0. trivial. }
					rewrite <- beqAddrFalse in beqpdpd.
					pose (H_Disjoints0 := Hfreeslotsdisjoints0 pdinsertion pd HPDTs0 HPDTentrypds0 beqpdpd).
					destruct H_Disjoints0 as [listoption1 (listoption2 & H_Disjoints0)].
					destruct H_Disjoints0 as [Hlistoption1 (HwellFormedList1 & (Hlistoption2 & (HwellFormedList2 & H_Disjoints0)))].
					unfold getFreeSlotsList in Hlistoption1.
					unfold getFreeSlotsList in Hlistoption2.
					rewrite Hpdinsertions0 in *.
					rewrite Hlookups0 in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					assert(HnewBFirstFrees0P : firstfreeslot p = newBlockEntryAddr) by intuition.
						rewrite HnewBFirstFrees0PDT in *.
						rewrite HnewBFirstFrees0P in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
						rewrite FreeSlotsListRec_unroll in Hlistoption1.
						rewrite FreeSlotsListRec_unroll in Hlistoption2.
						unfold getFreeSlotsListAux in *.
						induction (maxIdx+1). (* false induction because of fixpoint constraints *)
						** (* N=0 -> NotWellFormed *)
							rewrite Hlistoption1 in *.
							cbn in HwellFormedList1.
							congruence.
						** (* N>0 *)
							clear IHn.
							cbn in *.
							rewrite HlookupnewBs0 in *.
							destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred1 ; try(exfalso ; congruence).
							*** destruct (StateLib.Index.pred (nbfreeslots p)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
									rewrite Hlistoption1 in *.
									cbn in *.
									unfold Lib.disjoint in H_Disjoints0.
									specialize(H_Disjoints0 newBlockEntryAddr).
									simpl in H_Disjoints0.
									intuition.
							*** rewrite Hlistoption1 in *.
									cbn in HwellFormedList1.
									exfalso ; congruence.
			--- unfold isBE. unfold s7. cbn.
					destruct (beqAddr pdinsertion newBlockEntryAddr) ; try(exfalso ; congruence).
					rewrite beqAddrTrue.
					cbn.
					repeat rewrite removeDupIdentity ; intuition.
			--- destruct HwellFormedNoDup as [Hoptionlist Hfreeslotss0].
					assert(HFirstFreeSlotEq : getFreeSlotsList pd s0 = getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s0 (nbfreeslots p)).
					{ unfold getFreeSlotsList. rewrite Hlookups0. rewrite HpNotNull. reflexivity. }
					rewrite HFirstFreeSlotEq in *.
					assert(HwellFormed : wellFormedFreeSlotsList Hoptionlist = False -> False) by intuition.
					apply HwellFormed. intuition. subst Hoptionlist.
					rewrite <- Hfreeslotss1 in *. rewrite <- Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *.
					rewrite <- Hfreeslotss5 in *. rewrite <- Hfreeslotss6 in *. intuition.
			--- destruct HwellFormedNoDup as [Hoptionlist Hfreeslotss0].
					assert(HFirstFreeSlotEq : getFreeSlotsList pd s0 = getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s0 (nbfreeslots p)).
					{ unfold getFreeSlotsList. rewrite Hlookups0. rewrite HpNotNull. reflexivity. }
					rewrite HFirstFreeSlotEq in *.
					assert(HwellFormed : NoDup (filterOption  Hoptionlist)) by intuition.
					intuition. subst Hoptionlist.
					rewrite <- Hfreeslotss1 in *. rewrite <- Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *.
					rewrite <- Hfreeslotss5 in *. rewrite <- Hfreeslotss6 in *. intuition.
			--- rewrite <- Hfreeslotss6 in *. rewrite <- Hfreeslotss5 in *.
					rewrite <- Hfreeslotss4 in *. rewrite <- Hfreeslotss3 in *.
					rewrite Hfreeslotss2 in *. rewrite Hfreeslotss1 in *.
					(* newB is in freeslots list of pdinsertion, so can't be in other list
							because of Disjoint *)
					(* DUP from previous step *)
					assert(Hfreeslotsdisjoints0 : DisjointFreeSlotsLists s0)
						by (unfold consistency in *; intuition).
					unfold DisjointFreeSlotsLists in *.
					assert(HPDTentrypds0 : isPDT pd s0).
					{ unfold isPDT. rewrite Hlookups0. trivial. }
					rewrite <- beqAddrFalse in beqpdpd.
					pose (H_Disjoints0 := Hfreeslotsdisjoints0 pdinsertion pd HPDTs0 HPDTentrypds0 beqpdpd).
					destruct H_Disjoints0 as [listoption1 (listoption2 & H_Disjoints0)].
					destruct H_Disjoints0 as [Hlistoption1 (HwellFormedList1 & (Hlistoption2 & (HwellFormedList2 & H_Disjoints0)))].
					unfold getFreeSlotsList in Hlistoption1.
					unfold getFreeSlotsList in Hlistoption2.
					rewrite Hpdinsertions0 in *.
					rewrite Hlookups0 in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					rewrite HnewBFirstFrees0PDT in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
					rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
					destruct (beqAddr (firstfreeslot p) nullAddr) eqn:HfirstfreeNull ; try(exfalso ; congruence).
					(* firstfreeslot p <> NULL *)
					(* if first free of other PD is NOT NULL,
					then newB can't be in the two lists at s0 because of Disjoint -> False *)
					subst listoption2. subst listoption1.
					unfold Lib.disjoint in H_Disjoints0.
					specialize(H_Disjoints0 newBlockEntryAddr).
					destruct (H_Disjoints0).
					* induction (maxIdx+1). (* false induction because of fixpoint constraints *)
						** (* N=0 -> NotWellFormed *)
								cbn in *.
								congruence.
						** (* N>0 *)
								clear IHn.
								simpl. rewrite HlookupnewBs0.
								assert(HcurrNb : currnbfreeslots = nbfreeslots pdentry).
								{ unfold pdentryNbFreeSlots in *. rewrite Hpdinsertions0 in *. intuition. }
								rewrite <- HcurrNb in *.
								destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred ; try(exfalso ; congruence).
								rewrite <- HcurrNb in *. rewrite Hpred. cbn. intuition.
					* intuition.
}
	fold s1. fold s2. fold s3. fold s4. fold s5. fold s6. fold s7.
	set (s8 := {| currentPartition := currentPartition ?s7; memory := _ |}).
	simpl in s7.
	assert(Hfreeslotss8 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s8 (nbfreeslots p) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s7 (nbfreeslots p)).
	{
		(* DUP *)
				assert(HwellFormedNoDup : NoDupInFreeSlotsList s0) by (unfold consistency in * ; intuition).
				unfold NoDupInFreeSlotsList in *.
				specialize (HwellFormedNoDup pd p Hlookups0).
				apply getFreeSlotsListRecEqBE ; intuition.
				---	(* Lists are disjoint at s0, so newB <> firstfreeslot p *)
					assert(Hfreeslotsdisjoints0 : DisjointFreeSlotsLists s0)
						by (unfold consistency in *; intuition).
					unfold DisjointFreeSlotsLists in *.
					assert(HPDTentrypds0 : isPDT pd s0).
					{ unfold isPDT. rewrite Hlookups0. trivial. }
					rewrite <- beqAddrFalse in beqpdpd.
					pose (H_Disjoints0 := Hfreeslotsdisjoints0 pdinsertion pd HPDTs0 HPDTentrypds0 beqpdpd).
					destruct H_Disjoints0 as [listoption1 (listoption2 & H_Disjoints0)].
					destruct H_Disjoints0 as [Hlistoption1 (HwellFormedList1 & (Hlistoption2 & (HwellFormedList2 & H_Disjoints0)))].
					unfold getFreeSlotsList in Hlistoption1.
					unfold getFreeSlotsList in Hlistoption2.
					rewrite Hpdinsertions0 in *.
					rewrite Hlookups0 in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					assert(HnewBFirstFrees0P : firstfreeslot p = newBlockEntryAddr) by intuition.
						rewrite HnewBFirstFrees0PDT in *.
						rewrite HnewBFirstFrees0P in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
						rewrite FreeSlotsListRec_unroll in Hlistoption1.
						rewrite FreeSlotsListRec_unroll in Hlistoption2.
						unfold getFreeSlotsListAux in *.
						induction (maxIdx+1). (* false induction because of fixpoint constraints *)
						** (* N=0 -> NotWellFormed *)
							rewrite Hlistoption1 in *.
							cbn in HwellFormedList1.
							congruence.
						** (* N>0 *)
							clear IHn.
							cbn in *.
							rewrite HlookupnewBs0 in *.
							destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred1 ; try(exfalso ; congruence).
							*** destruct (StateLib.Index.pred (nbfreeslots p)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
									rewrite Hlistoption1 in *.
									cbn in *.
									unfold Lib.disjoint in H_Disjoints0.
									specialize(H_Disjoints0 newBlockEntryAddr).
									simpl in H_Disjoints0.
									intuition.
							*** rewrite Hlistoption1 in *.
									cbn in HwellFormedList1.
									exfalso ; congruence.
			--- unfold isBE. unfold s8. cbn.
					destruct (beqAddr pdinsertion newBlockEntryAddr) ; try(exfalso ; congruence).
					rewrite beqAddrTrue.
					cbn.
					repeat rewrite removeDupIdentity ; intuition.
			--- destruct HwellFormedNoDup as [Hoptionlist Hfreeslotss0].
					assert(HFirstFreeSlotEq : getFreeSlotsList pd s0 = getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s0 (nbfreeslots p)).
					{ unfold getFreeSlotsList. rewrite Hlookups0. rewrite HpNotNull. reflexivity. }
					rewrite HFirstFreeSlotEq in *.
					assert(HwellFormed : wellFormedFreeSlotsList Hoptionlist = False -> False) by intuition.
					apply HwellFormed. intuition. subst Hoptionlist.
					rewrite <- Hfreeslotss1 in *. rewrite <- Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *.
					rewrite <- Hfreeslotss5 in *. rewrite <- Hfreeslotss6 in *.
					rewrite <- Hfreeslotss7 in *. intuition.
			--- destruct HwellFormedNoDup as [Hoptionlist Hfreeslotss0].
					assert(HFirstFreeSlotEq : getFreeSlotsList pd s0 = getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s0 (nbfreeslots p)).
					{ unfold getFreeSlotsList. rewrite Hlookups0. rewrite HpNotNull. reflexivity. }
					rewrite HFirstFreeSlotEq in *.
					assert(HwellFormed : NoDup (filterOption  Hoptionlist)) by intuition.
					intuition. subst Hoptionlist.
					rewrite <- Hfreeslotss1 in *. rewrite <- Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *.
					rewrite <- Hfreeslotss5 in *. rewrite <- Hfreeslotss6 in *.
					rewrite <- Hfreeslotss7 in *. intuition.
			--- rewrite <- Hfreeslotss7 in *.
					rewrite <- Hfreeslotss6 in *. rewrite <- Hfreeslotss5 in *.
					rewrite <- Hfreeslotss4 in *. rewrite <- Hfreeslotss3 in *.
					rewrite Hfreeslotss2 in *. rewrite Hfreeslotss1 in *.
					(* newB is in freeslots list of pdinsertion, so can't be in other list
							because of Disjoint *)
					(* DUP from previous step *)
					assert(Hfreeslotsdisjoints0 : DisjointFreeSlotsLists s0)
						by (unfold consistency in *; intuition).
					unfold DisjointFreeSlotsLists in *.
					assert(HPDTentrypds0 : isPDT pd s0).
					{ unfold isPDT. rewrite Hlookups0. trivial. }
					rewrite <- beqAddrFalse in beqpdpd.
					pose (H_Disjoints0 := Hfreeslotsdisjoints0 pdinsertion pd HPDTs0 HPDTentrypds0 beqpdpd).
					destruct H_Disjoints0 as [listoption1 (listoption2 & H_Disjoints0)].
					destruct H_Disjoints0 as [Hlistoption1 (HwellFormedList1 & (Hlistoption2 & (HwellFormedList2 & H_Disjoints0)))].
					unfold getFreeSlotsList in Hlistoption1.
					unfold getFreeSlotsList in Hlistoption2.
					rewrite Hpdinsertions0 in *.
					rewrite Hlookups0 in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					rewrite HnewBFirstFrees0PDT in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
					rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
					destruct (beqAddr (firstfreeslot p) nullAddr) eqn:HfirstfreeNull ; try(exfalso ; congruence).
					(* firstfreeslot p <> NULL *)
					(* if first free of other PD is NOT NULL,
					then newB can't be in the two lists at s0 because of Disjoint -> False *)
					subst listoption2. subst listoption1.
					unfold Lib.disjoint in H_Disjoints0.
					specialize(H_Disjoints0 newBlockEntryAddr).
					destruct (H_Disjoints0).
					* induction (maxIdx+1). (* false induction because of fixpoint constraints *)
						** (* N=0 -> NotWellFormed *)
								cbn in *.
								congruence.
						** (* N>0 *)
								clear IHn.
								simpl. rewrite HlookupnewBs0.
								assert(HcurrNb : currnbfreeslots = nbfreeslots pdentry).
								{ unfold pdentryNbFreeSlots in *. rewrite Hpdinsertions0 in *. intuition. }
								rewrite <- HcurrNb in *.
								destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred ; try(exfalso ; congruence).
								rewrite <- HcurrNb in *. rewrite Hpred. cbn. intuition.
					* intuition.
}
	fold s1. fold s2. fold s3. fold s4. fold s5. fold s6. fold s7. fold s8.
	set (s9 := {| currentPartition := currentPartition ?s8; memory := _ |}).
	simpl in s7.
	assert(Hfreeslotss9 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s9 (nbfreeslots p) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s8 (nbfreeslots p)).
	{
		(* DUP *)
				assert(HwellFormedNoDup : NoDupInFreeSlotsList s0) by (unfold consistency in * ; intuition).
				unfold NoDupInFreeSlotsList in *.
				specialize (HwellFormedNoDup pd p Hlookups0).
				apply getFreeSlotsListRecEqBE ; intuition.
				---	(* Lists are disjoint at s0, so newB <> firstfreeslot p *)
					assert(Hfreeslotsdisjoints0 : DisjointFreeSlotsLists s0)
						by (unfold consistency in *; intuition).
					unfold DisjointFreeSlotsLists in *.
					assert(HPDTentrypds0 : isPDT pd s0).
					{ unfold isPDT. rewrite Hlookups0. trivial. }
					rewrite <- beqAddrFalse in beqpdpd.
					pose (H_Disjoints0 := Hfreeslotsdisjoints0 pdinsertion pd HPDTs0 HPDTentrypds0 beqpdpd).
					destruct H_Disjoints0 as [listoption1 (listoption2 & H_Disjoints0)].
					destruct H_Disjoints0 as [Hlistoption1 (HwellFormedList1 & (Hlistoption2 & (HwellFormedList2 & H_Disjoints0)))].
					unfold getFreeSlotsList in Hlistoption1.
					unfold getFreeSlotsList in Hlistoption2.
					rewrite Hpdinsertions0 in *.
					rewrite Hlookups0 in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					assert(HnewBFirstFrees0P : firstfreeslot p = newBlockEntryAddr) by intuition.
						rewrite HnewBFirstFrees0PDT in *.
						rewrite HnewBFirstFrees0P in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
						rewrite FreeSlotsListRec_unroll in Hlistoption1.
						rewrite FreeSlotsListRec_unroll in Hlistoption2.
						unfold getFreeSlotsListAux in *.
						induction (maxIdx+1). (* false induction because of fixpoint constraints *)
						** (* N=0 -> NotWellFormed *)
							rewrite Hlistoption1 in *.
							cbn in HwellFormedList1.
							congruence.
						** (* N>0 *)
							clear IHn.
							cbn in *.
							rewrite HlookupnewBs0 in *.
							destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred1 ; try(exfalso ; congruence).
							*** destruct (StateLib.Index.pred (nbfreeslots p)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
									rewrite Hlistoption1 in *.
									cbn in *.
									unfold Lib.disjoint in H_Disjoints0.
									specialize(H_Disjoints0 newBlockEntryAddr).
									simpl in H_Disjoints0.
									intuition.
							*** rewrite Hlistoption1 in *.
									cbn in HwellFormedList1.
									exfalso ; congruence.
			--- unfold isBE. unfold s9. cbn.
					destruct (beqAddr pdinsertion newBlockEntryAddr) ; try(exfalso ; congruence).
					rewrite beqAddrTrue.
					cbn.
					repeat rewrite removeDupIdentity ; intuition.
			--- destruct HwellFormedNoDup as [Hoptionlist Hfreeslotss0].
					assert(HFirstFreeSlotEq : getFreeSlotsList pd s0 = getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s0 (nbfreeslots p)).
					{ unfold getFreeSlotsList. rewrite Hlookups0. rewrite HpNotNull. reflexivity. }
					rewrite HFirstFreeSlotEq in *.
					assert(HwellFormed : wellFormedFreeSlotsList Hoptionlist = False -> False) by intuition.
					apply HwellFormed. intuition. subst Hoptionlist.
					rewrite <- Hfreeslotss1 in *. rewrite <- Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *.
					rewrite <- Hfreeslotss5 in *. rewrite <- Hfreeslotss6 in *.
					rewrite <- Hfreeslotss7 in *. rewrite <- Hfreeslotss8 in *. intuition.
			--- destruct HwellFormedNoDup as [Hoptionlist Hfreeslotss0].
					assert(HFirstFreeSlotEq : getFreeSlotsList pd s0 = getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s0 (nbfreeslots p)).
					{ unfold getFreeSlotsList. rewrite Hlookups0. rewrite HpNotNull. reflexivity. }
					rewrite HFirstFreeSlotEq in *.
					assert(HwellFormed : NoDup (filterOption  Hoptionlist)) by intuition.
					intuition. subst Hoptionlist.
					rewrite <- Hfreeslotss1 in *. rewrite <- Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *.
					rewrite <- Hfreeslotss5 in *. rewrite <- Hfreeslotss6 in *.
					rewrite <- Hfreeslotss7 in *. rewrite <- Hfreeslotss8 in *. intuition.
			--- rewrite <- Hfreeslotss8 in *. rewrite <- Hfreeslotss7 in *.
					rewrite <- Hfreeslotss6 in *. rewrite <- Hfreeslotss5 in *.
					rewrite <- Hfreeslotss4 in *. rewrite <- Hfreeslotss3 in *.
					rewrite Hfreeslotss2 in *. rewrite Hfreeslotss1 in *.
					(* newB is in freeslots list of pdinsertion, so can't be in other list
							because of Disjoint *)
					(* DUP from previous step *)
					assert(Hfreeslotsdisjoints0 : DisjointFreeSlotsLists s0)
						by (unfold consistency in *; intuition).
					unfold DisjointFreeSlotsLists in *.
					assert(HPDTentrypds0 : isPDT pd s0).
					{ unfold isPDT. rewrite Hlookups0. trivial. }
					rewrite <- beqAddrFalse in beqpdpd.
					pose (H_Disjoints0 := Hfreeslotsdisjoints0 pdinsertion pd HPDTs0 HPDTentrypds0 beqpdpd).
					destruct H_Disjoints0 as [listoption1 (listoption2 & H_Disjoints0)].
					destruct H_Disjoints0 as [Hlistoption1 (HwellFormedList1 & (Hlistoption2 & (HwellFormedList2 & H_Disjoints0)))].
					unfold getFreeSlotsList in Hlistoption1.
					unfold getFreeSlotsList in Hlistoption2.
					rewrite Hpdinsertions0 in *.
					rewrite Hlookups0 in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					rewrite HnewBFirstFrees0PDT in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
					rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
					destruct (beqAddr (firstfreeslot p) nullAddr) eqn:HfirstfreeNull ; try(exfalso ; congruence).
					(* firstfreeslot p <> NULL *)
					(* if first free of other PD is NOT NULL,
					then newB can't be in the two lists at s0 because of Disjoint -> False *)
					subst listoption2. subst listoption1.
					unfold Lib.disjoint in H_Disjoints0.
					specialize(H_Disjoints0 newBlockEntryAddr).
					destruct (H_Disjoints0).
					* induction (maxIdx+1). (* false induction because of fixpoint constraints *)
						** (* N=0 -> NotWellFormed *)
								cbn in *.
								congruence.
						** (* N>0 *)
								clear IHn.
								simpl. rewrite HlookupnewBs0.
								assert(HcurrNb : currnbfreeslots = nbfreeslots pdentry).
								{ unfold pdentryNbFreeSlots in *. rewrite Hpdinsertions0 in *. intuition. }
								rewrite <- HcurrNb in *.
								destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred ; try(exfalso ; congruence).
								rewrite <- HcurrNb in *. rewrite Hpred. cbn. intuition.
					* intuition.
}
	fold s1. fold s2. fold s3. fold s4. fold s5. fold s6. fold s7. fold s8. fold s9.
	set (s10 := {| currentPartition := currentPartition ?s9; memory := _ |}).
	simpl in s8. simpl in s9.
	assert(Hfreeslotss10 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s10 (nbfreeslots p) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s9 (nbfreeslots p)).
	{			assert(HSCEs9 : isSCE sceaddr s9).
				{ unfold isSCE. unfold s9. cbn. rewrite beqAddrTrue.
					destruct (beqAddr newBlockEntryAddr sceaddr) eqn:Hf ; try(exfalso ; congruence).
					rewrite <- beqAddrFalse in *.
					repeat rewrite removeDupIdentity ; intuition.
					destruct (beqAddr pdinsertion newBlockEntryAddr) eqn:Hff ; try(exfalso ; congruence).
					rewrite <- DependentTypeLemmas.beqAddrTrue in Hff. congruence.
					cbn.
					destruct (beqAddr pdinsertion sceaddr) eqn:Hfff ; try(exfalso ; congruence).
					rewrite <- DependentTypeLemmas.beqAddrTrue in Hfff. congruence.
					rewrite beqAddrTrue.
					rewrite <- beqAddrFalse in *.
					repeat rewrite removeDupIdentity ; intuition.
				}
				apply getFreeSlotsListRecEqSCE.
				--- 	intro Hfirstsceeq.
						assert(HFirstFreeSlotPointerIsBEAndFreeSlots0 : FirstFreeSlotPointerIsBEAndFreeSlot s0)
							by (unfold consistency in * ; intuition).
						unfold FirstFreeSlotPointerIsBEAndFreeSlot in *.
						specialize (HFirstFreeSlotPointerIsBEAndFreeSlots0 pd p Hlookups0).
						destruct HFirstFreeSlotPointerIsBEAndFreeSlots0.
						---- intro HfirstfreeNull.
								assert(HnullAddrExistss0 : nullAddrExists s0)
									by (unfold consistency in * ; intuition).
								unfold nullAddrExists in *.
								unfold isSCE in *.
								unfold isPADDR in *.
								rewrite HfirstfreeNull in *. rewrite <- Hfirstsceeq in *.
								destruct (lookup nullAddr (memory s0) beqAddr) ; try(exfalso ; congruence).
								destruct v ; try(exfalso ; congruence).
						---- rewrite Hfirstsceeq in *.
								unfold isSCE in *.
								unfold isBE in *.
								destruct (lookup sceaddr (memory s0) beqAddr) ; try (exfalso ; congruence).
								destruct v ; try(exfalso ; congruence).
				--- unfold isBE. unfold isSCE in HSCEs9.
						destruct (lookup sceaddr (memory s9) beqAddr) eqn:Hlookupsces9 ; try(exfalso ; congruence).
						destruct v ; try(exfalso ; congruence).
						intuition.
				--- unfold isPADDR. unfold isSCE in HSCEs9.
						destruct (lookup sceaddr (memory s9) beqAddr) eqn:Hlookupsces9 ; try(exfalso ; congruence).
						destruct v ; try(exfalso ; congruence).
						intuition.
}
	fold s1. fold s2. fold s3. fold s4. fold s5. fold s6. fold s7. fold s8. fold s9.
	fold s10.

	intuition.
	assert(HcurrLtmaxIdx : nbfreeslots p <= maxIdx).
	{ intuition. apply IdxLtMaxIdx. }
	lia.
}
destruct Hs' as [s1 (s2 & (s3 & (s4 & (s5 & (s6 & (s7 & (s8 & (s9 & (s10 &
									(n1 & (nbleft & (Hnbleft & Hstates))))))))))))].
assert(HsEq : s10 = s).
{ intuition. subst s1. subst s2. subst s3. subst s4. subst s5. subst s6.
	subst s7. subst s8. subst s9. subst s10.
	rewrite Hs. f_equal.
}
rewrite HsEq in *.
assert(HfreeslotsEq : getFreeSlotsListRec n1 (firstfreeslot p) s (nbfreeslots p) =
											getFreeSlotsListRec (maxIdx+1) (firstfreeslot p) s0 (nbfreeslots p)).
{
	intuition.
	subst nbleft.
	(* rewrite all previous getFreeSlotsListRec equalities *)
	rewrite <- H33. rewrite <- H36. rewrite <- H38. rewrite <- H40. rewrite <- H42.
	rewrite <- H44.	rewrite <- H46. rewrite <- H48. rewrite <- H50. rewrite <- H53.
	reflexivity.
}
assert (HfreeslotsEqn1 : getFreeSlotsListRec n1 (firstfreeslot p) s (nbfreeslots p)
													= getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s (nbfreeslots p)).
{ eapply getFreeSlotsListRecEqN ; intuition.
	subst nbleft. lia.
	assert (HnbLtmaxIdx : nbfreeslots p <= maxIdx) by apply IdxLtMaxIdx.
	lia.
}
rewrite <- HfreeslotsEq. rewrite HfreeslotsEqn1. intuition.
}
specialize (Hcons0 optionfreeslotslist freeslotslist HPDTpds0 HfreeSlotsListEq).
assert(HInfreeSlot : freeslotslist = filterOption optionfreeslotslist /\
         In freeslotaddr freeslotslist) by intuition.
specialize (Hcons0 HInfreeSlot HfreeSlotNotNull).
(* dismiss all impossible values for freeslotaddr except newB *)
destruct (beqAddr sceaddr freeslotaddr) eqn:beqfscefree; try(exfalso ; congruence).
	---- (* sceaddr = freeslotaddr *)
				rewrite <- DependentTypeLemmas.beqAddrTrue in beqfscefree.
				rewrite <- beqfscefree in *.
				unfold isSCE in *.
				unfold isFreeSlot in *.
				destruct (lookup sceaddr (memory s0) beqAddr) ; try(exfalso ; congruence).
				destruct v ; try(exfalso ; congruence).
	---- (* sceaddr <> freeslotaddr *)
				destruct (beqAddr pdinsertion freeslotaddr) eqn:beqfpdfree; try(exfalso ; congruence).
				----- (* pdinsertion = freeslotaddr *)
							rewrite <- DependentTypeLemmas.beqAddrTrue in beqfpdfree.
							rewrite <- beqfpdfree in *.
							unfold isPDT in *.
							unfold isFreeSlot in *.
							destruct (lookup pdinsertion (memory s0) beqAddr) ; try(exfalso ; congruence).
							destruct v ; try(exfalso ; congruence).
				----- (* pdinsertion <> freeslotaddr *)
							destruct (beqAddr newBlockEntryAddr freeslotaddr) eqn:beqfnewBfree; try(exfalso ; congruence).
							------ (* newBlockEntryAddr = freeslotaddr *)
											rewrite <- DependentTypeLemmas.beqAddrTrue in beqfnewBfree.
											rewrite <- beqfnewBfree in *.
											(* if newB belongs to pd's free slots list, then it was the case at s0
													but that means newB was at the same time in pd's and pdinsertion's free slots list
													which is false because they are disjoint -> contradiction *)
											assert(H_Disjoints0 : DisjointFreeSlotsLists s0)
																by (unfold consistency in * ; intuition).
											unfold DisjointFreeSlotsLists in *.
											assert(HPDTNotEq : pdinsertion <> pd)
														by (rewrite <- beqAddrFalse in * ; intuition).
											specialize (H_Disjoints0 pdinsertion pd HPDTs0 HPDTpds0 HPDTNotEq).
											destruct H_Disjoints0 as [listoption1 (listoption2 & H_Disjoints0)].
											destruct H_Disjoints0 as [Hlistoption1 (HwellFormedList1 & (Hlistoption2 & (HwellFormedList2 & H_Disjoints0)))].
											assert(Hcontra : In newBlockEntryAddr (filterOption listoption1)).
											{ subst listoption1.
												unfold getFreeSlotsList in *.
												rewrite Hpdinsertions0 in *.
												rewrite <- HnewB in *.
												destruct (beqAddr newBlockEntryAddr nullAddr) eqn:HnewNotNull ; try(exfalso ; congruence).
												rewrite <- DependentTypeLemmas.beqAddrTrue in HnewNotNull. congruence.
												rewrite FreeSlotsListRec_unroll.
												unfold getFreeSlotsListAux in *.
												induction (maxIdx+1). (* false induction because of fixpoint constraints *)
												** (* N=0 -> NotWellFormed *)
													cbn in *. congruence.
												** (* N>0 *)
													clear IHn.
													cbn in *.
													rewrite HlookupnewBs0 in *.
													destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred1 ; try(exfalso ; congruence).
													*** cbn. intuition.
													*** cbn in *.
															exfalso ; congruence.
											}
											assert(HfreeSlotsListpdEq : getFreeSlotsList pd s0 = getFreeSlotsList pd s).
											{ subst optionfreeslotslist. intuition. }
											rewrite <- HfreeSlotsListpdEq in *.
											assert(Hcontra' : In newBlockEntryAddr (filterOption listoption2)).
											{ subst listoption2.
												unfold getFreeSlotsList in *.
												apply isPDTLookupEq in HPDTpds0. destruct HPDTpds0 as [pdentrys0 Hlookuppds0].
												rewrite HlookupEq in *. rewrite Hlookuppds0 in *.
												destruct (beqAddr (firstfreeslot pdentrys0) nullAddr) eqn:HnewNotNull ; try(exfalso ; congruence).
												rewrite <- DependentTypeLemmas.beqAddrTrue in HnewNotNull.
												subst optionfreeslotslist. subst freeslotslist. intuition.
												subst freeslotslist. subst optionfreeslotslist. intuition.
											}
											assert(HlistEq : optionfreeslotslist = listoption2).
											{ subst listoption2. intuition. }
											rewrite HlistEq in *.
											contradict H_Disjoints0.
											unfold Lib.disjoint. intuition.
											specialize (H30 newBlockEntryAddr Hcontra Hcontra'). congruence.
							------ (* newBlockEntryAddr <> freeslotaddr *)
											(* no entry left to try out -> leads to s0 *)
											rewrite Hs. unfold isFreeSlot.
											cbn. rewrite beqAddrTrue.
											rewrite beqfscefree.
											destruct (beqAddr newBlockEntryAddr sceaddr) eqn:newsce ; try(exfalso ; congruence).
											rewrite beqAddrTrue.
											cbn. rewrite beqfnewBfree.
											rewrite <- beqAddrFalse in *.
											rewrite removeDupIdentity ; try congruence.
											rewrite removeDupIdentity ; try congruence.
											rewrite removeDupIdentity ; try congruence.
											rewrite removeDupIdentity ; try congruence.
											rewrite removeDupIdentity ; try congruence.
											rewrite removeDupIdentity ; try congruence.
											rewrite removeDupIdentity ; try congruence.
											destruct (beqAddr pdinsertion newBlockEntryAddr) eqn:pdnew ; try(exfalso ; congruence).
											rewrite <- DependentTypeLemmas.beqAddrTrue in pdnew. congruence.
											cbn.
											destruct (beqAddr pdinsertion freeslotaddr) eqn:pdffentry; try(exfalso ; congruence).
											rewrite <- DependentTypeLemmas.beqAddrTrue in pdffentry. congruence.
											rewrite <- beqAddrFalse in *.
											rewrite removeDupIdentity ; try congruence.
											rewrite removeDupIdentity ; try congruence.
											rewrite removeDupIdentity ; try congruence.
											unfold isFreeSlot in Hcons0.
											destruct (lookup freeslotaddr (memory s0) beqAddr) eqn:HfreeSlots0 ; try(exfalso ; congruence).
											destruct v ; try(exfalso ; congruence).
											destruct (beqAddr sceaddr (CPaddr (freeslotaddr + sh1offset))) eqn:beqscefreesh1 ; try(exfalso ; congruence).
											rewrite <- DependentTypeLemmas.beqAddrTrue in beqscefreesh1.
											rewrite <- beqscefreesh1 in *.
											unfold isFreeSlot in *.
											unfold isSCE in *.
											destruct (lookup sceaddr (memory s0) beqAddr) ; try(exfalso ; congruence).
											destruct v ; try(exfalso ; congruence).
											destruct (beqAddr newBlockEntryAddr (CPaddr (freeslotaddr + sh1offset))) eqn:beqscefreesc ; try(exfalso ; congruence).
											rewrite <- DependentTypeLemmas.beqAddrTrue in beqscefreesc.
											rewrite <- beqscefreesc in *.
											unfold isFreeSlot in *.
											unfold isBE in *.
											destruct (lookup newBlockEntryAddr (memory s0) beqAddr) ; try(exfalso ; congruence).
											destruct v ; try(exfalso ; congruence).
											rewrite <- beqAddrFalse in *.
											rewrite removeDupIdentity ; try congruence.
											rewrite removeDupIdentity ; try congruence.
											rewrite removeDupIdentity ; try congruence.
											rewrite removeDupIdentity ; try congruence.
											rewrite removeDupIdentity ; try congruence.
											rewrite removeDupIdentity ; try congruence.
											destruct (beqAddr pdinsertion newBlockEntryAddr) eqn:pdnewB; try(exfalso ; congruence).
											rewrite <- DependentTypeLemmas.beqAddrTrue in pdnewB. congruence.
											cbn.
											destruct (beqAddr pdinsertion (CPaddr (freeslotaddr + sh1offset))) eqn:beqpdfreesh1 ; try(exfalso ; congruence).
											rewrite <- DependentTypeLemmas.beqAddrTrue in beqpdfreesh1.
											rewrite <- beqpdfreesh1 in *.
											unfold isFreeSlot in *.
											unfold isPDT in *.
											destruct (lookup pdinsertion (memory s0) beqAddr) ; try(exfalso ; congruence).
											destruct v ; try(exfalso ; congruence).
											rewrite removeDupIdentity ; try congruence.
											rewrite removeDupIdentity ; try congruence.
											rewrite removeDupIdentity ; try congruence.
											rewrite <- beqAddrFalse in *.
											rewrite removeDupIdentity ; try congruence.
											destruct (lookup (CPaddr (freeslotaddr + sh1offset)) (memory s0) beqAddr) ; try(exfalso ; congruence).
											destruct v ; try(exfalso ; congruence).
											destruct (beqAddr sceaddr (CPaddr (freeslotaddr + scoffset))) eqn:beqscefssc ; try(exfalso ; congruence).
											(* show sceaddr must be equal to freeslot which is false *)
											rewrite <- DependentTypeLemmas.beqAddrTrue in beqscefssc.
											assert(HSCEOffset : sceaddr = CPaddr (newBlockEntryAddr + scoffset)) by intuition.
											rewrite HSCEOffset in beqscefssc.
											contradict beqscefssc.
											unfold nullAddrExists in *. unfold isPADDR in *.
											unfold CPaddr.
											destruct (le_dec (newBlockEntryAddr + scoffset) maxAddr) eqn:Hj.
											* destruct (le_dec (freeslotaddr + scoffset) maxAddr) eqn:Hk.
												** simpl in *. intro Hfalse.
													inversion Hfalse as [Heq].
													rewrite PeanoNat.Nat.add_cancel_r in Heq.
													apply CPaddrInjectionNat in Heq.
													repeat rewrite paddrEqId in Heq.
													congruence.
												** 	intro Hfalse.
														inversion Hfalse as [Heq].
														assert(HeqNull : CPaddr(newBlockEntryAddr + scoffset) = nullAddr).
														{ rewrite nullAddrIs0.
															apply CPaddrInjectionNat in Heq.
															intuition.
														}
														rewrite HeqNull in *.
														rewrite HSCEOffset in *.
														unfold isSCE in *.
														destruct (lookup nullAddr (memory s) beqAddr) ; try(exfalso ; congruence).
														destruct v ; try(exfalso ; congruence).
											* assert(Heq : CPaddr(newBlockEntryAddr + scoffset) = nullAddr).
												{ rewrite nullAddrIs0.
													unfold CPaddr. rewrite Hj.
													destruct (le_dec 0 maxAddr) ; intuition.
													f_equal. apply proof_irrelevance.
												}
												rewrite Heq in *.
												rewrite HSCEOffset in *.
												unfold isSCE in *.
												destruct (lookup nullAddr (memory s) beqAddr) ; try(exfalso ; congruence).
												destruct v ; try(exfalso ; congruence).
											* destruct (beqAddr newBlockEntryAddr (CPaddr (freeslotaddr + scoffset))) eqn:beqnewBfssc ; try(exfalso ; congruence).
												------- (* newBlockEntryAddr = (CPaddr (freeslotaddr + scoffset)) *)
																rewrite <- DependentTypeLemmas.beqAddrTrue in beqnewBfssc.
																rewrite <- beqnewBfssc in *.
																destruct (lookup newBlockEntryAddr (memory s0) beqAddr) ; try(exfalso ; congruence).
																destruct v ; try(exfalso ; congruence).
												------- (* newBlockEntryAddr <> (CPaddr (freeslotaddr + scoffset)) *)
																rewrite <- beqAddrFalse in *.
																repeat rewrite removeDupIdentity ; try congruence.
																destruct (beqAddr pdinsertion newBlockEntryAddr) eqn:Hf; try(exfalso ; congruence).
																rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
																rewrite <- beqAddrFalse in *.
																repeat rewrite removeDupIdentity ; try congruence.
																cbn.
																destruct (beqAddr pdinsertion (CPaddr (freeslotaddr + scoffset))) eqn:beqpdfssc ; try (exfalso ; congruence).
																-------- (* pdinsertion = (CPaddr (freeslotaddr + scoffset)) *)
																					rewrite <- DependentTypeLemmas.beqAddrTrue in beqpdfssc.
																					rewrite <- beqpdfssc in *.
																					destruct (lookup pdinsertion (memory s0) beqAddr) ; try(exfalso ; congruence).
																					destruct v ; try(exfalso ; congruence).
																-------- (* pdinsertion <> (CPaddr (freeslotaddr + scoffset)) *)
																					rewrite <- beqAddrFalse in *.
																					repeat rewrite removeDupIdentity ; try congruence.
																					destruct (lookup (CPaddr (freeslotaddr + scoffset)) (memory s0) beqAddr) eqn:Hlookupsc ; try(exfalso ; congruence).
																					destruct v ; try(exfalso ; congruence).
																					intuition.
											* intro Hf. rewrite <- beqAddrFalse in *. congruence.
} (* end of freeSlotsListIsFreeSlot *)
{ (* DisjointFreeSlotsLists s *)
	unfold DisjointFreeSlotsLists.
	intros pd1 pd2 HPDTpd1 HPDTpd2 Hpd1pd2NotEq.

	assert(Hcons0 : DisjointFreeSlotsLists s0) by (unfold consistency in * ; intuition).
	unfold DisjointFreeSlotsLists in Hcons0.

	(* we must show all free slots list are disjoint
		check all possible values for pd1 AND pd2 in the modified state s
			-> only possible is pdinsertion
				1) - if pd1 = pdinsertion:
						-> show the pd1's new free slots list is a subset of the initial free slots list
								and that pd2's free slots list is identical at s and s0,
							-> if they were disjoint at s0, they are still disjoint at s -> OK
				2) - if pd1 <> pdinsertion, it is another pd, but pd2 could be pdinsertion
						3) - if pd2 = pdinsertion:
								same proof as with pd1
						4) - if pd2 <> pdinsertion: prove pd1's free slots list and pd2's free slot list
								have NOT changed in the modified state, so they are still disjoint
									-> compute the list at each modified state and check not changed from s0 -> OK
*)
	(* Check all values for pd1 and pd2 except pdinsertion *)
	destruct (beqAddr sceaddr pd1) eqn:beqscepd1; try(exfalso ; congruence).
	-	(* sceaddr = pd1 *)
		rewrite <- DependentTypeLemmas.beqAddrTrue in beqscepd1.
		rewrite <- beqscepd1 in *.
		unfold isSCE in *.
		unfold isPDT in *.
		destruct (lookup sceaddr (memory s) beqAddr) ; try(exfalso ; congruence).
		destruct v ; try(exfalso ; congruence).
	-	(* sceaddr <> pd1 *)
		destruct (beqAddr newBlockEntryAddr pd1) eqn:beqnewpd1 ; try(exfalso ; congruence).
		-- (* newBlockEntryAddr = pd1 *)
				rewrite <- DependentTypeLemmas.beqAddrTrue in beqnewpd1.
				rewrite <- beqnewpd1 in *.
				unfold isBE in *.
				unfold isPDT in *.
				destruct (lookup newBlockEntryAddr (memory s) beqAddr) ; try(exfalso ; congruence).
				destruct v ; try(exfalso ; congruence).
		-- (* newBlockEntryAddr <> pd1 *)
				destruct (beqAddr sceaddr pd2) eqn:beqscepd2; try(exfalso ; congruence).
				---	(* sceaddr = pd2 *)
						rewrite <- DependentTypeLemmas.beqAddrTrue in beqscepd2.
						rewrite <- beqscepd2 in *.
						unfold isSCE in *.
						unfold isPDT in *.
						destruct (lookup sceaddr (memory s) beqAddr) ; try(exfalso ; congruence).
						destruct v ; try(exfalso ; congruence).
				---	(* sceaddr <> pd2 *)
						destruct (beqAddr newBlockEntryAddr pd2) eqn:beqnewpd2 ; try(exfalso ; congruence).
					---- (* newBlockEntryAddr = pd2 *)
								rewrite <- DependentTypeLemmas.beqAddrTrue in beqnewpd2.
								rewrite <- beqnewpd2 in *.
								unfold isPDT in *.
								unfold isBE in *.
								destruct (lookup newBlockEntryAddr (memory s) beqAddr) ; try(exfalso ; congruence).
								destruct v ; try(exfalso ; congruence).
					---- (* newBlockEntryAddr <> pd2 *)
								destruct (beqAddr pdinsertion pd1) eqn:beqpdpd1; try(exfalso ; congruence).
								----- (* 1) pdinsertion = pd1 *)
										rewrite <- DependentTypeLemmas.beqAddrTrue in beqpdpd1.
										rewrite <- beqpdpd1 in *.
										destruct (beqAddr pdinsertion pd2) eqn:beqpdpd2; try(exfalso ; congruence).
										rewrite <- DependentTypeLemmas.beqAddrTrue in beqpdpd2. congruence.
										(* DUP *)
										assert(Hlookuppd2Eq : lookup pd2 (memory s) beqAddr = lookup pd2 (memory s0) beqAddr).
										{
											rewrite Hs. unfold isPDT.
											cbn. rewrite beqAddrTrue.
											rewrite beqscepd2.
											assert(HnewBsceNotEq : beqAddr newBlockEntryAddr sceaddr = false) by intuition.
											rewrite HnewBsceNotEq. (*newBlock <> sce *)
											assert(HpdnewBNotEq : beqAddr pdinsertion newBlockEntryAddr = false) by intuition.
											rewrite HpdnewBNotEq. (*pd <> newblock*)
											cbn.
											rewrite beqnewpd2.
											rewrite beqAddrTrue.
											rewrite <- beqAddrFalse in *.
											repeat rewrite removeDupIdentity ; intuition.
											destruct (beqAddr pdinsertion newBlockEntryAddr) eqn:Hf ; try(exfalso ; congruence).
											rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
											cbn.
											destruct (beqAddr pdinsertion pd2) eqn:Hff ; try(exfalso ; congruence).
											rewrite <- DependentTypeLemmas.beqAddrTrue in Hff. congruence.
											rewrite <- beqAddrFalse in *.
											repeat rewrite removeDupIdentity ; intuition.
										}
										assert(HPDTpd2Eq : isPDT pd2 s = isPDT pd2 s0).
										{ unfold isPDT. rewrite Hlookuppd2Eq. intuition. }
										assert(HPDTpd2s0 : isPDT pd2 s0) by (rewrite HPDTpd2Eq in * ; assumption).
										specialize(Hcons0 pdinsertion pd2 HPDTs0 HPDTpd2s0 Hpd1pd2NotEq).
										destruct Hcons0 as [listoption1 (listoption2 & (Hoptionlist1s0 & (Hwellformed1s0 & (Hoptionlist2s0 & (Hwellformed2s0 & HDisjoints0)))))].
										(* Show equality for pd2's free slot list
												so between listoption2 at s and listoption2 at s0 *)
										unfold getFreeSlotsList in Hoptionlist2s0.
										apply isPDTLookupEq in HPDTpd2s0. destruct HPDTpd2s0 as [pd2entry Hlookuppd2s0].
										rewrite Hlookuppd2s0 in *.
										destruct (beqAddr (firstfreeslot pd2entry) nullAddr) eqn:Hpd2Null ; try(exfalso ; congruence).
										------ (* listoption2 = NIL *)
													destruct H31 as [Hoptionlists (olds & (n0 & (n1 & (n2 & (nbleft & Hfreeslotsolds)))))].
													exists Hoptionlists.
													exists listoption2.
													assert(Hlistoption2s : getFreeSlotsList pd2 s = nil).
													{
														unfold getFreeSlotsList.
														rewrite Hlookuppd2Eq. rewrite Hpd2Null. reflexivity.
													}
													rewrite Hlistoption2s in *.
													intuition.
													unfold getFreeSlotsList. rewrite Hpdinsertions.
													rewrite HnewFirstFree.
													assert(Hnbleft : nbfreeslots pdentry1 = nbleft).
													{ (* DUP *)
														subst pdentry1. simpl. intuition.
														rewrite H30. (* nbleft = CIndex (currnbfreeslots - 1)*)
														destruct predCurrentNbFreeSlots.
														unfold StateLib.Index.pred in H1.
														destruct (gt_dec currnbfreeslots 0); try (exfalso ; congruence).
														unfold CIndex. inversion H1 as [Hpred].
														rewrite Hpred. destruct (le_dec i maxIdx) ; try(exfalso ; congruence).
														f_equal. apply proof_irrelevance.
													}
													rewrite Hnbleft.
													assert(HfreeSlotsListEq : Hoptionlists = getFreeSlotsListRec (maxIdx + 1) newFirstFreeSlotAddr s nbleft).
													{ intuition.
														rewrite <- H34. (* getFreeSlotsList s = Hoptionlists *)
														eapply getFreeSlotsListRecEqN ; intuition.
													}
													rewrite <- HfreeSlotsListEq.
													destruct (beqAddr newFirstFreeSlotAddr nullAddr) eqn:beqfirstnull; try(exfalso ; congruence).
													------- (* newFirstFreeSlotAddr = nullAddr *)
																	rewrite <- DependentTypeLemmas.beqAddrTrue in beqfirstnull.
																	rewrite beqfirstnull in *.
																	intuition.
																	assert(Hoption :  Hoptionlists = getFreeSlotsListRec n0 nullAddr s0 nbleft) by intuition.
																	rewrite FreeSlotsListRec_unroll in Hoption.
																	unfold getFreeSlotsListAux in Hoption.
																	destruct n0.
																	rewrite Hoption in *. cbn in *. congruence.
																	destruct (StateLib.Index.ltb nbleft zero).
																	rewrite Hoption in *. cbn in *. congruence.
																	assert(HNullAddrExistss0 : nullAddrExists s0)
																			by (unfold consistency in * ; intuition).
																	unfold nullAddrExists in *.
																	unfold isPADDR in *.
																	destruct (lookup nullAddr (memory s0) beqAddr) ; try(exfalso ; congruence).
																	destruct v ; try(exfalso ; congruence).
																	destruct (beqAddr p nullAddr).
																	rewrite Hoption in *. cbn in *. congruence.
																	rewrite Hoption in *. cbn in *. congruence.
													------- (* newFirstFreeSlotAddr <> nullAddr *)
																	intuition.
													------- (* Disjoint : listoption2 = NIL *)
																	subst listoption2. cbn.
																	unfold Lib.disjoint. intuition.
										------ (* listoption2 <> NIL *)
														(* show equality between listoption2 at s and s0 
																+ if listoption2 has NOT changed, listoption1 at s is
																just a subset of listoption1 at s0 so they are
																still disjoint *)
														assert(Hfreeslotspd2Eq : exists s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 n1 nbleft,
nbleft = (nbfreeslots pd2entry) /\
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
                     vidtBlock := vidtBlock pdentry
                   |}) (memory s0) beqAddr |} /\
getFreeSlotsListRec n1 (firstfreeslot pd2entry) s1 nbleft =
getFreeSlotsListRec (maxIdx+1) (firstfreeslot pd2entry) s0 nbleft
			 /\
	n1 <= maxIdx+1 /\ nbleft < n1
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
		                vidtBlock := vidtBlock pdentry0
		              |}
                 ) (memory s1) beqAddr |} /\
getFreeSlotsListRec n1 (firstfreeslot pd2entry) s2 nbleft =
			getFreeSlotsListRec n1 (firstfreeslot pd2entry) s1 nbleft
/\ s3 = {|
     currentPartition := currentPartition s2;
     memory := add newBlockEntryAddr
	            (BE
	               (CBlockEntry (read bentry) 
	                  (write bentry) (exec bentry) 
	                  (present bentry) (accessible bentry)
	                  (blockindex bentry)
	                  (CBlock startaddr (endAddr (blockrange bentry))))
                 ) (memory s2) beqAddr |} /\
getFreeSlotsListRec n1 (firstfreeslot pd2entry) s3 nbleft =
			getFreeSlotsListRec n1 (firstfreeslot pd2entry) s2 nbleft
/\ s4 = {|
     currentPartition := currentPartition s3;
     memory := add newBlockEntryAddr
               (BE
                  (CBlockEntry (read bentry0) 
                     (write bentry0) (exec bentry0) 
                     (present bentry0) (accessible bentry0)
                     (blockindex bentry0)
                     (CBlock (startAddr (blockrange bentry0)) endaddr))
                 ) (memory s3) beqAddr |} /\
getFreeSlotsListRec n1 (firstfreeslot pd2entry) s4 nbleft =
			getFreeSlotsListRec n1 (firstfreeslot pd2entry) s3 nbleft
/\ s5 = {|
     currentPartition := currentPartition s4;
     memory := add newBlockEntryAddr
              (BE
                 (CBlockEntry (read bentry1) 
                    (write bentry1) (exec bentry1) 
                    (present bentry1) true (blockindex bentry1)
                    (blockrange bentry1))
                 ) (memory s4) beqAddr |} /\
getFreeSlotsListRec n1 (firstfreeslot pd2entry) s5 nbleft =
			getFreeSlotsListRec n1 (firstfreeslot pd2entry) s4 nbleft
/\ s6 = {|
     currentPartition := currentPartition s5;
     memory := add newBlockEntryAddr
               (BE
                  (CBlockEntry (read bentry2) (write bentry2) 
                     (exec bentry2) true (accessible bentry2)
                     (blockindex bentry2) (blockrange bentry2))
                 ) (memory s5) beqAddr |} /\
getFreeSlotsListRec n1 (firstfreeslot pd2entry) s6 nbleft =
			getFreeSlotsListRec n1 (firstfreeslot pd2entry) s5 nbleft
/\ s7 = {|
     currentPartition := currentPartition s6;
     memory := add newBlockEntryAddr
              (BE
                 (CBlockEntry r (write bentry3) (exec bentry3)
                    (present bentry3) (accessible bentry3) 
                    (blockindex bentry3) (blockrange bentry3))
                 ) (memory s6) beqAddr |} /\
getFreeSlotsListRec n1 (firstfreeslot pd2entry) s7 nbleft =
			getFreeSlotsListRec n1 (firstfreeslot pd2entry) s6 nbleft
/\ s8 = {|
     currentPartition := currentPartition s7;
     memory := add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry4) w (exec bentry4) 
                       (present bentry4) (accessible bentry4) 
                       (blockindex bentry4) (blockrange bentry4))
                 ) (memory s7) beqAddr |} /\
getFreeSlotsListRec n1(firstfreeslot pd2entry) s8 nbleft =
			getFreeSlotsListRec n1 (firstfreeslot pd2entry) s7 nbleft
/\ s9 = {|
     currentPartition := currentPartition s8;
     memory := add newBlockEntryAddr
              (BE
                 (CBlockEntry (read bentry5) (write bentry5) e 
                    (present bentry5) (accessible bentry5) 
                    (blockindex bentry5) (blockrange bentry5))
                 ) (memory s8) beqAddr |} /\
getFreeSlotsListRec n1 (firstfreeslot pd2entry) s9 nbleft =
			getFreeSlotsListRec n1 (firstfreeslot pd2entry) s8 nbleft
/\ s10 = {|
     currentPartition := currentPartition s9;
     memory := add sceaddr 
								(SCE {| origin := origin; next := next scentry |}
                 ) (memory s9) beqAddr |} /\
getFreeSlotsListRec n1 (firstfreeslot pd2entry) s10 nbleft =
			getFreeSlotsListRec n1 (firstfreeslot pd2entry) s9 nbleft
).
{
	eexists ?[s1]. eexists ?[s2]. eexists ?[s3]. eexists ?[s4]. eexists ?[s5].
	eexists ?[s6]. eexists ?[s7]. eexists ?[s8]. eexists ?[s9].
	eexists ?[s10]. eexists ?[n1]. eexists.
	split. intuition.
	split. intuition.
	set (s1 := {| currentPartition := _ |}).
	(* prove outside *)
	assert(Hfreeslotss1 : getFreeSlotsListRec ?n1 (firstfreeslot pd2entry) s1 (nbfreeslots pd2entry) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s0 (nbfreeslots pd2entry)).
	{
		apply getFreeSlotsListRecEqPDT.
		-- 	intro Hfirstpdeq.
				assert(HFirstFreeSlotPointerIsBEAndFreeSlots0 : FirstFreeSlotPointerIsBEAndFreeSlot s0)
					by (unfold consistency in * ; intuition).
				unfold FirstFreeSlotPointerIsBEAndFreeSlot in *.
				specialize (HFirstFreeSlotPointerIsBEAndFreeSlots0 pd2 pd2entry Hlookuppd2s0).
				destruct HFirstFreeSlotPointerIsBEAndFreeSlots0.
				--- intro HfirstfreeNull.
						assert(HnullAddrExistss0 : nullAddrExists s0)
							by (unfold consistency in * ; intuition).
						unfold nullAddrExists in *.
						unfold isPADDR in *.
						rewrite HfirstfreeNull in *. rewrite <- Hfirstpdeq in *.
						destruct (lookup nullAddr (memory s0) beqAddr) ; try(exfalso ; congruence).
						destruct v ; try(exfalso ; congruence).
				--- rewrite Hfirstpdeq in *.
						unfold isBE in *.
						destruct (lookup pdinsertion (memory s0) beqAddr) ; try (exfalso ; congruence).
						destruct v ; try(exfalso ; congruence).
		-- unfold isBE. rewrite Hpdinsertions0. intuition.
		-- unfold isPADDR. rewrite Hpdinsertions0. intuition.
	}
	set (s2 := {| currentPartition := _ |}).
	assert(Hfreeslotss2 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s2 (nbfreeslots pd2entry) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s1 (nbfreeslots pd2entry)).
	{
				apply getFreeSlotsListRecEqPDT.
				--- 	intro Hfirstpdeq.
						assert(HFirstFreeSlotPointerIsBEAndFreeSlots0 : FirstFreeSlotPointerIsBEAndFreeSlot s0)
							by (unfold consistency in * ; intuition).
						unfold FirstFreeSlotPointerIsBEAndFreeSlot in *.
						specialize (HFirstFreeSlotPointerIsBEAndFreeSlots0 pd2 pd2entry Hlookuppd2s0).
						destruct HFirstFreeSlotPointerIsBEAndFreeSlots0.
						---- intro HfirstfreeNull.
								assert(HnullAddrExistss0 : nullAddrExists s0)
									by (unfold consistency in * ; intuition).
								unfold nullAddrExists in *.
								unfold isPADDR in *.
								rewrite HfirstfreeNull in *. rewrite <- Hfirstpdeq in *.
								destruct (lookup nullAddr (memory s0) beqAddr) ; try(exfalso ; congruence).
								destruct v ; try(exfalso ; congruence).
						---- rewrite Hfirstpdeq in *.
								unfold isBE in *.
								destruct (lookup pdinsertion (memory s0) beqAddr) ; try (exfalso ; congruence).
								destruct v ; try(exfalso ; congruence).
				--- unfold isBE. unfold s1. cbn. rewrite beqAddrTrue. intuition.
				--- unfold isPADDR. unfold s1. cbn. rewrite beqAddrTrue. intuition.
	}
	set (s3 := {| currentPartition := _ |}).
	assert(Hfreeslotss3 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s3 (nbfreeslots pd2entry) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s2 (nbfreeslots pd2entry)).
	{
				apply getFreeSlotsListRecEqBE ; intuition.
				---	(* Lists are disjoint at s0, so newB <> firstfreeslot pd2entry *)
							unfold getFreeSlotsList in Hoptionlist1s0.
							unfold getFreeSlotsList in Hoptionlist2s0.
							rewrite Hpdinsertions0 in *.
							assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
							{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
							assert(HnewBFirstFrees0P : firstfreeslot pd2entry = newBlockEntryAddr) by intuition.
							rewrite HnewBFirstFrees0PDT in *.
							rewrite HnewBFirstFrees0P in *.
							destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
								rewrite FreeSlotsListRec_unroll in Hoptionlist1s0.
								rewrite FreeSlotsListRec_unroll in Hoptionlist2s0.
								unfold getFreeSlotsListAux in *.
								induction (maxIdx+1). (* false induction because of fixpoint constraints *)
								** (* N=0 -> NotWellFormed *)
									rewrite Hoptionlist1s0 in *.
									cbn in Hwellformed1s0.
									congruence.
								** (* N>0 *)
									clear IHn.
									cbn in *.
									rewrite HlookupnewBs0 in *.
									destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred1 ; try(exfalso ; congruence).
									*** destruct (StateLib.Index.pred (nbfreeslots pd2entry)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
											rewrite Hoptionlist1s0 in *.
											cbn in *.
											unfold Lib.disjoint in HDisjoints0.
											specialize(HDisjoints0 newBlockEntryAddr).
											simpl in HDisjoints0.
											intuition.
									*** rewrite Hoptionlist1s0 in *.
											cbn in Hwellformed1s0.
											exfalso ; congruence.
			--- unfold isBE. unfold s3. cbn.
					destruct (beqAddr pdinsertion newBlockEntryAddr) ; try(exfalso ; congruence).
					rewrite beqAddrTrue.
					cbn.
					repeat rewrite removeDupIdentity ; intuition.
			--- subst listoption2.
					rewrite <- Hfreeslotss1 in *. rewrite <- Hfreeslotss2 in *. intuition.
			--- assert(H_NoDups0 : NoDupInFreeSlotsList s0)
							by (unfold consistency in * ; intuition).
					unfold NoDupInFreeSlotsList in *.
					specialize (H_NoDups0 pd2 pd2entry Hlookuppd2s0).
					destruct H_NoDups0 as [optionlist2 (Hoptionlist2 & HwellFormed2' & HNoDup2)].
					unfold getFreeSlotsList in Hoptionlist2.
					rewrite Hlookuppd2s0 in *. rewrite Hpd2Null in *.
					subst optionlist2. subst listoption2.
					rewrite Hfreeslotss1 in *. rewrite Hfreeslotss2 in *. intuition.
			--- rewrite Hfreeslotss2 in *. rewrite Hfreeslotss1 in *.
					(* newB is in freeslots list of pdinsertion, so can't be in other list
							because of Disjoint *)
					(* DUP from previous step *)
					unfold getFreeSlotsList in Hoptionlist1s0.
					unfold getFreeSlotsList in Hoptionlist2s0.
					rewrite Hpdinsertions0 in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					rewrite HnewBFirstFrees0PDT in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
					rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
					destruct (beqAddr (firstfreeslot pd2entry) nullAddr) eqn:HfirstfreeNull ; try(exfalso ; congruence).
					(* firstfreeslot p <> NULL *)
					(* if first free of other PD is NOT NULL,
					then newB can't be in the two lists at s0 because of Disjoint -> False *)
					subst listoption2. subst listoption1.
					unfold Lib.disjoint in HDisjoints0.
					specialize(HDisjoints0 newBlockEntryAddr).
					destruct (HDisjoints0).
					* induction (maxIdx+1). (* false induction because of fixpoint constraints *)
						** (* N=0 -> NotWellFormed *)
								cbn in *.
								congruence.
						** (* N>0 *)
								clear IHn.
								simpl. rewrite HlookupnewBs0.
								assert(HcurrNb : currnbfreeslots = nbfreeslots pdentry).
								{ unfold pdentryNbFreeSlots in *. rewrite Hpdinsertions0 in *. intuition. }
								rewrite <- HcurrNb in *.
								destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred ; try(exfalso ; congruence).
								rewrite <- HcurrNb in *. rewrite Hpred. cbn. intuition.
					* intuition.
}
	set (s4 := {| currentPartition := currentPartition ?s3; memory := _ |}). simpl in s4. simpl in s3.
	assert(Hfreeslotss4 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s4 (nbfreeslots pd2entry) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s3 (nbfreeslots pd2entry)).
	{
		(* DUP *)
		apply getFreeSlotsListRecEqBE ; intuition.
		---	(* Lists are disjoint at s0, so newB <> firstfreeslot p *)
					unfold getFreeSlotsList in Hoptionlist1s0.
					unfold getFreeSlotsList in Hoptionlist2s0.
					rewrite Hpdinsertions0 in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					assert(HnewBFirstFrees0P : firstfreeslot pd2entry = newBlockEntryAddr) by intuition.
					rewrite HnewBFirstFrees0PDT in *.
					rewrite HnewBFirstFrees0P in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
						rewrite FreeSlotsListRec_unroll in Hoptionlist1s0.
						rewrite FreeSlotsListRec_unroll in Hoptionlist2s0.
						unfold getFreeSlotsListAux in *.
						induction (maxIdx+1). (* false induction because of fixpoint constraints *)
						** (* N=0 -> NotWellFormed *)
							rewrite Hoptionlist1s0 in *.
							cbn in Hwellformed1s0.
							congruence.
						** (* N>0 *)
							clear IHn.
							cbn in *.
							rewrite HlookupnewBs0 in *.
							destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred1 ; try(exfalso ; congruence).
							*** destruct (StateLib.Index.pred (nbfreeslots pd2entry)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
									rewrite Hoptionlist1s0 in *.
									cbn in *.
									unfold Lib.disjoint in HDisjoints0.
									specialize(HDisjoints0 newBlockEntryAddr).
									simpl in HDisjoints0.
									intuition.
							*** rewrite Hoptionlist1s0 in *.
									cbn in Hwellformed1s0.
									exfalso ; congruence.
			--- unfold isBE. unfold s4. cbn.
					destruct (beqAddr pdinsertion newBlockEntryAddr) ; try(exfalso ; congruence).
					rewrite beqAddrTrue.
					cbn.
					repeat rewrite removeDupIdentity ; intuition.
			--- subst listoption2.
					rewrite <- Hfreeslotss1 in *. rewrite <- Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. intuition.
			--- assert(H_NoDups0 : NoDupInFreeSlotsList s0)
							by (unfold consistency in * ; intuition).
					unfold NoDupInFreeSlotsList in *.
					specialize (H_NoDups0 pd2 pd2entry Hlookuppd2s0).
					destruct H_NoDups0 as [optionlist2 (Hoptionlist2 & HwellFormed2' & HNoDup2)].
					unfold getFreeSlotsList in Hoptionlist2.
					rewrite Hlookuppd2s0 in *. rewrite Hpd2Null in *.
					subst optionlist2. subst listoption2.
					rewrite Hfreeslotss1 in *. rewrite Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. intuition.
			--- rewrite <- Hfreeslotss3 in *.
					rewrite Hfreeslotss2 in *. rewrite Hfreeslotss1 in *.
					(* newB is in freeslots list of pdinsertion, so can't be in other list
							because of Disjoint *)
					(* DUP from previous step *)
					unfold getFreeSlotsList in Hoptionlist1s0.
					unfold getFreeSlotsList in Hoptionlist2s0.
					rewrite Hpdinsertions0 in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					rewrite HnewBFirstFrees0PDT in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
					rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
					destruct (beqAddr (firstfreeslot pd2entry) nullAddr) eqn:HfirstfreeNull ; try(exfalso ; congruence).
					(* firstfreeslot p <> NULL *)
					(* if first free of other PD is NOT NULL,
					then newB can't be in the two lists at s0 because of Disjoint -> False *)
					subst listoption2. subst listoption1.
					unfold Lib.disjoint in HDisjoints0.
					specialize(HDisjoints0 newBlockEntryAddr).
					destruct (HDisjoints0).
					* induction (maxIdx+1). (* false induction because of fixpoint constraints *)
						** (* N=0 -> NotWellFormed *)
								cbn in *.
								congruence.
						** (* N>0 *)
								clear IHn.
								simpl. rewrite HlookupnewBs0.
								assert(HcurrNb : currnbfreeslots = nbfreeslots pdentry).
								{ unfold pdentryNbFreeSlots in *. rewrite Hpdinsertions0 in *. intuition. }
								rewrite <- HcurrNb in *.
								destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred ; try(exfalso ; congruence).
								rewrite <- HcurrNb in *. rewrite Hpred. cbn. intuition.
					* intuition.
} fold s1. fold s2. fold s3. fold s4.
	set (s5 := {| currentPartition := currentPartition ?s4; memory := _ |}).
	simpl in s4.
	assert(Hfreeslotss5 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s5 (nbfreeslots pd2entry) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s4 (nbfreeslots pd2entry)).
	{
		(* DUP *)
		apply getFreeSlotsListRecEqBE ; intuition.
		---	(* Lists are disjoint at s0, so newB <> firstfreeslot p *)

					unfold getFreeSlotsList in Hoptionlist1s0.
					unfold getFreeSlotsList in Hoptionlist2s0.
					rewrite Hpdinsertions0 in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					assert(HnewBFirstFrees0P : firstfreeslot pd2entry = newBlockEntryAddr) by intuition.
					rewrite HnewBFirstFrees0PDT in *.
					rewrite HnewBFirstFrees0P in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
						rewrite FreeSlotsListRec_unroll in Hoptionlist1s0.
						rewrite FreeSlotsListRec_unroll in Hoptionlist2s0.
						unfold getFreeSlotsListAux in *.
						induction (maxIdx+1). (* false induction because of fixpoint constraints *)
						** (* N=0 -> NotWellFormed *)
							rewrite Hoptionlist1s0 in *.
							cbn in Hwellformed1s0.
							congruence.
						** (* N>0 *)
							clear IHn.
							cbn in *.
							rewrite HlookupnewBs0 in *.
							destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred1 ; try(exfalso ; congruence).
							*** destruct (StateLib.Index.pred (nbfreeslots pd2entry)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
									rewrite Hoptionlist1s0 in *.
									cbn in *.
									unfold Lib.disjoint in HDisjoints0.
									specialize(HDisjoints0 newBlockEntryAddr).
									simpl in HDisjoints0.
									intuition.
							*** rewrite Hoptionlist1s0 in *.
									cbn in Hwellformed1s0.
									exfalso ; congruence.
			--- unfold isBE. unfold s5. cbn.
					destruct (beqAddr pdinsertion newBlockEntryAddr) ; try(exfalso ; congruence).
					rewrite beqAddrTrue.
					cbn.
					repeat rewrite removeDupIdentity ; intuition.
			--- subst listoption2.
					rewrite <- Hfreeslotss1 in *. rewrite <- Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *. intuition.
			--- assert(H_NoDups0 : NoDupInFreeSlotsList s0)
							by (unfold consistency in * ; intuition).
					unfold NoDupInFreeSlotsList in *.
					specialize (H_NoDups0 pd2 pd2entry Hlookuppd2s0).
					destruct H_NoDups0 as [optionlist2 (Hoptionlist2 & HwellFormed2' & HNoDup2)].
					unfold getFreeSlotsList in Hoptionlist2.
					rewrite Hlookuppd2s0 in *. rewrite Hpd2Null in *.
					subst optionlist2. subst listoption2.
					rewrite Hfreeslotss1 in *. rewrite Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *. intuition.
			--- rewrite <- Hfreeslotss4 in *. rewrite <- Hfreeslotss3 in *.
					rewrite Hfreeslotss2 in *. rewrite Hfreeslotss1 in *.
					(* newB is in freeslots list of pdinsertion, so can't be in other list
							because of Disjoint *)
					(* DUP from previous step *)
					unfold getFreeSlotsList in Hoptionlist1s0.
					unfold getFreeSlotsList in Hoptionlist2s0.
					rewrite Hpdinsertions0 in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					rewrite HnewBFirstFrees0PDT in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
					rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
					destruct (beqAddr (firstfreeslot pd2entry) nullAddr) eqn:HfirstfreeNull ; try(exfalso ; congruence).
					(* firstfreeslot p <> NULL *)
					(* if first free of other PD is NOT NULL,
					then newB can't be in the two lists at s0 because of Disjoint -> False *)
					subst listoption2. subst listoption1.
					unfold Lib.disjoint in HDisjoints0.
					specialize(HDisjoints0 newBlockEntryAddr).
					destruct (HDisjoints0).
					* induction (maxIdx+1). (* false induction because of fixpoint constraints *)
						** (* N=0 -> NotWellFormed *)
								cbn in *.
								congruence.
						** (* N>0 *)
								clear IHn.
								simpl. rewrite HlookupnewBs0.
								assert(HcurrNb : currnbfreeslots = nbfreeslots pdentry).
								{ unfold pdentryNbFreeSlots in *. rewrite Hpdinsertions0 in *. intuition. }
								rewrite <- HcurrNb in *.
								destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred ; try(exfalso ; congruence).
								rewrite <- HcurrNb in *. rewrite Hpred. cbn. intuition.
					* intuition.
}
	fold s1. fold s2. fold s3. fold s4. fold s5.
	set (s6 := {| currentPartition := currentPartition ?s5; memory := _ |}).
	simpl in s4.
	assert(Hfreeslotss6 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s6 (nbfreeslots pd2entry) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s5 (nbfreeslots pd2entry)).
	{
		(* DUP *)
		apply getFreeSlotsListRecEqBE ; intuition.
		---	(* Lists are disjoint at s0, so newB <> firstfreeslot p *)
					unfold getFreeSlotsList in Hoptionlist1s0.
					unfold getFreeSlotsList in Hoptionlist2s0.
					rewrite Hpdinsertions0 in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					assert(HnewBFirstFrees0P : firstfreeslot pd2entry = newBlockEntryAddr) by intuition.
					rewrite HnewBFirstFrees0PDT in *.
					rewrite HnewBFirstFrees0P in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
						rewrite FreeSlotsListRec_unroll in Hoptionlist1s0.
						rewrite FreeSlotsListRec_unroll in Hoptionlist2s0.
						unfold getFreeSlotsListAux in *.
						induction (maxIdx+1). (* false induction because of fixpoint constraints *)
						** (* N=0 -> NotWellFormed *)
							rewrite Hoptionlist1s0 in *.
							cbn in Hwellformed1s0.
							congruence.
						** (* N>0 *)
							clear IHn.
							cbn in *.
							rewrite HlookupnewBs0 in *.
							destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred1 ; try(exfalso ; congruence).
							*** destruct (StateLib.Index.pred (nbfreeslots pd2entry)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
									rewrite Hoptionlist1s0 in *.
									cbn in *.
									unfold Lib.disjoint in HDisjoints0.
									specialize(HDisjoints0 newBlockEntryAddr).
									simpl in HDisjoints0.
									intuition.
							*** rewrite Hoptionlist1s0 in *.
									cbn in Hwellformed1s0.
									exfalso ; congruence.
			--- unfold isBE. unfold s6. cbn.
					destruct (beqAddr pdinsertion newBlockEntryAddr) ; try(exfalso ; congruence).
					rewrite beqAddrTrue.
					cbn.
					repeat rewrite removeDupIdentity ; intuition.
			--- subst listoption2.
					rewrite <- Hfreeslotss1 in *. rewrite <- Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *.
					rewrite <- Hfreeslotss5 in *. intuition.
			--- assert(H_NoDups0 : NoDupInFreeSlotsList s0)
							by (unfold consistency in * ; intuition).
					unfold NoDupInFreeSlotsList in *.
					specialize (H_NoDups0 pd2 pd2entry Hlookuppd2s0).
					destruct H_NoDups0 as [optionlist2 (Hoptionlist2 & HwellFormed2' & HNoDup2)].
					unfold getFreeSlotsList in Hoptionlist2.
					rewrite Hlookuppd2s0 in *. rewrite Hpd2Null in *.
					subst optionlist2. subst listoption2.
					rewrite Hfreeslotss1 in *. rewrite Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *.
					rewrite <- Hfreeslotss5 in *. intuition.
			--- rewrite <- Hfreeslotss5 in *.
					rewrite <- Hfreeslotss4 in *. rewrite <- Hfreeslotss3 in *.
					rewrite Hfreeslotss2 in *. rewrite Hfreeslotss1 in *.
					(* newB is in freeslots list of pdinsertion, so can't be in other list
							because of Disjoint *)
					(* DUP from previous step *)
					unfold getFreeSlotsList in Hoptionlist1s0.
					unfold getFreeSlotsList in Hoptionlist2s0.
					rewrite Hpdinsertions0 in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					rewrite HnewBFirstFrees0PDT in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
					rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
					destruct (beqAddr (firstfreeslot pd2entry) nullAddr) eqn:HfirstfreeNull ; try(exfalso ; congruence).
					(* firstfreeslot p <> NULL *)
					(* if first free of other PD is NOT NULL,
					then newB can't be in the two lists at s0 because of Disjoint -> False *)
					subst listoption2. subst listoption1.
					unfold Lib.disjoint in HDisjoints0.
					specialize(HDisjoints0 newBlockEntryAddr).
					destruct (HDisjoints0).
					* induction (maxIdx+1). (* false induction because of fixpoint constraints *)
						** (* N=0 -> NotWellFormed *)
								cbn in *.
								congruence.
						** (* N>0 *)
								clear IHn.
								simpl. rewrite HlookupnewBs0.
								assert(HcurrNb : currnbfreeslots = nbfreeslots pdentry).
								{ unfold pdentryNbFreeSlots in *. rewrite Hpdinsertions0 in *. intuition. }
								rewrite <- HcurrNb in *.
								destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred ; try(exfalso ; congruence).
								rewrite <- HcurrNb in *. rewrite Hpred. cbn. intuition.
					* intuition.
}
	fold s1. fold s2. fold s3. fold s4. fold s5. fold s6.
	set (s7 := {| currentPartition := currentPartition ?s6; memory := _ |}).
	simpl in s5. simpl in s6.
	assert(Hfreeslotss7 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s7 (nbfreeslots pd2entry) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s6 (nbfreeslots pd2entry)).
	{
		(* DUP *)
		apply getFreeSlotsListRecEqBE ; intuition.
		---	(* Lists are disjoint at s0, so newB <> firstfreeslot p *)
					unfold getFreeSlotsList in Hoptionlist1s0.
					unfold getFreeSlotsList in Hoptionlist2s0.
					rewrite Hpdinsertions0 in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					assert(HnewBFirstFrees0P : firstfreeslot pd2entry = newBlockEntryAddr) by intuition.
					rewrite HnewBFirstFrees0PDT in *.
					rewrite HnewBFirstFrees0P in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
						rewrite FreeSlotsListRec_unroll in Hoptionlist1s0.
						rewrite FreeSlotsListRec_unroll in Hoptionlist2s0.
						unfold getFreeSlotsListAux in *.
						induction (maxIdx+1). (* false induction because of fixpoint constraints *)
						** (* N=0 -> NotWellFormed *)
							rewrite Hoptionlist1s0 in *.
							cbn in Hwellformed1s0.
							congruence.
						** (* N>0 *)
							clear IHn.
							cbn in *.
							rewrite HlookupnewBs0 in *.
							destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred1 ; try(exfalso ; congruence).
							*** destruct (StateLib.Index.pred (nbfreeslots pd2entry)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
									rewrite Hoptionlist1s0 in *.
									cbn in *.
									unfold Lib.disjoint in HDisjoints0.
									specialize(HDisjoints0 newBlockEntryAddr).
									simpl in HDisjoints0.
									intuition.
							*** rewrite Hoptionlist1s0 in *.
									cbn in Hwellformed1s0.
									exfalso ; congruence.
			--- unfold isBE. unfold s7. cbn.
					destruct (beqAddr pdinsertion newBlockEntryAddr) ; try(exfalso ; congruence).
					rewrite beqAddrTrue.
					cbn.
					repeat rewrite removeDupIdentity ; intuition.
			--- subst listoption2.
					rewrite <- Hfreeslotss1 in *. rewrite <- Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *.
					rewrite <- Hfreeslotss5 in *. rewrite <- Hfreeslotss6 in *. intuition.
			--- assert(H_NoDups0 : NoDupInFreeSlotsList s0)
							by (unfold consistency in * ; intuition).
					unfold NoDupInFreeSlotsList in *.
					specialize (H_NoDups0 pd2 pd2entry Hlookuppd2s0).
					destruct H_NoDups0 as [optionlist2 (Hoptionlist2 & HwellFormed2' & HNoDup2)].
					unfold getFreeSlotsList in Hoptionlist2.
					rewrite Hlookuppd2s0 in *. rewrite Hpd2Null in *.
					subst optionlist2. subst listoption2.
					rewrite Hfreeslotss1 in *. rewrite Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *.
					rewrite <- Hfreeslotss5 in *. rewrite <- Hfreeslotss6 in *. intuition.
			--- rewrite <- Hfreeslotss6 in *. rewrite <- Hfreeslotss5 in *.
					rewrite <- Hfreeslotss4 in *. rewrite <- Hfreeslotss3 in *.
					rewrite Hfreeslotss2 in *. rewrite Hfreeslotss1 in *.
					(* newB is in freeslots list of pdinsertion, so can't be in other list
							because of Disjoint *)
					(* DUP from previous step *)
					unfold getFreeSlotsList in Hoptionlist1s0.
					unfold getFreeSlotsList in Hoptionlist2s0.
					rewrite Hpdinsertions0 in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					rewrite HnewBFirstFrees0PDT in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
					rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
					destruct (beqAddr (firstfreeslot pd2entry) nullAddr) eqn:HfirstfreeNull ; try(exfalso ; congruence).
					(* firstfreeslot p <> NULL *)
					(* if first free of other PD is NOT NULL,
					then newB can't be in the two lists at s0 because of Disjoint -> False *)
					subst listoption2. subst listoption1.
					unfold Lib.disjoint in HDisjoints0.
					specialize(HDisjoints0 newBlockEntryAddr).
					destruct (HDisjoints0).
					* induction (maxIdx+1). (* false induction because of fixpoint constraints *)
						** (* N=0 -> NotWellFormed *)
								cbn in *.
								congruence.
						** (* N>0 *)
								clear IHn.
								simpl. rewrite HlookupnewBs0.
								assert(HcurrNb : currnbfreeslots = nbfreeslots pdentry).
								{ unfold pdentryNbFreeSlots in *. rewrite Hpdinsertions0 in *. intuition. }
								rewrite <- HcurrNb in *.
								destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred ; try(exfalso ; congruence).
								rewrite <- HcurrNb in *. rewrite Hpred. cbn. intuition.
					* intuition.
}
	fold s1. fold s2. fold s3. fold s4. fold s5. fold s6. fold s7.
	set (s8 := {| currentPartition := currentPartition ?s7; memory := _ |}).
	simpl in s7.
	assert(Hfreeslotss8 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s8 (nbfreeslots pd2entry) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s7 (nbfreeslots pd2entry)).
	{
		(* DUP *)
				apply getFreeSlotsListRecEqBE ; intuition.
				---	(* Lists are disjoint at s0, so newB <> firstfreeslot p *)
							unfold getFreeSlotsList in Hoptionlist1s0.
							unfold getFreeSlotsList in Hoptionlist2s0.
							rewrite Hpdinsertions0 in *.
							assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
							{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
							assert(HnewBFirstFrees0P : firstfreeslot pd2entry = newBlockEntryAddr) by intuition.
							rewrite HnewBFirstFrees0PDT in *.
							rewrite HnewBFirstFrees0P in *.
							destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
								rewrite FreeSlotsListRec_unroll in Hoptionlist1s0.
								rewrite FreeSlotsListRec_unroll in Hoptionlist2s0.
								unfold getFreeSlotsListAux in *.
								induction (maxIdx+1). (* false induction because of fixpoint constraints *)
								** (* N=0 -> NotWellFormed *)
									rewrite Hoptionlist1s0 in *.
									cbn in Hwellformed1s0.
									congruence.
								** (* N>0 *)
									clear IHn.
									cbn in *.
									rewrite HlookupnewBs0 in *.
									destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred1 ; try(exfalso ; congruence).
									*** destruct (StateLib.Index.pred (nbfreeslots pd2entry)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
											rewrite Hoptionlist1s0 in *.
											cbn in *.
											unfold Lib.disjoint in HDisjoints0.
											specialize(HDisjoints0 newBlockEntryAddr).
											simpl in HDisjoints0.
											intuition.
									*** rewrite Hoptionlist1s0 in *.
											cbn in Hwellformed1s0.
											exfalso ; congruence.
			--- unfold isBE. unfold s8. cbn.
					destruct (beqAddr pdinsertion newBlockEntryAddr) ; try(exfalso ; congruence).
					rewrite beqAddrTrue.
					cbn.
					repeat rewrite removeDupIdentity ; intuition.
			--- subst listoption2.
					rewrite <- Hfreeslotss1 in *. rewrite <- Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *.
					rewrite <- Hfreeslotss5 in *. rewrite <- Hfreeslotss6 in *.
					rewrite <- Hfreeslotss7 in *. intuition.
			--- assert(H_NoDups0 : NoDupInFreeSlotsList s0)
							by (unfold consistency in * ; intuition).
					unfold NoDupInFreeSlotsList in *.
					specialize (H_NoDups0 pd2 pd2entry Hlookuppd2s0).
					destruct H_NoDups0 as [optionlist2 (Hoptionlist2 & HwellFormed2' & HNoDup2)].
					unfold getFreeSlotsList in Hoptionlist2.
					rewrite Hlookuppd2s0 in *. rewrite Hpd2Null in *.
					subst optionlist2. subst listoption2.
					rewrite Hfreeslotss1 in *. rewrite Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *.
					rewrite <- Hfreeslotss5 in *. rewrite <- Hfreeslotss6 in *.
					rewrite <- Hfreeslotss7 in *. intuition.
			--- rewrite <- Hfreeslotss7 in *.
					rewrite <- Hfreeslotss6 in *. rewrite <- Hfreeslotss5 in *.
					rewrite <- Hfreeslotss4 in *. rewrite <- Hfreeslotss3 in *.
					rewrite Hfreeslotss2 in *. rewrite Hfreeslotss1 in *.
					(* newB is in freeslots list of pdinsertion, so can't be in other list
							because of Disjoint *)
					(* DUP from previous step *)
					unfold getFreeSlotsList in Hoptionlist1s0.
					unfold getFreeSlotsList in Hoptionlist2s0.
					rewrite Hpdinsertions0 in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					rewrite HnewBFirstFrees0PDT in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
					rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
					destruct (beqAddr (firstfreeslot pd2entry) nullAddr) eqn:HfirstfreeNull ; try(exfalso ; congruence).
					(* firstfreeslot p <> NULL *)
					(* if first free of other PD is NOT NULL,
					then newB can't be in the two lists at s0 because of Disjoint -> False *)
					subst listoption2. subst listoption1.
					unfold Lib.disjoint in HDisjoints0.
					specialize(HDisjoints0 newBlockEntryAddr).
					destruct (HDisjoints0).
					* induction (maxIdx+1). (* false induction because of fixpoint constraints *)
						** (* N=0 -> NotWellFormed *)
								cbn in *.
								congruence.
						** (* N>0 *)
								clear IHn.
								simpl. rewrite HlookupnewBs0.
								assert(HcurrNb : currnbfreeslots = nbfreeslots pdentry).
								{ unfold pdentryNbFreeSlots in *. rewrite Hpdinsertions0 in *. intuition. }
								rewrite <- HcurrNb in *.
								destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred ; try(exfalso ; congruence).
								rewrite <- HcurrNb in *. rewrite Hpred. cbn. intuition.
					* intuition.
}
	fold s1. fold s2. fold s3. fold s4. fold s5. fold s6. fold s7. fold s8.
	set (s9 := {| currentPartition := currentPartition ?s8; memory := _ |}).
	simpl in s7.
	assert(Hfreeslotss9 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s9 (nbfreeslots pd2entry) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s8 (nbfreeslots pd2entry)).
	{
		(* DUP *)
				apply getFreeSlotsListRecEqBE ; intuition.
				---	(* Lists are disjoint at s0, so newB <> firstfreeslot p *)
							unfold getFreeSlotsList in Hoptionlist1s0.
							unfold getFreeSlotsList in Hoptionlist2s0.
							rewrite Hpdinsertions0 in *.
							assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
							{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
							assert(HnewBFirstFrees0P : firstfreeslot pd2entry = newBlockEntryAddr) by intuition.
							rewrite HnewBFirstFrees0PDT in *.
							rewrite HnewBFirstFrees0P in *.
							destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
								rewrite FreeSlotsListRec_unroll in Hoptionlist1s0.
								rewrite FreeSlotsListRec_unroll in Hoptionlist2s0.
								unfold getFreeSlotsListAux in *.
								induction (maxIdx+1). (* false induction because of fixpoint constraints *)
								** (* N=0 -> NotWellFormed *)
									rewrite Hoptionlist1s0 in *.
									cbn in Hwellformed1s0.
									congruence.
								** (* N>0 *)
									clear IHn.
									cbn in *.
									rewrite HlookupnewBs0 in *.
									destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred1 ; try(exfalso ; congruence).
									*** destruct (StateLib.Index.pred (nbfreeslots pd2entry)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
											rewrite Hoptionlist1s0 in *.
											cbn in *.
											unfold Lib.disjoint in HDisjoints0.
											specialize(HDisjoints0 newBlockEntryAddr).
											simpl in HDisjoints0.
											intuition.
									*** rewrite Hoptionlist1s0 in *.
											cbn in Hwellformed1s0.
											exfalso ; congruence.
			--- unfold isBE. unfold s9. cbn.
					destruct (beqAddr pdinsertion newBlockEntryAddr) ; try(exfalso ; congruence).
					rewrite beqAddrTrue.
					cbn.
					repeat rewrite removeDupIdentity ; intuition.
			--- subst listoption2.
					rewrite <- Hfreeslotss1 in *. rewrite <- Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *.
					rewrite <- Hfreeslotss5 in *. rewrite <- Hfreeslotss6 in *.
					rewrite <- Hfreeslotss7 in *. rewrite <- Hfreeslotss8 in *. intuition.
			--- assert(H_NoDups0 : NoDupInFreeSlotsList s0)
							by (unfold consistency in * ; intuition).
					unfold NoDupInFreeSlotsList in *.
					specialize (H_NoDups0 pd2 pd2entry Hlookuppd2s0).
					destruct H_NoDups0 as [optionlist2 (Hoptionlist2 & HwellFormed2' & HNoDup2)].
					unfold getFreeSlotsList in Hoptionlist2.
					rewrite Hlookuppd2s0 in *. rewrite Hpd2Null in *.
					subst optionlist2. subst listoption2.
					rewrite Hfreeslotss1 in *. rewrite Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *.
					rewrite <- Hfreeslotss5 in *. rewrite <- Hfreeslotss6 in *.
					rewrite <- Hfreeslotss7 in *. rewrite <- Hfreeslotss8 in *. intuition.
			--- rewrite <- Hfreeslotss8 in *. rewrite <- Hfreeslotss7 in *.
					rewrite <- Hfreeslotss6 in *. rewrite <- Hfreeslotss5 in *.
					rewrite <- Hfreeslotss4 in *. rewrite <- Hfreeslotss3 in *.
					rewrite Hfreeslotss2 in *. rewrite Hfreeslotss1 in *.
					(* newB is in freeslots list of pdinsertion, so can't be in other list
							because of Disjoint *)
					(* DUP from previous step *)
					unfold getFreeSlotsList in Hoptionlist1s0.
					unfold getFreeSlotsList in Hoptionlist2s0.
					rewrite Hpdinsertions0 in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					rewrite HnewBFirstFrees0PDT in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
					rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
					destruct (beqAddr (firstfreeslot pd2entry) nullAddr) eqn:HfirstfreeNull ; try(exfalso ; congruence).
					(* firstfreeslot p <> NULL *)
					(* if first free of other PD is NOT NULL,
					then newB can't be in the two lists at s0 because of Disjoint -> False *)
					subst listoption2. subst listoption1.
					unfold Lib.disjoint in HDisjoints0.
					specialize(HDisjoints0 newBlockEntryAddr).
					destruct (HDisjoints0).
					* induction (maxIdx+1). (* false induction because of fixpoint constraints *)
						** (* N=0 -> NotWellFormed *)
								cbn in *.
								congruence.
						** (* N>0 *)
								clear IHn.
								simpl. rewrite HlookupnewBs0.
								assert(HcurrNb : currnbfreeslots = nbfreeslots pdentry).
								{ unfold pdentryNbFreeSlots in *. rewrite Hpdinsertions0 in *. intuition. }
								rewrite <- HcurrNb in *.
								destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred ; try(exfalso ; congruence).
								rewrite <- HcurrNb in *. rewrite Hpred. cbn. intuition.
					* intuition.
}
	fold s1. fold s2. fold s3. fold s4. fold s5. fold s6. fold s7. fold s8. fold s9.
	set (s10 := {| currentPartition := currentPartition ?s9; memory := _ |}).
	simpl in s8. simpl in s9.
	assert(Hfreeslotss10 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s10 (nbfreeslots pd2entry) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s9 (nbfreeslots pd2entry)).
	{			assert(HSCEs9 : isSCE sceaddr s9).
						{ unfold isSCE. unfold s9. cbn. rewrite beqAddrTrue.
							destruct (beqAddr newBlockEntryAddr sceaddr) eqn:Hf ; try(exfalso ; congruence).
							rewrite <- beqAddrFalse in *.
							repeat rewrite removeDupIdentity ; intuition.
							destruct (beqAddr pdinsertion newBlockEntryAddr) eqn:Hff ; try(exfalso ; congruence).
							rewrite <- DependentTypeLemmas.beqAddrTrue in Hff. congruence.
							cbn.
							destruct (beqAddr pdinsertion sceaddr) eqn:Hfff ; try(exfalso ; congruence).
							rewrite <- DependentTypeLemmas.beqAddrTrue in Hfff. congruence.
							rewrite beqAddrTrue.
							rewrite <- beqAddrFalse in *.
							repeat rewrite removeDupIdentity ; intuition.
						}
				apply getFreeSlotsListRecEqSCE.
				--- 	intro Hfirstsceeq.
						assert(HFirstFreeSlotPointerIsBEAndFreeSlots0 : FirstFreeSlotPointerIsBEAndFreeSlot s0)
							by (unfold consistency in * ; intuition).
						unfold FirstFreeSlotPointerIsBEAndFreeSlot in *.
						specialize (HFirstFreeSlotPointerIsBEAndFreeSlots0 pd2 pd2entry Hlookuppd2s0).
						destruct HFirstFreeSlotPointerIsBEAndFreeSlots0.
						---- intro HfirstfreeNull.
								assert(HnullAddrExistss0 : nullAddrExists s0)
									by (unfold consistency in * ; intuition).
								unfold nullAddrExists in *.
								unfold isSCE in *.
								unfold isPADDR in *.
								rewrite HfirstfreeNull in *. rewrite <- Hfirstsceeq in *.
								destruct (lookup nullAddr (memory s0) beqAddr) ; try(exfalso ; congruence).
								destruct v ; try(exfalso ; congruence).
						---- rewrite Hfirstsceeq in *.
								unfold isSCE in *.
								unfold isBE in *.
								destruct (lookup sceaddr (memory s0) beqAddr) ; try (exfalso ; congruence).
								destruct v ; try(exfalso ; congruence).
				--- unfold isBE. unfold isSCE in HSCEs9.
						destruct (lookup sceaddr (memory s9) beqAddr) eqn:Hlookupsces9 ; try(exfalso ; congruence).
						destruct v ; try(exfalso ; congruence).
						intuition.
				--- unfold isPADDR. unfold isSCE in HSCEs9.
						destruct (lookup sceaddr (memory s9) beqAddr) eqn:Hlookupsces9 ; try(exfalso ; congruence).
						destruct v ; try(exfalso ; congruence).
						intuition.
}
	fold s1. fold s2. fold s3. fold s4. fold s5. fold s6. fold s7. fold s8. fold s9.
	fold s10.

	intuition.
	assert(HcurrLtmaxIdx : nbfreeslots pd2entry <= maxIdx).
	{ intuition. apply IdxLtMaxIdx. }
	lia.
}
										destruct Hfreeslotspd2Eq as [s1 (s2 & (s3 & (s4 & (s5 & (s6 & (s7 & (s8 & (s9 & (s10 &
																			(n1 & (nbleft & (Hnbleft & Hstates))))))))))))].
										assert(HsEq : s10 = s).
										{ intuition. subst s1. subst s2. subst s3. subst s4. subst s5. subst s6.
											subst s7. subst s8. subst s9. subst s10.
											rewrite Hs. f_equal.
										}
										rewrite HsEq in *.
										(* listoption2 didn't change *)
										assert(HfreeslotsEq : getFreeSlotsListRec n1 (firstfreeslot pd2entry) s (nbfreeslots pd2entry) =
																					getFreeSlotsListRec (maxIdx+1) (firstfreeslot pd2entry) s0 (nbfreeslots pd2entry)).
										{
											intuition.
											subst nbleft.
											(* rewrite all previous getFreeSlotsListRec equalities *)
											rewrite <- H33. rewrite <- H36. rewrite <- H38. rewrite <- H40.
											rewrite <- H42. rewrite <- H44. rewrite <- H46. rewrite <- H48.
											rewrite <- H50. rewrite <- H53.
											reflexivity.
										}
										assert (HfreeslotsEqn1 : getFreeSlotsListRec n1 (firstfreeslot pd2entry) s (nbfreeslots pd2entry)
																							= getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s (nbfreeslots pd2entry)).
										{ eapply getFreeSlotsListRecEqN ; intuition.
											subst nbleft. lia.
											assert (HnbLtmaxIdx : nbfreeslots pd2entry <= maxIdx) by apply IdxLtMaxIdx.
											lia.
										}
										unfold getFreeSlotsList in *.
										rewrite Hlookuppd2Eq in *.
										rewrite Hpdinsertions0 in *. rewrite Hpdinsertions.
										rewrite <- HfreeslotsEqn1. rewrite HfreeslotsEq.
										rewrite HnewFirstFree.
										rewrite <- HnewB in *.
										destruct(beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
										rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
										destruct(beqAddr (firstfreeslot pd2entry) nullAddr) eqn:Hff ; try(exfalso ; congruence).
										destruct H31 as [Hoptionlists (olds & (n0' & (n1' & (n2' & (nbleft' & Hfreeslotsolds')))))].
										exists Hoptionlists. exists listoption2.
										destruct (beqAddr newFirstFreeSlotAddr nullAddr) eqn:beqfirstnull; try(exfalso ; congruence).
										------- (* newFirstFreeSlotAddr = nullAddr *)
														rewrite <- DependentTypeLemmas.beqAddrTrue in beqfirstnull.
														rewrite beqfirstnull in *.
														assert(HoptionlistsNull : Hoptionlists = nil).
														{
															intuition.
															assert(Hoption :  Hoptionlists = getFreeSlotsListRec n0' nullAddr s0 nbleft') by intuition.
															rewrite FreeSlotsListRec_unroll in Hoption.
															unfold getFreeSlotsListAux in Hoption.
															destruct n0'.
															rewrite Hoption in *. cbn in *. congruence.
															destruct (StateLib.Index.ltb nbleft' zero).
															rewrite Hoption in *. cbn in *. congruence.
															assert(HNullAddrExistss0 : nullAddrExists s0)
																	by (unfold consistency in * ; intuition).
															unfold nullAddrExists in *.
															unfold isPADDR in *.
															destruct (lookup nullAddr (memory s0) beqAddr) ; try(exfalso ; congruence).
															destruct v ; try(exfalso ; congruence).
															rewrite beqAddrTrue in Hoption.
															rewrite Hoption in *. cbn in *. congruence.
														}
														intuition.
														rewrite HoptionlistsNull in *.
														unfold Lib.disjoint. intros. intuition.
										------- (* newFirstFreeSlotAddr <> nullAddr *)
														assert(HoptionlistEq : Hoptionlists = getFreeSlotsListRec (maxIdx + 1) newFirstFreeSlotAddr s (nbfreeslots pdentry1)).
														{ subst pdentry1. (* pdentry1 *) cbn.
														assert(HpredNbLeftEq : predCurrentNbFreeSlots = nbleft').
														{ intuition. subst nbleft'. unfold StateLib.Index.pred in *.
															destruct (gt_dec currnbfreeslots 0) ; intuition.
															inversion H1. (* Some ... = Some predCurrentNbFreeSlots *)
															unfold CIndex.
															assert(HnbLtmaxIdx : currnbfreeslots - 1 < maxIdx).
															{ 
																assert(HcurrLtmaxIdx : currnbfreeslots <= maxIdx).
																{ intuition. apply IdxLtMaxIdx. }
																lia.
															}
															destruct (le_dec (currnbfreeslots - 1) maxIdx) ; intuition.
															f_equal. apply proof_irrelevance.
														}
														rewrite HpredNbLeftEq.
														assert(HoptionlistEq : getFreeSlotsListRec n2' newFirstFreeSlotAddr s nbleft' = Hoptionlists) by intuition.
														rewrite <- HoptionlistEq. (* n2 s = Hoptionlist *)
														eapply getFreeSlotsListRecEqN ; intuition.
														}
														(* we know listoption2 and Hoptionlist haven't changed
																and as Hoptionlist is a subset of listoption1
															and from the beginning they were disjoint, so still disjoint at s *)
														assert(HIncl : incl (filterOption Hoptionlists) (filterOption listoption1)).
														{
															rewrite FreeSlotsListRec_unroll in Hoptionlist1s0.
															unfold getFreeSlotsListAux in Hoptionlist1s0.
															assert(HMaxIdxNext : maxIdx + 1 = S maxIdx).
															{ lia. }
															rewrite HMaxIdxNext in *.
															assert(Hnbfreeslots : (nbfreeslots pdentry) = currnbfreeslots).
															{ unfold pdentryNbFreeSlots in *. rewrite Hpdinsertions0 in *. intuition. }
															rewrite Hnbfreeslots in *.
															destruct (StateLib.Index.ltb currnbfreeslots zero) eqn:Hltb ; try(exfalso ; congruence).
															* unfold StateLib.Index.ltb in Hltb.
																apply PeanoNat.Nat.ltb_lt in Hltb.
																contradict Hltb. apply PeanoNat.Nat.lt_asymm. intuition.
															* rewrite HlookupnewBs0 in *.
																destruct (StateLib.Index.pred currnbfreeslots) eqn:Hpred ; try(exfalso ; congruence).
																assert(Hoptionlists0 : Hoptionlists =
                  												getFreeSlotsListRec n0' newFirstFreeSlotAddr s0 nbleft') by intuition.
																rewrite Hoptionlists0.
																assert(HnewBEndIsNewFirst : (endAddr (blockrange bentry)) = newFirstFreeSlotAddr).
																{ unfold bentryEndAddr in *. rewrite HlookupnewBs0 in *. intuition. }
																rewrite HnewBEndIsNewFirst in *.
																assert(HnbLtmaxIdx : currnbfreeslots - 1 < maxIdx).
																{
																		unfold pdentryNbFreeSlots in *. rewrite Hpdinsertions0 in *.
																		destruct currnbfreeslots.
																		+ simpl. destruct i0.
																			* simpl. apply maxIdxNotZero.
																			* cbn. rewrite PeanoNat.Nat.sub_0_r. intuition.
																}
																assert((CIndex (currnbfreeslots - 1)) = i).
																{ unfold CIndex.
																	destruct (le_dec (currnbfreeslots - 1) maxIdx) ; simpl in * ; intuition ; try(exfalso ; congruence).
																		unfold StateLib.Index.pred in *.
																		destruct (gt_dec currnbfreeslots 0) ; try(exfalso ; congruence).
																		inversion Hpred. f_equal. apply proof_irrelevance.
																}
																unfold pdentryNbFreeSlots in *. rewrite H5 in *.
																rewrite H8 in *.
																assert(i < maxIdx).
																{	unfold StateLib.Index.pred in *.
																	destruct (gt_dec currnbfreeslots 0) ; try(exfalso ; congruence).
																	inversion Hpred. simpl. intuition.
																}
																assert(HEq : getFreeSlotsListRec maxIdx newFirstFreeSlotAddr s0 i =
																								getFreeSlotsListRec (maxIdx+1) newFirstFreeSlotAddr s0 i).
																{
																	eapply getFreeSlotsListRecEqN ; intuition.
																}
																rewrite HEq in *.
																subst nbleft. subst listoption1.
																assert(HnbleftEq': nbleft' = i).
																{ intuition. subst nbleft'. intuition. }
																rewrite HnbleftEq' in *.
																assert(HEq' : getFreeSlotsListRec n0' newFirstFreeSlotAddr s0 i =
																										getFreeSlotsListRec (maxIdx + 1) newFirstFreeSlotAddr s0 i).
																{
																	eapply getFreeSlotsListRecEqN ; intuition.
																	{ lia. }
																}
																rewrite HEq'. intuition.
																cbn. intuition.
														}
														intuition.
														eapply Lib.inclDisjoint.
														apply HDisjoints0. intuition. intuition.
									----- (* 2) pdinsertion <> pd1 *)
											(* similarly, we must prove optionfreeslotslist1 is strictly
													the same at s than at s0 by recomputing each
													intermediate steps and check at that time *)
											assert(Hlookuppd1Eq : lookup pd1 (memory s) beqAddr = lookup pd1 (memory s0) beqAddr).
											{
												rewrite Hs.
												cbn. rewrite beqAddrTrue.
												rewrite beqscepd1.
												assert(HnewBsceNotEq : beqAddr newBlockEntryAddr sceaddr = false) by intuition.
												rewrite HnewBsceNotEq. (*newBlock <> sce *)
												cbn.
												rewrite beqnewpd1. (*pd1 <> newblock*)
												rewrite beqAddrTrue.
												rewrite <- beqAddrFalse in *.
												repeat rewrite removeDupIdentity ; intuition.
												destruct (beqAddr pdinsertion newBlockEntryAddr) eqn:Hf ; try(exfalso ; congruence).
												rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
												cbn.
												destruct (beqAddr pdinsertion pd1) eqn:Hff ; try(exfalso ; congruence).
												rewrite <- DependentTypeLemmas.beqAddrTrue in Hff. congruence.
												rewrite <- beqAddrFalse in *.
												repeat rewrite removeDupIdentity ; intuition.
											}
										assert(HPDTpd1Eq : isPDT pd1 s = isPDT pd1 s0).
										{ unfold isPDT. rewrite Hlookuppd1Eq. intuition. }
										assert(HPDTpd1s0 : isPDT pd1 s0) by (rewrite HPDTpd1Eq in * ; assumption).
											(* DUP of previous steps to show strict equality of listoption2
												at s and s0 *)
										destruct (beqAddr pdinsertion pd2) eqn:beqpdpd2; try(exfalso ; congruence).
										------ (* 3) pdinsertion = pd2 *)
													(* DUP of pdinsertion = pd1 *)
													rewrite <- DependentTypeLemmas.beqAddrTrue in beqpdpd2.
													rewrite <- beqpdpd2 in *.
													(* DUP with pd1 instead of pd2 *)
													assert(Hpd1pd2NotEq' : pdinsertion <> pd1 ) by intuition.
													specialize(Hcons0 pdinsertion pd1 HPDTs0 HPDTpd1s0 Hpd1pd2NotEq').
													destruct Hcons0 as [listoption1 (listoption2 & (Hoptionlist1s0 & (Hwellformed1s0 & (Hoptionlist2s0 & (Hwellformed2s0 & HDisjoints0)))))].
													(* Show equality between listoption2 at s and listoption2 at s0 *)
													unfold getFreeSlotsList in Hoptionlist2s0.
													apply isPDTLookupEq in HPDTpd1s0. destruct HPDTpd1s0 as [pd1entry Hlookuppd1s0].
													rewrite Hlookuppd1s0 in *.
													destruct (beqAddr (firstfreeslot pd1entry) nullAddr) eqn:Hpd1Null ; try(exfalso ; congruence).
													------- (* listoption2 = NIL *)
																destruct H31 as [Hoptionlists (olds & (n0 & (n1 & (n2 & (nbleft & Hfreeslotsolds)))))].
																exists listoption2. exists Hoptionlists.
																assert(Hlistoption2s : getFreeSlotsList pd1 s = nil).
																{
																	unfold getFreeSlotsList.
																	rewrite Hlookuppd1Eq. rewrite Hpd1Null. reflexivity.
																}
																rewrite Hlistoption2s in *. intuition.
																unfold getFreeSlotsList. rewrite Hpdinsertions.
																rewrite HnewFirstFree.
																assert(Hnbleft : nbfreeslots pdentry1 = nbleft).
																{ (* DUP *)
																	subst pdentry1. simpl. intuition.
																	rewrite H30. (* nbleft = CIndex (currnbfreeslots - 1)*)
																	destruct predCurrentNbFreeSlots.
																	unfold StateLib.Index.pred in H1.
																	destruct (gt_dec currnbfreeslots 0); try (exfalso ; congruence).
																	unfold CIndex. inversion H1 as [Hpred].
																	rewrite Hpred. destruct (le_dec i maxIdx) ; try(exfalso ; congruence).
																	f_equal. apply proof_irrelevance.
																}
																rewrite Hnbleft.
																assert(HfreeSlotsListEq : Hoptionlists = getFreeSlotsListRec (maxIdx + 1) newFirstFreeSlotAddr s nbleft).
																{ intuition.
																	rewrite <- H34. (* getFreeSlotsList s = Hoptionlists *)
																	eapply getFreeSlotsListRecEqN ; intuition.
																}
																rewrite <- HfreeSlotsListEq.
																destruct (beqAddr newFirstFreeSlotAddr nullAddr) eqn:beqfirstnull; try(exfalso ; congruence).
																-------- (* newFirstFreeSlotAddr = nullAddr *)
																				rewrite <- DependentTypeLemmas.beqAddrTrue in beqfirstnull.
																				rewrite beqfirstnull in *.
																				intuition.
																				assert(Hoption :  Hoptionlists = getFreeSlotsListRec n0 nullAddr s0 nbleft) by intuition.
																				rewrite FreeSlotsListRec_unroll in Hoption.
																				unfold getFreeSlotsListAux in Hoption.
																				destruct n0.
																				rewrite Hoption in *. cbn in *. congruence.
																				destruct (StateLib.Index.ltb nbleft zero).
																				rewrite Hoption in *. cbn in *. congruence.
																				assert(HNullAddrExistss0 : nullAddrExists s0)
																						by (unfold consistency in * ; intuition).
																				unfold nullAddrExists in *.
																				unfold isPADDR in *.
																				destruct (lookup nullAddr (memory s0) beqAddr) ; try(exfalso ; congruence).
																				destruct v ; try(exfalso ; congruence).
																				destruct (beqAddr p nullAddr).
																				rewrite Hoption in *. cbn in *. congruence.
																				rewrite Hoption in *. cbn in *. congruence.
																-------- (* newFirstFreeSlotAddr <> nullAddr *)
																				intuition.
																-------- (* Disjoint : listoption2 = NIL *)
																				subst listoption2. cbn.
																				unfold Lib.disjoint. intuition.
													------- (* listoption2 <> NIL *)
																	(* WIP show equality between listoption2 at s and s0 
																			+ if listoption2 has NOT changed, listoption1 at s is
																			just a subset of listoption1 at s0 so they are
																			still disjoint *)
																	assert(Hfreeslotspd1Eq : exists s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 n1 nbleft,
nbleft = (nbfreeslots pd1entry) /\
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
                     vidtBlock := vidtBlock pdentry
                   |}) (memory s0) beqAddr |} /\
getFreeSlotsListRec n1 (firstfreeslot pd1entry) s1 nbleft =
getFreeSlotsListRec (maxIdx+1) (firstfreeslot pd1entry) s0 nbleft
			 /\
	n1 <= maxIdx+1 /\ nbleft < n1
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
		                vidtBlock := vidtBlock pdentry0
		              |}
                 ) (memory s1) beqAddr |} /\
getFreeSlotsListRec n1 (firstfreeslot pd1entry) s2 nbleft =
			getFreeSlotsListRec n1 (firstfreeslot pd1entry) s1 nbleft
/\ s3 = {|
     currentPartition := currentPartition s2;
     memory := add newBlockEntryAddr
	            (BE
	               (CBlockEntry (read bentry) 
	                  (write bentry) (exec bentry) 
	                  (present bentry) (accessible bentry)
	                  (blockindex bentry)
	                  (CBlock startaddr (endAddr (blockrange bentry))))
                 ) (memory s2) beqAddr |} /\
getFreeSlotsListRec n1 (firstfreeslot pd1entry) s3 nbleft =
			getFreeSlotsListRec n1 (firstfreeslot pd1entry) s2 nbleft
/\ s4 = {|
     currentPartition := currentPartition s3;
     memory := add newBlockEntryAddr
               (BE
                  (CBlockEntry (read bentry0) 
                     (write bentry0) (exec bentry0) 
                     (present bentry0) (accessible bentry0)
                     (blockindex bentry0)
                     (CBlock (startAddr (blockrange bentry0)) endaddr))
                 ) (memory s3) beqAddr |} /\
getFreeSlotsListRec n1 (firstfreeslot pd1entry) s4 nbleft =
			getFreeSlotsListRec n1 (firstfreeslot pd1entry) s3 nbleft
/\ s5 = {|
     currentPartition := currentPartition s4;
     memory := add newBlockEntryAddr
              (BE
                 (CBlockEntry (read bentry1) 
                    (write bentry1) (exec bentry1) 
                    (present bentry1) true (blockindex bentry1)
                    (blockrange bentry1))
                 ) (memory s4) beqAddr |} /\
getFreeSlotsListRec n1 (firstfreeslot pd1entry) s5 nbleft =
			getFreeSlotsListRec n1 (firstfreeslot pd1entry) s4 nbleft
/\ s6 = {|
     currentPartition := currentPartition s5;
     memory := add newBlockEntryAddr
               (BE
                  (CBlockEntry (read bentry2) (write bentry2) 
                     (exec bentry2) true (accessible bentry2)
                     (blockindex bentry2) (blockrange bentry2))
                 ) (memory s5) beqAddr |} /\
getFreeSlotsListRec n1 (firstfreeslot pd1entry) s6 nbleft =
			getFreeSlotsListRec n1 (firstfreeslot pd1entry) s5 nbleft
/\ s7 = {|
     currentPartition := currentPartition s6;
     memory := add newBlockEntryAddr
              (BE
                 (CBlockEntry r (write bentry3) (exec bentry3)
                    (present bentry3) (accessible bentry3) 
                    (blockindex bentry3) (blockrange bentry3))
                 ) (memory s6) beqAddr |} /\
getFreeSlotsListRec n1 (firstfreeslot pd1entry) s7 nbleft =
			getFreeSlotsListRec n1 (firstfreeslot pd1entry) s6 nbleft
/\ s8 = {|
     currentPartition := currentPartition s7;
     memory := add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry4) w (exec bentry4) 
                       (present bentry4) (accessible bentry4) 
                       (blockindex bentry4) (blockrange bentry4))
                 ) (memory s7) beqAddr |} /\
getFreeSlotsListRec n1(firstfreeslot pd1entry) s8 nbleft =
			getFreeSlotsListRec n1 (firstfreeslot pd1entry) s7 nbleft
/\ s9 = {|
     currentPartition := currentPartition s8;
     memory := add newBlockEntryAddr
              (BE
                 (CBlockEntry (read bentry5) (write bentry5) e 
                    (present bentry5) (accessible bentry5) 
                    (blockindex bentry5) (blockrange bentry5))
                 ) (memory s8) beqAddr |} /\
getFreeSlotsListRec n1 (firstfreeslot pd1entry) s9 nbleft =
			getFreeSlotsListRec n1 (firstfreeslot pd1entry) s8 nbleft
/\ s10 = {|
     currentPartition := currentPartition s9;
     memory := add sceaddr 
								(SCE {| origin := origin; next := next scentry |}
                 ) (memory s9) beqAddr |} /\
getFreeSlotsListRec n1 (firstfreeslot pd1entry) s10 nbleft =
			getFreeSlotsListRec n1 (firstfreeslot pd1entry) s9 nbleft
).
{
	eexists ?[s1]. eexists ?[s2]. eexists ?[s3]. eexists ?[s4]. eexists ?[s5].
	eexists ?[s6]. eexists ?[s7]. eexists ?[s8]. eexists ?[s9].
	eexists ?[s10]. eexists ?[n1]. eexists.
	split. intuition.
	split. intuition.
	set (s1 := {| currentPartition := _ |}).
	(* prove outside *)
	assert(Hfreeslotss1 : getFreeSlotsListRec ?n1 (firstfreeslot pd1entry) s1 (nbfreeslots pd1entry) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd1entry) s0 (nbfreeslots pd1entry)).
	{
		apply getFreeSlotsListRecEqPDT.
		-- 	intro Hfirstpdeq.
				assert(HFirstFreeSlotPointerIsBEAndFreeSlots0 : FirstFreeSlotPointerIsBEAndFreeSlot s0)
					by (unfold consistency in * ; intuition).
				unfold FirstFreeSlotPointerIsBEAndFreeSlot in *.
				specialize (HFirstFreeSlotPointerIsBEAndFreeSlots0 pd1 pd1entry Hlookuppd1s0).
				destruct HFirstFreeSlotPointerIsBEAndFreeSlots0.
				--- intro HfirstfreeNull.
						assert(HnullAddrExistss0 : nullAddrExists s0)
							by (unfold consistency in * ; intuition).
						unfold nullAddrExists in *.
						unfold isPADDR in *.
						rewrite HfirstfreeNull in *. rewrite <- Hfirstpdeq in *.
						destruct (lookup nullAddr (memory s0) beqAddr) ; try(exfalso ; congruence).
						destruct v ; try(exfalso ; congruence).
				--- rewrite Hfirstpdeq in *.
						unfold isBE in *.
						destruct (lookup pdinsertion (memory s0) beqAddr) ; try (exfalso ; congruence).
						destruct v ; try(exfalso ; congruence).
		-- unfold isBE. rewrite Hpdinsertions0. intuition.
		-- unfold isPADDR. rewrite Hpdinsertions0. intuition.
	}
	set (s2 := {| currentPartition := _ |}).
	assert(Hfreeslotss2 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd1entry) s2 (nbfreeslots pd1entry) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd1entry) s1 (nbfreeslots pd1entry)).
	{
				apply getFreeSlotsListRecEqPDT.
				--- 	intro Hfirstpdeq.
						assert(HFirstFreeSlotPointerIsBEAndFreeSlots0 : FirstFreeSlotPointerIsBEAndFreeSlot s0)
							by (unfold consistency in * ; intuition).
						unfold FirstFreeSlotPointerIsBEAndFreeSlot in *.
						specialize (HFirstFreeSlotPointerIsBEAndFreeSlots0 pd1 pd1entry Hlookuppd1s0).
						destruct HFirstFreeSlotPointerIsBEAndFreeSlots0.
						---- intro HfirstfreeNull.
								assert(HnullAddrExistss0 : nullAddrExists s0)
									by (unfold consistency in * ; intuition).
								unfold nullAddrExists in *.
								unfold isPADDR in *.
								rewrite HfirstfreeNull in *. rewrite <- Hfirstpdeq in *.
								destruct (lookup nullAddr (memory s0) beqAddr) ; try(exfalso ; congruence).
								destruct v ; try(exfalso ; congruence).
						---- rewrite Hfirstpdeq in *.
								unfold isBE in *.
								destruct (lookup pdinsertion (memory s0) beqAddr) ; try (exfalso ; congruence).
								destruct v ; try(exfalso ; congruence).
				--- unfold isBE. unfold s1. cbn. rewrite beqAddrTrue. intuition.
				--- unfold isPADDR. unfold s1. cbn. rewrite beqAddrTrue. intuition.
	}
	set (s3 := {| currentPartition := _ |}).
	assert(Hfreeslotss3 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd1entry) s3 (nbfreeslots pd1entry) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd1entry) s2 (nbfreeslots pd1entry)).
	{
				apply getFreeSlotsListRecEqBE ; intuition.
				---	(* Lists are disjoint at s0, so newB <> firstfreeslot pd1entry *)
							unfold getFreeSlotsList in Hoptionlist1s0.
							unfold getFreeSlotsList in Hoptionlist2s0.
							rewrite Hpdinsertions0 in *.
							assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
							{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
							assert(HnewBFirstFrees0P : firstfreeslot pd1entry = newBlockEntryAddr) by intuition.
							rewrite HnewBFirstFrees0PDT in *.
							rewrite HnewBFirstFrees0P in *.
							destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
								rewrite FreeSlotsListRec_unroll in Hoptionlist1s0.
								rewrite FreeSlotsListRec_unroll in Hoptionlist2s0.
								unfold getFreeSlotsListAux in *.
								induction (maxIdx+1). (* false induction because of fixpoint constraints *)
								** (* N=0 -> NotWellFormed *)
									rewrite Hoptionlist1s0 in *.
									cbn in Hwellformed1s0.
									congruence.
								** (* N>0 *)
									clear IHn.
									cbn in *.
									rewrite HlookupnewBs0 in *.
									destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred1 ; try(exfalso ; congruence).
									*** destruct (StateLib.Index.pred (nbfreeslots pd1entry)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
											rewrite Hoptionlist1s0 in *.
											cbn in *.
											unfold Lib.disjoint in HDisjoints0.
											specialize(HDisjoints0 newBlockEntryAddr).
											simpl in HDisjoints0.
											intuition.
									*** rewrite Hoptionlist1s0 in *.
											cbn in Hwellformed1s0.
											exfalso ; congruence.
			--- unfold isBE. unfold s3. cbn.
					destruct (beqAddr pdinsertion newBlockEntryAddr) ; try(exfalso ; congruence).
					rewrite beqAddrTrue.
					cbn.
					repeat rewrite removeDupIdentity ; intuition.
			--- subst listoption2.
					rewrite <- Hfreeslotss1 in *. rewrite <- Hfreeslotss2 in *. intuition.
			--- assert(H_NoDups0 : NoDupInFreeSlotsList s0)
							by (unfold consistency in * ; intuition).
					unfold NoDupInFreeSlotsList in *.
					specialize (H_NoDups0 pd1 pd1entry Hlookuppd1s0).
					destruct H_NoDups0 as [optionlist2 (Hoptionlist2 & HwellFormed2' & HNoDup2)].
					unfold getFreeSlotsList in Hoptionlist2.
					rewrite Hlookuppd1s0 in *. rewrite Hpd1Null in *.
					subst optionlist2. subst listoption2.
					rewrite Hfreeslotss1 in *. rewrite Hfreeslotss2 in *. intuition.
			--- rewrite Hfreeslotss2 in *. rewrite Hfreeslotss1 in *.
					(* newB is in freeslots list of pdinsertion, so can't be in other list
							because of Disjoint *)
					(* DUP from previous step *)
					unfold getFreeSlotsList in Hoptionlist1s0.
					unfold getFreeSlotsList in Hoptionlist2s0.
					rewrite Hpdinsertions0 in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					rewrite HnewBFirstFrees0PDT in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
					rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
					destruct (beqAddr (firstfreeslot pd1entry) nullAddr) eqn:HfirstfreeNull ; try(exfalso ; congruence).
					(* firstfreeslot p <> NULL *)
					(* if first free of other PD is NOT NULL,
					then newB can't be in the two lists at s0 because of Disjoint -> False *)
					subst listoption2. subst listoption1.
					unfold Lib.disjoint in HDisjoints0.
					specialize(HDisjoints0 newBlockEntryAddr).
					destruct (HDisjoints0).
					* induction (maxIdx+1). (* false induction because of fixpoint constraints *)
						** (* N=0 -> NotWellFormed *)
								cbn in *.
								congruence.
						** (* N>0 *)
								clear IHn.
								simpl. rewrite HlookupnewBs0.
								assert(HcurrNb : currnbfreeslots = nbfreeslots pdentry).
								{ unfold pdentryNbFreeSlots in *. rewrite Hpdinsertions0 in *. intuition. }
								rewrite <- HcurrNb in *.
								destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred ; try(exfalso ; congruence).
								rewrite <- HcurrNb in *. rewrite Hpred. cbn. intuition.
					* intuition.
}
	set (s4 := {| currentPartition := currentPartition ?s3; memory := _ |}). simpl in s4. simpl in s3.
	assert(Hfreeslotss4 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd1entry) s4 (nbfreeslots pd1entry) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd1entry) s3 (nbfreeslots pd1entry)).
	{
		(* DUP *)
				apply getFreeSlotsListRecEqBE ; intuition.
				---	(* Lists are disjoint at s0, so newB <> firstfreeslot p *)
							unfold getFreeSlotsList in Hoptionlist1s0.
							unfold getFreeSlotsList in Hoptionlist2s0.
							rewrite Hpdinsertions0 in *.
							assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
							{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
							assert(HnewBFirstFrees0P : firstfreeslot pd1entry = newBlockEntryAddr) by intuition.
							rewrite HnewBFirstFrees0PDT in *.
							rewrite HnewBFirstFrees0P in *.
							destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
								rewrite FreeSlotsListRec_unroll in Hoptionlist1s0.
								rewrite FreeSlotsListRec_unroll in Hoptionlist2s0.
								unfold getFreeSlotsListAux in *.
								induction (maxIdx+1). (* false induction because of fixpoint constraints *)
								** (* N=0 -> NotWellFormed *)
									rewrite Hoptionlist1s0 in *.
									cbn in Hwellformed1s0.
									congruence.
								** (* N>0 *)
									clear IHn.
									cbn in *.
									rewrite HlookupnewBs0 in *.
									destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred1 ; try(exfalso ; congruence).
									*** destruct (StateLib.Index.pred (nbfreeslots pd1entry)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
											rewrite Hoptionlist1s0 in *.
											cbn in *.
											unfold Lib.disjoint in HDisjoints0.
											specialize(HDisjoints0 newBlockEntryAddr).
											simpl in HDisjoints0.
											intuition.
									*** rewrite Hoptionlist1s0 in *.
											cbn in Hwellformed1s0.
											exfalso ; congruence.
			--- unfold isBE. unfold s4. cbn.
					destruct (beqAddr pdinsertion newBlockEntryAddr) ; try(exfalso ; congruence).
					rewrite beqAddrTrue.
					cbn.
					repeat rewrite removeDupIdentity ; intuition.
			--- subst listoption2.
					rewrite <- Hfreeslotss1 in *. rewrite <- Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. intuition.
			--- assert(H_NoDups0 : NoDupInFreeSlotsList s0)
							by (unfold consistency in * ; intuition).
					unfold NoDupInFreeSlotsList in *.
					specialize (H_NoDups0 pd1 pd1entry Hlookuppd1s0).
					destruct H_NoDups0 as [optionlist2 (Hoptionlist2 & HwellFormed2' & HNoDup2)].
					unfold getFreeSlotsList in Hoptionlist2.
					rewrite Hlookuppd1s0 in *. rewrite Hpd1Null in *.
					subst optionlist2. subst listoption2.
					rewrite Hfreeslotss1 in *. rewrite Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. intuition.
			--- rewrite <- Hfreeslotss3 in *.
					rewrite Hfreeslotss2 in *. rewrite Hfreeslotss1 in *.
					(* newB is in freeslots list of pdinsertion, so can't be in other list
							because of Disjoint *)
					(* DUP from previous step *)
					unfold getFreeSlotsList in Hoptionlist1s0.
					unfold getFreeSlotsList in Hoptionlist2s0.
					rewrite Hpdinsertions0 in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					rewrite HnewBFirstFrees0PDT in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
					rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
					destruct (beqAddr (firstfreeslot pd1entry) nullAddr) eqn:HfirstfreeNull ; try(exfalso ; congruence).
					(* firstfreeslot p <> NULL *)
					(* if first free of other PD is NOT NULL,
					then newB can't be in the two lists at s0 because of Disjoint -> False *)
					subst listoption2. subst listoption1.
					unfold Lib.disjoint in HDisjoints0.
					specialize(HDisjoints0 newBlockEntryAddr).
					destruct (HDisjoints0).
					* induction (maxIdx+1). (* false induction because of fixpoint constraints *)
						** (* N=0 -> NotWellFormed *)
								cbn in *.
								congruence.
						** (* N>0 *)
								clear IHn.
								simpl. rewrite HlookupnewBs0.
								assert(HcurrNb : currnbfreeslots = nbfreeslots pdentry).
								{ unfold pdentryNbFreeSlots in *. rewrite Hpdinsertions0 in *. intuition. }
								rewrite <- HcurrNb in *.
								destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred ; try(exfalso ; congruence).
								rewrite <- HcurrNb in *. rewrite Hpred. cbn. intuition.
					* intuition.
} fold s1. fold s2. fold s3. fold s4.
	set (s5 := {| currentPartition := currentPartition ?s4; memory := _ |}).
	simpl in s4.
	assert(Hfreeslotss5 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd1entry) s5 (nbfreeslots pd1entry) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd1entry) s4 (nbfreeslots pd1entry)).
	{
		(* DUP *)
				apply getFreeSlotsListRecEqBE ; intuition.
				---	(* Lists are disjoint at s0, so newB <> firstfreeslot p *)
							unfold getFreeSlotsList in Hoptionlist1s0.
							unfold getFreeSlotsList in Hoptionlist2s0.
							rewrite Hpdinsertions0 in *.
							assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
							{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
							assert(HnewBFirstFrees0P : firstfreeslot pd1entry = newBlockEntryAddr) by intuition.
							rewrite HnewBFirstFrees0PDT in *.
							rewrite HnewBFirstFrees0P in *.
							destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
								rewrite FreeSlotsListRec_unroll in Hoptionlist1s0.
								rewrite FreeSlotsListRec_unroll in Hoptionlist2s0.
								unfold getFreeSlotsListAux in *.
								induction (maxIdx+1). (* false induction because of fixpoint constraints *)
								** (* N=0 -> NotWellFormed *)
									rewrite Hoptionlist1s0 in *.
									cbn in Hwellformed1s0.
									congruence.
								** (* N>0 *)
									clear IHn.
									cbn in *.
									rewrite HlookupnewBs0 in *.
									destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred1 ; try(exfalso ; congruence).
									*** destruct (StateLib.Index.pred (nbfreeslots pd1entry)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
											rewrite Hoptionlist1s0 in *.
											cbn in *.
											unfold Lib.disjoint in HDisjoints0.
											specialize(HDisjoints0 newBlockEntryAddr).
											simpl in HDisjoints0.
											intuition.
									*** rewrite Hoptionlist1s0 in *.
											cbn in Hwellformed1s0.
											exfalso ; congruence.
			--- unfold isBE. unfold s5. cbn.
					destruct (beqAddr pdinsertion newBlockEntryAddr) ; try(exfalso ; congruence).
					rewrite beqAddrTrue.
					cbn.
					repeat rewrite removeDupIdentity ; intuition.
			--- subst listoption2.
					rewrite <- Hfreeslotss1 in *. rewrite <- Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *. intuition.
			--- assert(H_NoDups0 : NoDupInFreeSlotsList s0)
							by (unfold consistency in * ; intuition).
					unfold NoDupInFreeSlotsList in *.
					specialize (H_NoDups0 pd1 pd1entry Hlookuppd1s0).
					destruct H_NoDups0 as [optionlist2 (Hoptionlist2 & HwellFormed2' & HNoDup2)].
					unfold getFreeSlotsList in Hoptionlist2.
					rewrite Hlookuppd1s0 in *. rewrite Hpd1Null in *.
					subst optionlist2. subst listoption2.
					rewrite Hfreeslotss1 in *. rewrite Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *. intuition.
			--- rewrite <- Hfreeslotss4 in *. rewrite <- Hfreeslotss3 in *.
					rewrite Hfreeslotss2 in *. rewrite Hfreeslotss1 in *.
					(* newB is in freeslots list of pdinsertion, so can't be in other list
							because of Disjoint *)
					(* DUP from previous step *)
					unfold getFreeSlotsList in Hoptionlist1s0.
					unfold getFreeSlotsList in Hoptionlist2s0.
					rewrite Hpdinsertions0 in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					rewrite HnewBFirstFrees0PDT in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
					rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
					destruct (beqAddr (firstfreeslot pd1entry) nullAddr) eqn:HfirstfreeNull ; try(exfalso ; congruence).
					(* firstfreeslot p <> NULL *)
					(* if first free of other PD is NOT NULL,
					then newB can't be in the two lists at s0 because of Disjoint -> False *)
					subst listoption2. subst listoption1.
					unfold Lib.disjoint in HDisjoints0.
					specialize(HDisjoints0 newBlockEntryAddr).
					destruct (HDisjoints0).
					* induction (maxIdx+1). (* false induction because of fixpoint constraints *)
						** (* N=0 -> NotWellFormed *)
								cbn in *.
								congruence.
						** (* N>0 *)
								clear IHn.
								simpl. rewrite HlookupnewBs0.
								assert(HcurrNb : currnbfreeslots = nbfreeslots pdentry).
								{ unfold pdentryNbFreeSlots in *. rewrite Hpdinsertions0 in *. intuition. }
								rewrite <- HcurrNb in *.
								destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred ; try(exfalso ; congruence).
								rewrite <- HcurrNb in *. rewrite Hpred. cbn. intuition.
					* intuition.
}
	fold s1. fold s2. fold s3. fold s4. fold s5.
	set (s6 := {| currentPartition := currentPartition ?s5; memory := _ |}).
	simpl in s4.
	assert(Hfreeslotss6 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd1entry) s6 (nbfreeslots pd1entry) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd1entry) s5 (nbfreeslots pd1entry)).
	{
		(* DUP *)
				apply getFreeSlotsListRecEqBE ; intuition.
				---	(* Lists are disjoint at s0, so newB <> firstfreeslot p *)
							unfold getFreeSlotsList in Hoptionlist1s0.
							unfold getFreeSlotsList in Hoptionlist2s0.
							rewrite Hpdinsertions0 in *.
							assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
							{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
							assert(HnewBFirstFrees0P : firstfreeslot pd1entry = newBlockEntryAddr) by intuition.
							rewrite HnewBFirstFrees0PDT in *.
							rewrite HnewBFirstFrees0P in *.
							destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
								rewrite FreeSlotsListRec_unroll in Hoptionlist1s0.
								rewrite FreeSlotsListRec_unroll in Hoptionlist2s0.
								unfold getFreeSlotsListAux in *.
								induction (maxIdx+1). (* false induction because of fixpoint constraints *)
								** (* N=0 -> NotWellFormed *)
									rewrite Hoptionlist1s0 in *.
									cbn in Hwellformed1s0.
									congruence.
								** (* N>0 *)
									clear IHn.
									cbn in *.
									rewrite HlookupnewBs0 in *.
									destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred1 ; try(exfalso ; congruence).
									*** destruct (StateLib.Index.pred (nbfreeslots pd1entry)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
											rewrite Hoptionlist1s0 in *.
											cbn in *.
											unfold Lib.disjoint in HDisjoints0.
											specialize(HDisjoints0 newBlockEntryAddr).
											simpl in HDisjoints0.
											intuition.
									*** rewrite Hoptionlist1s0 in *.
											cbn in Hwellformed1s0.
											exfalso ; congruence.
			--- unfold isBE. unfold s6. cbn.
					destruct (beqAddr pdinsertion newBlockEntryAddr) ; try(exfalso ; congruence).
					rewrite beqAddrTrue.
					cbn.
					repeat rewrite removeDupIdentity ; intuition.
			--- subst listoption2.
					rewrite <- Hfreeslotss1 in *. rewrite <- Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *.
					rewrite <- Hfreeslotss5 in *. intuition.
			--- assert(H_NoDups0 : NoDupInFreeSlotsList s0)
							by (unfold consistency in * ; intuition).
					unfold NoDupInFreeSlotsList in *.
					specialize (H_NoDups0 pd1 pd1entry Hlookuppd1s0).
					destruct H_NoDups0 as [optionlist2 (Hoptionlist2 & HwellFormed2' & HNoDup2)].
					unfold getFreeSlotsList in Hoptionlist2.
					rewrite Hlookuppd1s0 in *. rewrite Hpd1Null in *.
					subst optionlist2. subst listoption2.
					rewrite Hfreeslotss1 in *. rewrite Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *.
					rewrite <- Hfreeslotss5 in *. intuition.
			--- rewrite <- Hfreeslotss5 in *.
					rewrite <- Hfreeslotss4 in *. rewrite <- Hfreeslotss3 in *.
					rewrite Hfreeslotss2 in *. rewrite Hfreeslotss1 in *.
					(* newB is in freeslots list of pdinsertion, so can't be in other list
							because of Disjoint *)
					(* DUP from previous step *)
					unfold getFreeSlotsList in Hoptionlist1s0.
					unfold getFreeSlotsList in Hoptionlist2s0.
					rewrite Hpdinsertions0 in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					rewrite HnewBFirstFrees0PDT in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
					rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
					destruct (beqAddr (firstfreeslot pd1entry) nullAddr) eqn:HfirstfreeNull ; try(exfalso ; congruence).
					(* firstfreeslot p <> NULL *)
					(* if first free of other PD is NOT NULL,
					then newB can't be in the two lists at s0 because of Disjoint -> False *)
					subst listoption2. subst listoption1.
					unfold Lib.disjoint in HDisjoints0.
					specialize(HDisjoints0 newBlockEntryAddr).
					destruct (HDisjoints0).
					* induction (maxIdx+1). (* false induction because of fixpoint constraints *)
						** (* N=0 -> NotWellFormed *)
								cbn in *.
								congruence.
						** (* N>0 *)
								clear IHn.
								simpl. rewrite HlookupnewBs0.
								assert(HcurrNb : currnbfreeslots = nbfreeslots pdentry).
								{ unfold pdentryNbFreeSlots in *. rewrite Hpdinsertions0 in *. intuition. }
								rewrite <- HcurrNb in *.
								destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred ; try(exfalso ; congruence).
								rewrite <- HcurrNb in *. rewrite Hpred. cbn. intuition.
					* intuition.
}
	fold s1. fold s2. fold s3. fold s4. fold s5. fold s6.
	set (s7 := {| currentPartition := currentPartition ?s6; memory := _ |}).
	simpl in s5. simpl in s6.
	assert(Hfreeslotss7 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd1entry) s7 (nbfreeslots pd1entry) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd1entry) s6 (nbfreeslots pd1entry)).
	{
		(* DUP *)
				apply getFreeSlotsListRecEqBE ; intuition.
				---	(* Lists are disjoint at s0, so newB <> firstfreeslot p *)
							unfold getFreeSlotsList in Hoptionlist1s0.
							unfold getFreeSlotsList in Hoptionlist2s0.
							rewrite Hpdinsertions0 in *.
							assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
							{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
							assert(HnewBFirstFrees0P : firstfreeslot pd1entry = newBlockEntryAddr) by intuition.
							rewrite HnewBFirstFrees0PDT in *.
							rewrite HnewBFirstFrees0P in *.
							destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
								rewrite FreeSlotsListRec_unroll in Hoptionlist1s0.
								rewrite FreeSlotsListRec_unroll in Hoptionlist2s0.
								unfold getFreeSlotsListAux in *.
								induction (maxIdx+1). (* false induction because of fixpoint constraints *)
								** (* N=0 -> NotWellFormed *)
									rewrite Hoptionlist1s0 in *.
									cbn in Hwellformed1s0.
									congruence.
								** (* N>0 *)
									clear IHn.
									cbn in *.
									rewrite HlookupnewBs0 in *.
									destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred1 ; try(exfalso ; congruence).
									*** destruct (StateLib.Index.pred (nbfreeslots pd1entry)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
											rewrite Hoptionlist1s0 in *.
											cbn in *.
											unfold Lib.disjoint in HDisjoints0.
											specialize(HDisjoints0 newBlockEntryAddr).
											simpl in HDisjoints0.
											intuition.
									*** rewrite Hoptionlist1s0 in *.
											cbn in Hwellformed1s0.
											exfalso ; congruence.
			--- unfold isBE. unfold s7. cbn.
					destruct (beqAddr pdinsertion newBlockEntryAddr) ; try(exfalso ; congruence).
					rewrite beqAddrTrue.
					cbn.
					repeat rewrite removeDupIdentity ; intuition.
			--- subst listoption2.
					rewrite <- Hfreeslotss1 in *. rewrite <- Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *.
					rewrite <- Hfreeslotss5 in *. rewrite <- Hfreeslotss6 in *. intuition.
			--- assert(H_NoDups0 : NoDupInFreeSlotsList s0)
							by (unfold consistency in * ; intuition).
					unfold NoDupInFreeSlotsList in *.
					specialize (H_NoDups0 pd1 pd1entry Hlookuppd1s0).
					destruct H_NoDups0 as [optionlist2 (Hoptionlist2 & HwellFormed2' & HNoDup2)].
					unfold getFreeSlotsList in Hoptionlist2.
					rewrite Hlookuppd1s0 in *. rewrite Hpd1Null in *.
					subst optionlist2. subst listoption2.
					rewrite Hfreeslotss1 in *. rewrite Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *.
					rewrite <- Hfreeslotss5 in *. rewrite <- Hfreeslotss6 in *. intuition.
			--- rewrite <- Hfreeslotss6 in *. rewrite <- Hfreeslotss5 in *.
					rewrite <- Hfreeslotss4 in *. rewrite <- Hfreeslotss3 in *.
					rewrite Hfreeslotss2 in *. rewrite Hfreeslotss1 in *.
					(* newB is in freeslots list of pdinsertion, so can't be in other list
							because of Disjoint *)
					(* DUP from previous step *)
					unfold getFreeSlotsList in Hoptionlist1s0.
					unfold getFreeSlotsList in Hoptionlist2s0.
					rewrite Hpdinsertions0 in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					rewrite HnewBFirstFrees0PDT in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
					rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
					destruct (beqAddr (firstfreeslot pd1entry) nullAddr) eqn:HfirstfreeNull ; try(exfalso ; congruence).
					(* firstfreeslot p <> NULL *)
					(* if first free of other PD is NOT NULL,
					then newB can't be in the two lists at s0 because of Disjoint -> False *)
					subst listoption2. subst listoption1.
					unfold Lib.disjoint in HDisjoints0.
					specialize(HDisjoints0 newBlockEntryAddr).
					destruct (HDisjoints0).
					* induction (maxIdx+1). (* false induction because of fixpoint constraints *)
						** (* N=0 -> NotWellFormed *)
								cbn in *.
								congruence.
						** (* N>0 *)
								clear IHn.
								simpl. rewrite HlookupnewBs0.
								assert(HcurrNb : currnbfreeslots = nbfreeslots pdentry).
								{ unfold pdentryNbFreeSlots in *. rewrite Hpdinsertions0 in *. intuition. }
								rewrite <- HcurrNb in *.
								destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred ; try(exfalso ; congruence).
								rewrite <- HcurrNb in *. rewrite Hpred. cbn. intuition.
					* intuition.
}
	fold s1. fold s2. fold s3. fold s4. fold s5. fold s6. fold s7.
	set (s8 := {| currentPartition := currentPartition ?s7; memory := _ |}).
	simpl in s7.
	assert(Hfreeslotss8 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd1entry) s8 (nbfreeslots pd1entry) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd1entry) s7 (nbfreeslots pd1entry)).
	{
		(* DUP *)
				apply getFreeSlotsListRecEqBE ; intuition.
				---	(* Lists are disjoint at s0, so newB <> firstfreeslot p *)
							unfold getFreeSlotsList in Hoptionlist1s0.
							unfold getFreeSlotsList in Hoptionlist2s0.
							rewrite Hpdinsertions0 in *.
							assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
							{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
							assert(HnewBFirstFrees0P : firstfreeslot pd1entry = newBlockEntryAddr) by intuition.
							rewrite HnewBFirstFrees0PDT in *.
							rewrite HnewBFirstFrees0P in *.
							destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
								rewrite FreeSlotsListRec_unroll in Hoptionlist1s0.
								rewrite FreeSlotsListRec_unroll in Hoptionlist2s0.
								unfold getFreeSlotsListAux in *.
								induction (maxIdx+1). (* false induction because of fixpoint constraints *)
								** (* N=0 -> NotWellFormed *)
									rewrite Hoptionlist1s0 in *.
									cbn in Hwellformed1s0.
									congruence.
								** (* N>0 *)
									clear IHn.
									cbn in *.
									rewrite HlookupnewBs0 in *.
									destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred1 ; try(exfalso ; congruence).
									*** destruct (StateLib.Index.pred (nbfreeslots pd1entry)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
											rewrite Hoptionlist1s0 in *.
											cbn in *.
											unfold Lib.disjoint in HDisjoints0.
											specialize(HDisjoints0 newBlockEntryAddr).
											simpl in HDisjoints0.
											intuition.
									*** rewrite Hoptionlist1s0 in *.
											cbn in Hwellformed1s0.
											exfalso ; congruence.
			--- unfold isBE. unfold s8. cbn.
					destruct (beqAddr pdinsertion newBlockEntryAddr) ; try(exfalso ; congruence).
					rewrite beqAddrTrue.
					cbn.
					repeat rewrite removeDupIdentity ; intuition.
			--- subst listoption2.
					rewrite <- Hfreeslotss1 in *. rewrite <- Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *.
					rewrite <- Hfreeslotss5 in *. rewrite <- Hfreeslotss6 in *.
					rewrite <- Hfreeslotss7 in *. intuition.
			--- assert(H_NoDups0 : NoDupInFreeSlotsList s0)
							by (unfold consistency in * ; intuition).
					unfold NoDupInFreeSlotsList in *.
					specialize (H_NoDups0 pd1 pd1entry Hlookuppd1s0).
					destruct H_NoDups0 as [optionlist2 (Hoptionlist2 & HwellFormed2' & HNoDup2)].
					unfold getFreeSlotsList in Hoptionlist2.
					rewrite Hlookuppd1s0 in *. rewrite Hpd1Null in *.
					subst optionlist2. subst listoption2.
					rewrite Hfreeslotss1 in *. rewrite Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *.
					rewrite <- Hfreeslotss5 in *. rewrite <- Hfreeslotss6 in *.
					rewrite <- Hfreeslotss7 in *. intuition.
			--- rewrite <- Hfreeslotss7 in *.
					rewrite <- Hfreeslotss6 in *. rewrite <- Hfreeslotss5 in *.
					rewrite <- Hfreeslotss4 in *. rewrite <- Hfreeslotss3 in *.
					rewrite Hfreeslotss2 in *. rewrite Hfreeslotss1 in *.
					(* newB is in freeslots list of pdinsertion, so can't be in other list
							because of Disjoint *)
					(* DUP from previous step *)
					unfold getFreeSlotsList in Hoptionlist1s0.
					unfold getFreeSlotsList in Hoptionlist2s0.
					rewrite Hpdinsertions0 in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					rewrite HnewBFirstFrees0PDT in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
					rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
					destruct (beqAddr (firstfreeslot pd1entry) nullAddr) eqn:HfirstfreeNull ; try(exfalso ; congruence).
					(* firstfreeslot p <> NULL *)
					(* if first free of other PD is NOT NULL,
					then newB can't be in the two lists at s0 because of Disjoint -> False *)
					subst listoption2. subst listoption1.
					unfold Lib.disjoint in HDisjoints0.
					specialize(HDisjoints0 newBlockEntryAddr).
					destruct (HDisjoints0).
					* induction (maxIdx+1). (* false induction because of fixpoint constraints *)
						** (* N=0 -> NotWellFormed *)
								cbn in *.
								congruence.
						** (* N>0 *)
								clear IHn.
								simpl. rewrite HlookupnewBs0.
								assert(HcurrNb : currnbfreeslots = nbfreeslots pdentry).
								{ unfold pdentryNbFreeSlots in *. rewrite Hpdinsertions0 in *. intuition. }
								rewrite <- HcurrNb in *.
								destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred ; try(exfalso ; congruence).
								rewrite <- HcurrNb in *. rewrite Hpred. cbn. intuition.
					* intuition.
}
	fold s1. fold s2. fold s3. fold s4. fold s5. fold s6. fold s7. fold s8.
	set (s9 := {| currentPartition := currentPartition ?s8; memory := _ |}).
	simpl in s7.
	assert(Hfreeslotss9 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd1entry) s9 (nbfreeslots pd1entry) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd1entry) s8 (nbfreeslots pd1entry)).
	{
		(* DUP *)
				apply getFreeSlotsListRecEqBE ; intuition.
				---	(* Lists are disjoint at s0, so newB <> firstfreeslot p *)
							unfold getFreeSlotsList in Hoptionlist1s0.
							unfold getFreeSlotsList in Hoptionlist2s0.
							rewrite Hpdinsertions0 in *.
							assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
							{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
							assert(HnewBFirstFrees0P : firstfreeslot pd1entry = newBlockEntryAddr) by intuition.
							rewrite HnewBFirstFrees0PDT in *.
							rewrite HnewBFirstFrees0P in *.
							destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
								rewrite FreeSlotsListRec_unroll in Hoptionlist1s0.
								rewrite FreeSlotsListRec_unroll in Hoptionlist2s0.
								unfold getFreeSlotsListAux in *.
								induction (maxIdx+1). (* false induction because of fixpoint constraints *)
								** (* N=0 -> NotWellFormed *)
									rewrite Hoptionlist1s0 in *.
									cbn in Hwellformed1s0.
									congruence.
								** (* N>0 *)
									clear IHn.
									cbn in *.
									rewrite HlookupnewBs0 in *.
									destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred1 ; try(exfalso ; congruence).
									*** destruct (StateLib.Index.pred (nbfreeslots pd1entry)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
											rewrite Hoptionlist1s0 in *.
											cbn in *.
											unfold Lib.disjoint in HDisjoints0.
											specialize(HDisjoints0 newBlockEntryAddr).
											simpl in HDisjoints0.
											intuition.
									*** rewrite Hoptionlist1s0 in *.
											cbn in Hwellformed1s0.
											exfalso ; congruence.
			--- unfold isBE. unfold s9. cbn.
					destruct (beqAddr pdinsertion newBlockEntryAddr) ; try(exfalso ; congruence).
					rewrite beqAddrTrue.
					cbn.
					repeat rewrite removeDupIdentity ; intuition.
			--- subst listoption2.
					rewrite <- Hfreeslotss1 in *. rewrite <- Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *.
					rewrite <- Hfreeslotss5 in *. rewrite <- Hfreeslotss6 in *.
					rewrite <- Hfreeslotss7 in *. rewrite <- Hfreeslotss8 in *. intuition.
			--- assert(H_NoDups0 : NoDupInFreeSlotsList s0)
							by (unfold consistency in * ; intuition).
					unfold NoDupInFreeSlotsList in *.
					specialize (H_NoDups0 pd1 pd1entry Hlookuppd1s0).
					destruct H_NoDups0 as [optionlist2 (Hoptionlist2 & HwellFormed2' & HNoDup2)].
					unfold getFreeSlotsList in Hoptionlist2.
					rewrite Hlookuppd1s0 in *. rewrite Hpd1Null in *.
					subst optionlist2. subst listoption2.
					rewrite Hfreeslotss1 in *. rewrite Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *.
					rewrite <- Hfreeslotss5 in *. rewrite <- Hfreeslotss6 in *.
					rewrite <- Hfreeslotss7 in *. rewrite <- Hfreeslotss8 in *. intuition.
			--- rewrite <- Hfreeslotss8 in *. rewrite <- Hfreeslotss7 in *.
					rewrite <- Hfreeslotss6 in *. rewrite <- Hfreeslotss5 in *.
					rewrite <- Hfreeslotss4 in *. rewrite <- Hfreeslotss3 in *.
					rewrite Hfreeslotss2 in *. rewrite Hfreeslotss1 in *.
					(* newB is in freeslots list of pdinsertion, so can't be in other list
							because of Disjoint *)
					(* DUP from previous step *)
					unfold getFreeSlotsList in Hoptionlist1s0.
					unfold getFreeSlotsList in Hoptionlist2s0.
					rewrite Hpdinsertions0 in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					rewrite HnewBFirstFrees0PDT in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
					rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
					destruct (beqAddr (firstfreeslot pd1entry) nullAddr) eqn:HfirstfreeNull ; try(exfalso ; congruence).
					(* firstfreeslot p <> NULL *)
					(* if first free of other PD is NOT NULL,
					then newB can't be in the two lists at s0 because of Disjoint -> False *)
					subst listoption2. subst listoption1.
					unfold Lib.disjoint in HDisjoints0.
					specialize(HDisjoints0 newBlockEntryAddr).
					destruct (HDisjoints0).
					* induction (maxIdx+1). (* false induction because of fixpoint constraints *)
						** (* N=0 -> NotWellFormed *)
								cbn in *.
								congruence.
						** (* N>0 *)
								clear IHn.
								simpl. rewrite HlookupnewBs0.
								assert(HcurrNb : currnbfreeslots = nbfreeslots pdentry).
								{ unfold pdentryNbFreeSlots in *. rewrite Hpdinsertions0 in *. intuition. }
								rewrite <- HcurrNb in *.
								destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred ; try(exfalso ; congruence).
								rewrite <- HcurrNb in *. rewrite Hpred. cbn. intuition.
					* intuition.
}
	fold s1. fold s2. fold s3. fold s4. fold s5. fold s6. fold s7. fold s8. fold s9.
	set (s10 := {| currentPartition := currentPartition ?s9; memory := _ |}).
	simpl in s8. simpl in s9.
	assert(Hfreeslotss10 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd1entry) s10 (nbfreeslots pd1entry) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd1entry) s9 (nbfreeslots pd1entry)).
	{			assert(HSCEs9 : isSCE sceaddr s9).
				{ unfold isSCE. unfold s9. cbn. rewrite beqAddrTrue.
					destruct (beqAddr newBlockEntryAddr sceaddr) eqn:Hf ; try(exfalso ; congruence).
					rewrite <- beqAddrFalse in *.
					repeat rewrite removeDupIdentity ; intuition.
					destruct (beqAddr pdinsertion newBlockEntryAddr) eqn:Hff ; try(exfalso ; congruence).
					rewrite <- DependentTypeLemmas.beqAddrTrue in Hff. congruence.
					cbn.
					destruct (beqAddr pdinsertion sceaddr) eqn:Hfff ; try(exfalso ; congruence).
					rewrite <- DependentTypeLemmas.beqAddrTrue in Hfff. congruence.
					rewrite beqAddrTrue.
					rewrite <- beqAddrFalse in *.
					repeat rewrite removeDupIdentity ; intuition.
				}
				apply getFreeSlotsListRecEqSCE.
				--- 	intro Hfirstsceeq.
						assert(HFirstFreeSlotPointerIsBEAndFreeSlots0 : FirstFreeSlotPointerIsBEAndFreeSlot s0)
							by (unfold consistency in * ; intuition).
						unfold FirstFreeSlotPointerIsBEAndFreeSlot in *.
						specialize (HFirstFreeSlotPointerIsBEAndFreeSlots0 pd1 pd1entry Hlookuppd1s0).
						destruct HFirstFreeSlotPointerIsBEAndFreeSlots0.
						---- intro HfirstfreeNull.
								assert(HnullAddrExistss0 : nullAddrExists s0)
									by (unfold consistency in * ; intuition).
								unfold nullAddrExists in *.
								unfold isSCE in *.
								unfold isPADDR in *.
								rewrite HfirstfreeNull in *. rewrite <- Hfirstsceeq in *.
								destruct (lookup nullAddr (memory s0) beqAddr) ; try(exfalso ; congruence).
								destruct v ; try(exfalso ; congruence).
						---- rewrite Hfirstsceeq in *.
								unfold isSCE in *.
								unfold isBE in *.
								destruct (lookup sceaddr (memory s0) beqAddr) ; try (exfalso ; congruence).
								destruct v ; try(exfalso ; congruence).
				--- unfold isBE. unfold isSCE in HSCEs9.
						destruct (lookup sceaddr (memory s9) beqAddr) eqn:Hlookupsces9 ; try(exfalso ; congruence).
						destruct v ; try(exfalso ; congruence).
						intuition.
				--- unfold isPADDR. unfold isSCE in HSCEs9.
						destruct (lookup sceaddr (memory s9) beqAddr) eqn:Hlookupsces9 ; try(exfalso ; congruence).
						destruct v ; try(exfalso ; congruence).
						intuition.
	}
	fold s1. fold s2. fold s3. fold s4. fold s5. fold s6. fold s7. fold s8. fold s9.
	fold s10.

	intuition.
	assert(HcurrLtmaxIdx : nbfreeslots pd1entry <= maxIdx).
	{ intuition. apply IdxLtMaxIdx. }
	lia.
}
									destruct Hfreeslotspd1Eq as [s1 (s2 & (s3 & (s4 & (s5 & (s6 & (s7 & (s8 & (s9 & (s10 &
																		(n1 & (nbleft & (Hnbleft & Hstates))))))))))))].
									assert(HsEq : s10 = s).
									{ intuition. subst s1. subst s2. subst s3. subst s4. subst s5. subst s6.
										subst s7. subst s8. subst s9. subst s10.
										rewrite Hs. f_equal.
									}
									rewrite HsEq in *.
									assert(HfreeslotsEq : getFreeSlotsListRec n1 (firstfreeslot pd1entry) s (nbfreeslots pd1entry) =
																				getFreeSlotsListRec (maxIdx+1) (firstfreeslot pd1entry) s0 (nbfreeslots pd1entry)).
									{
										intuition.
										subst nbleft.
										(* rewrite all previous getFreeSlotsListRec equalities *)
										rewrite <- H33. rewrite <- H36. rewrite <- H38. rewrite <- H40.
										rewrite <- H42. rewrite <- H44. rewrite <- H46. rewrite <- H48.
										rewrite <- H50. rewrite <- H53.
										reflexivity.
									}
									assert (HfreeslotsEqn1 : getFreeSlotsListRec n1 (firstfreeslot pd1entry) s (nbfreeslots pd1entry)
																						= getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd1entry) s (nbfreeslots pd1entry)).
									{ eapply getFreeSlotsListRecEqN ; intuition.
										subst nbleft. lia.
										assert (HnbLtmaxIdx : nbfreeslots pd1entry <= maxIdx) by apply IdxLtMaxIdx.
										lia.
									}
									unfold getFreeSlotsList in *.
									rewrite Hlookuppd1Eq in *.
									rewrite Hpdinsertions0 in *. rewrite Hpdinsertions.
									rewrite <- HfreeslotsEqn1. rewrite HfreeslotsEq.
									rewrite HnewFirstFree.
									rewrite <- HnewB in *.
									destruct(beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
									rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
									destruct(beqAddr (firstfreeslot pd1entry) nullAddr) eqn:Hff ; try(exfalso ; congruence).
									destruct H31 as [Hoptionlists (olds & (n0' & (n1' & (n2' & (nbleft' & Hfreeslotsolds')))))].
									exists listoption2. exists Hoptionlists. (* inverse as we treat pd2 and not pd1 *)
									destruct (beqAddr newFirstFreeSlotAddr nullAddr) eqn:beqfirstnull; try(exfalso ; congruence).
									-------- (* newFirstFreeSlotAddr = nullAddr *)
													rewrite <- DependentTypeLemmas.beqAddrTrue in beqfirstnull.
													rewrite beqfirstnull in *.
													assert(HoptionlistsNull : Hoptionlists = nil).
													{
														intuition.
														assert(Hoption :  Hoptionlists = getFreeSlotsListRec n0' nullAddr s0 nbleft') by intuition.
														rewrite FreeSlotsListRec_unroll in Hoption.
														unfold getFreeSlotsListAux in Hoption.
														destruct n0'.
														rewrite Hoption in *. cbn in *. congruence.
														destruct (StateLib.Index.ltb nbleft' zero).
														rewrite Hoption in *. cbn in *. congruence.
														assert(HNullAddrExistss0 : nullAddrExists s0)
																by (unfold consistency in * ; intuition).
														unfold nullAddrExists in *.
														unfold isPADDR in *.
														destruct (lookup nullAddr (memory s0) beqAddr) ; try(exfalso ; congruence).
														destruct v ; try(exfalso ; congruence).
														rewrite beqAddrTrue in Hoption.
														rewrite Hoption in *. cbn in *. congruence.
													}
													intuition.
													rewrite HoptionlistsNull in *.
													unfold Lib.disjoint. intros. intuition.
									-------- (* newFirstFreeSlotAddr <> nullAddr *)
													assert(HoptionlistEq : Hoptionlists = getFreeSlotsListRec (maxIdx + 1) newFirstFreeSlotAddr s (nbfreeslots pdentry1)).
													{ subst pdentry1. (* pdentry1 *) cbn.
													assert(HpredNbLeftEq : predCurrentNbFreeSlots = nbleft').
													{ intuition. subst nbleft'. unfold StateLib.Index.pred in *.
														destruct (gt_dec currnbfreeslots 0) ; intuition.
														inversion H1. (* Some ... = Some predCurrentNbFreeSlots *)
														unfold CIndex.
														assert(HnbLtmaxIdx : currnbfreeslots - 1 < maxIdx).
														{ 
															assert(HcurrLtmaxIdx : currnbfreeslots <= maxIdx).
															{ intuition. apply IdxLtMaxIdx. }
															lia.
														}
														destruct (le_dec (currnbfreeslots - 1) maxIdx) ; intuition.
														f_equal. apply proof_irrelevance.
													}
													rewrite HpredNbLeftEq.
													assert(HoptionlistEq : getFreeSlotsListRec n2' newFirstFreeSlotAddr s nbleft' = Hoptionlists) by intuition.
													rewrite <- HoptionlistEq. (* n2 s = Hoptionlist *)
													eapply getFreeSlotsListRecEqN ; intuition.
													}
													(* we know listoption2 and Hoptionlist haven't changed
															and as Hoptionlist is a subset of listoption1
														and from the beginning they were disjoint, so still disjoint  *)
													assert(HIncl : incl (filterOption Hoptionlists) (filterOption listoption1)).
													{
														rewrite FreeSlotsListRec_unroll in Hoptionlist1s0.
														unfold getFreeSlotsListAux in Hoptionlist1s0.
														assert(HMaxIdxNext : maxIdx + 1 = S maxIdx).
														{ lia. }
														rewrite HMaxIdxNext in *.
														assert(Hnbfreeslots : (nbfreeslots pdentry) = currnbfreeslots).
														{ unfold pdentryNbFreeSlots in *. rewrite Hpdinsertions0 in *. intuition. }
														rewrite Hnbfreeslots in *.
														destruct (StateLib.Index.ltb currnbfreeslots zero) eqn:Hltb ; try(exfalso ; congruence).
														* unfold StateLib.Index.ltb in Hltb.
															apply PeanoNat.Nat.ltb_lt in Hltb.
															contradict Hltb. apply PeanoNat.Nat.lt_asymm. intuition.
														* rewrite HlookupnewBs0 in *.
															destruct (StateLib.Index.pred currnbfreeslots) eqn:Hpred ; try(exfalso ; congruence).
															assert(Hoptionlists0 : Hoptionlists =
                												getFreeSlotsListRec n0' newFirstFreeSlotAddr s0 nbleft') by intuition.
															rewrite Hoptionlists0.
															assert(HnewBEndIsNewFirst : (endAddr (blockrange bentry)) = newFirstFreeSlotAddr).
															{ unfold bentryEndAddr in *. rewrite HlookupnewBs0 in *. intuition. }
															rewrite HnewBEndIsNewFirst in *.
															assert(HnbLtmaxIdx : currnbfreeslots - 1 < maxIdx).
															{
																	unfold pdentryNbFreeSlots in *. rewrite Hpdinsertions0 in *.
																	destruct currnbfreeslots.
																	+ simpl. destruct i0.
																		* simpl. apply maxIdxNotZero.
																		* cbn. rewrite PeanoNat.Nat.sub_0_r. intuition.
															}
															assert((CIndex (currnbfreeslots - 1)) = i).
															{ unfold CIndex.
																destruct (le_dec (currnbfreeslots - 1) maxIdx) ; simpl in * ; intuition ; try(exfalso ; congruence).
																	unfold StateLib.Index.pred in *.
																	destruct (gt_dec currnbfreeslots 0) ; try(exfalso ; congruence).
																	inversion Hpred. f_equal. apply proof_irrelevance.
															}
															unfold pdentryNbFreeSlots in *. rewrite H5 in *.
															rewrite H8 in *.
															assert(i < maxIdx).
															{	unfold StateLib.Index.pred in *.
																destruct (gt_dec currnbfreeslots 0) ; try(exfalso ; congruence).
																inversion Hpred. simpl. intuition.
															}
															assert(HEq : getFreeSlotsListRec maxIdx newFirstFreeSlotAddr s0 i =
																							getFreeSlotsListRec (maxIdx+1) newFirstFreeSlotAddr s0 i).
															{
																eapply getFreeSlotsListRecEqN ; intuition.
															}
															rewrite HEq in *.
															subst nbleft. subst listoption1.
															assert(HnbleftEq': nbleft' = i).
															{ intuition. subst nbleft'. intuition. }
															rewrite HnbleftEq' in *.
															assert(HEq' : getFreeSlotsListRec n0' newFirstFreeSlotAddr s0 i =
																									getFreeSlotsListRec (maxIdx + 1) newFirstFreeSlotAddr s0 i).
															{
																eapply getFreeSlotsListRecEqN ; intuition.
																{ lia. }
															}
															rewrite HEq'. intuition.
															cbn. intuition.
													}
													intuition. apply Lib.disjointPermut.
													eapply Lib.inclDisjoint.
													apply HDisjoints0. intuition. intuition.

										------ (* 4) pdinsertion <> pd2 *)
														(* show strict equality of listoption1 at s and s0
																and listoption2 at s and s0 because no list changed 
																	as only pdinsertion's free slots list changed *)
														(* DUP *)
														(* show list equality between s0 and s*)
														(* similarly, we must prove optionfreeslotslist1 
															and optionfreeslotslist2 are strictly
															the same at s than at s0 by recomputing each
															intermediate steps and check at that time *)
														assert(Hlookuppd2Eq : lookup pd2 (memory s) beqAddr = lookup pd2 (memory s0) beqAddr).
														{
															rewrite Hs.
															cbn. rewrite beqAddrTrue.
															rewrite beqscepd2.
															assert(HnewBsceNotEq : beqAddr newBlockEntryAddr sceaddr = false) by intuition.
															rewrite HnewBsceNotEq. (*newBlock <> sce *)
															cbn.
															rewrite beqnewpd2. (*pd2 <> newblock*)
															rewrite beqAddrTrue.
															rewrite <- beqAddrFalse in *.
															repeat rewrite removeDupIdentity ; intuition.
															destruct (beqAddr pdinsertion newBlockEntryAddr) eqn:Hf ; try(exfalso ; congruence).
															rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
															cbn.
															destruct (beqAddr pdinsertion pd2) eqn:Hff ; try(exfalso ; congruence).
															rewrite <- DependentTypeLemmas.beqAddrTrue in Hff. congruence.
															rewrite <- beqAddrFalse in *.
															repeat rewrite removeDupIdentity ; intuition.
														}
														assert(HPDTpd2Eq : isPDT pd2 s = isPDT pd2 s0).
														{ unfold isPDT. rewrite Hlookuppd2Eq. intuition. }
														assert(HPDTpd2s0 : isPDT pd2 s0) by (rewrite HPDTpd2Eq in * ; assumption).
															(* DUP of previous steps to show strict equality of listoption2
																at s and s0 *)
														specialize (Hcons0 pd1 pd2 HPDTpd1s0 HPDTpd2s0 Hpd1pd2NotEq).
														destruct Hcons0 as [listoption1 (listoption2 & (Hoptionlist1s0 & (Hwellformed1s0 & (Hoptionlist2s0 & (Hwellformed2s0 & HDisjoints0)))))].
														assert(Hpdpd1NotEq : pdinsertion <> pd1) by (rewrite <- beqAddrFalse in * ; intuition).
														assert(Hpdpd2NotEq : pdinsertion <> pd2) by (rewrite <- beqAddrFalse in * ; intuition).
														assert(HDisjointpdpd1s0 : DisjointFreeSlotsLists s0)
															by (unfold consistency in * ; intuition).
														unfold DisjointFreeSlotsLists in *.
														specialize (HDisjointpdpd1s0 pdinsertion pd1 HPDTs0 HPDTpd1s0 Hpdpd1NotEq).
														assert(HDisjointpdpd2s0 : DisjointFreeSlotsLists s0)
															by (unfold consistency in * ; intuition).
														unfold DisjointFreeSlotsLists in *.
														specialize (HDisjointpdpd2s0 pdinsertion pd2 HPDTs0 HPDTpd2s0 Hpdpd2NotEq).

														(* Show equality between listoption1 at s and listoption1 at s0 *)
														unfold getFreeSlotsList in Hoptionlist1s0.
														apply isPDTLookupEq in HPDTpd1s0. destruct HPDTpd1s0 as [pd1entry Hlookuppd1s0].
														rewrite Hlookuppd1s0 in *.
														destruct (beqAddr (firstfreeslot pd1entry) nullAddr) eqn:Hpd1Null ; try(exfalso ; congruence).
														------- (* listoption1 = NIL *)
																	exists listoption1. exists listoption2.
																	assert(Hlistoption1s : getFreeSlotsList pd1 s = nil).
																	{
																		unfold getFreeSlotsList.
																		rewrite Hlookuppd1Eq. rewrite Hpd1Null. reflexivity.
																	}
																	rewrite Hlistoption1s in *. intuition.
																	unfold getFreeSlotsList in *. rewrite Hlookuppd2Eq in *.
																	apply isPDTLookupEq in HPDTpd2s0. destruct HPDTpd2s0 as [pd2entry Hlookuppd2s0].
																	rewrite Hlookuppd2s0 in *.
																	destruct (beqAddr (firstfreeslot pd2entry) nullAddr) eqn:beqfirstnull; try(exfalso ; congruence).
																	-------- (* (firstfreeslot pd2entry) = nullAddr *)
																					intuition.
																	-------- (* (firstfreeslot pd2entry) <> nullAddr *)
																		(* show equality between listoption2 at s and s0
																				-> if listoption2 has NOT changed, they are
																				still disjoint at s because lisoption1 is NIL *)
assert(Hfreeslotspd2Eq : exists s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 n1 nbleft,
nbleft = (nbfreeslots pd2entry) /\
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
                     vidtBlock := vidtBlock pdentry
                   |}) (memory s0) beqAddr |} /\
getFreeSlotsListRec n1 (firstfreeslot pd2entry) s1 nbleft =
getFreeSlotsListRec (maxIdx+1) (firstfreeslot pd2entry) s0 nbleft
			 /\
	n1 <= maxIdx+1 /\ nbleft < n1
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
		                vidtBlock := vidtBlock pdentry0
		              |}
                 ) (memory s1) beqAddr |} /\
getFreeSlotsListRec n1 (firstfreeslot pd2entry) s2 nbleft =
			getFreeSlotsListRec n1 (firstfreeslot pd2entry) s1 nbleft
/\ s3 = {|
     currentPartition := currentPartition s2;
     memory := add newBlockEntryAddr
	            (BE
	               (CBlockEntry (read bentry) 
	                  (write bentry) (exec bentry) 
	                  (present bentry) (accessible bentry)
	                  (blockindex bentry)
	                  (CBlock startaddr (endAddr (blockrange bentry))))
                 ) (memory s2) beqAddr |} /\
getFreeSlotsListRec n1 (firstfreeslot pd2entry) s3 nbleft =
			getFreeSlotsListRec n1 (firstfreeslot pd2entry) s2 nbleft
/\ s4 = {|
     currentPartition := currentPartition s3;
     memory := add newBlockEntryAddr
               (BE
                  (CBlockEntry (read bentry0) 
                     (write bentry0) (exec bentry0) 
                     (present bentry0) (accessible bentry0)
                     (blockindex bentry0)
                     (CBlock (startAddr (blockrange bentry0)) endaddr))
                 ) (memory s3) beqAddr |} /\
getFreeSlotsListRec n1 (firstfreeslot pd2entry) s4 nbleft =
			getFreeSlotsListRec n1 (firstfreeslot pd2entry) s3 nbleft
/\ s5 = {|
     currentPartition := currentPartition s4;
     memory := add newBlockEntryAddr
              (BE
                 (CBlockEntry (read bentry1) 
                    (write bentry1) (exec bentry1) 
                    (present bentry1) true (blockindex bentry1)
                    (blockrange bentry1))
                 ) (memory s4) beqAddr |} /\
getFreeSlotsListRec n1 (firstfreeslot pd2entry) s5 nbleft =
			getFreeSlotsListRec n1 (firstfreeslot pd2entry) s4 nbleft
/\ s6 = {|
     currentPartition := currentPartition s5;
     memory := add newBlockEntryAddr
               (BE
                  (CBlockEntry (read bentry2) (write bentry2) 
                     (exec bentry2) true (accessible bentry2)
                     (blockindex bentry2) (blockrange bentry2))
                 ) (memory s5) beqAddr |} /\
getFreeSlotsListRec n1 (firstfreeslot pd2entry) s6 nbleft =
			getFreeSlotsListRec n1 (firstfreeslot pd2entry) s5 nbleft
/\ s7 = {|
     currentPartition := currentPartition s6;
     memory := add newBlockEntryAddr
              (BE
                 (CBlockEntry r (write bentry3) (exec bentry3)
                    (present bentry3) (accessible bentry3) 
                    (blockindex bentry3) (blockrange bentry3))
                 ) (memory s6) beqAddr |} /\
getFreeSlotsListRec n1 (firstfreeslot pd2entry) s7 nbleft =
			getFreeSlotsListRec n1 (firstfreeslot pd2entry) s6 nbleft
/\ s8 = {|
     currentPartition := currentPartition s7;
     memory := add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry4) w (exec bentry4) 
                       (present bentry4) (accessible bentry4) 
                       (blockindex bentry4) (blockrange bentry4))
                 ) (memory s7) beqAddr |} /\
getFreeSlotsListRec n1(firstfreeslot pd2entry) s8 nbleft =
			getFreeSlotsListRec n1 (firstfreeslot pd2entry) s7 nbleft
/\ s9 = {|
     currentPartition := currentPartition s8;
     memory := add newBlockEntryAddr
              (BE
                 (CBlockEntry (read bentry5) (write bentry5) e 
                    (present bentry5) (accessible bentry5) 
                    (blockindex bentry5) (blockrange bentry5))
                 ) (memory s8) beqAddr |} /\
getFreeSlotsListRec n1 (firstfreeslot pd2entry) s9 nbleft =
			getFreeSlotsListRec n1 (firstfreeslot pd2entry) s8 nbleft
/\ s10 = {|
     currentPartition := currentPartition s9;
     memory := add sceaddr 
								(SCE {| origin := origin; next := next scentry |}
                 ) (memory s9) beqAddr |} /\
getFreeSlotsListRec n1 (firstfreeslot pd2entry) s10 nbleft =
			getFreeSlotsListRec n1 (firstfreeslot pd2entry) s9 nbleft
).
{
	eexists ?[s1]. eexists ?[s2]. eexists ?[s3]. eexists ?[s4]. eexists ?[s5].
	eexists ?[s6]. eexists ?[s7]. eexists ?[s8]. eexists ?[s9].
	eexists ?[s10]. eexists ?[n1]. eexists.
	split. intuition.
	split. intuition.
	set (s1 := {| currentPartition := _ |}).
	(* prove outside *)
	assert(Hfreeslotss1 : getFreeSlotsListRec ?n1 (firstfreeslot pd2entry) s1 (nbfreeslots pd2entry) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s0 (nbfreeslots pd2entry)).
	{
		apply getFreeSlotsListRecEqPDT.
		-- 	intro Hfirstpdeq.
				assert(HFirstFreeSlotPointerIsBEAndFreeSlots0 : FirstFreeSlotPointerIsBEAndFreeSlot s0)
					by (unfold consistency in * ; intuition).
				unfold FirstFreeSlotPointerIsBEAndFreeSlot in *.
				specialize (HFirstFreeSlotPointerIsBEAndFreeSlots0 pd2 pd2entry Hlookuppd2s0).
				destruct HFirstFreeSlotPointerIsBEAndFreeSlots0.
				--- intro HfirstfreeNull.
						assert(HnullAddrExistss0 : nullAddrExists s0)
							by (unfold consistency in * ; intuition).
						unfold nullAddrExists in *.
						unfold isPADDR in *.
						rewrite HfirstfreeNull in *. rewrite <- Hfirstpdeq in *.
						destruct (lookup nullAddr (memory s0) beqAddr) ; try(exfalso ; congruence).
						destruct v ; try(exfalso ; congruence).
				--- rewrite Hfirstpdeq in *.
						unfold isBE in *.
						destruct (lookup pdinsertion (memory s0) beqAddr) ; try (exfalso ; congruence).
						destruct v ; try(exfalso ; congruence).
		-- unfold isBE. rewrite Hpdinsertions0. intuition.
		-- unfold isPADDR. rewrite Hpdinsertions0. intuition.
	}
	set (s2 := {| currentPartition := _ |}).
	assert(Hfreeslotss2 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s2 (nbfreeslots pd2entry) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s1 (nbfreeslots pd2entry)).
	{
				apply getFreeSlotsListRecEqPDT.
				--- 	intro Hfirstpdeq.
						assert(HFirstFreeSlotPointerIsBEAndFreeSlots0 : FirstFreeSlotPointerIsBEAndFreeSlot s0)
							by (unfold consistency in * ; intuition).
						unfold FirstFreeSlotPointerIsBEAndFreeSlot in *.
						specialize (HFirstFreeSlotPointerIsBEAndFreeSlots0 pd2 pd2entry Hlookuppd2s0).
						destruct HFirstFreeSlotPointerIsBEAndFreeSlots0.
						---- intro HfirstfreeNull.
								assert(HnullAddrExistss0 : nullAddrExists s0)
									by (unfold consistency in * ; intuition).
								unfold nullAddrExists in *.
								unfold isPADDR in *.
								rewrite HfirstfreeNull in *. rewrite <- Hfirstpdeq in *.
								destruct (lookup nullAddr (memory s0) beqAddr) ; try(exfalso ; congruence).
								destruct v ; try(exfalso ; congruence).
						---- rewrite Hfirstpdeq in *.
								unfold isBE in *.
								destruct (lookup pdinsertion (memory s0) beqAddr) ; try (exfalso ; congruence).
								destruct v ; try(exfalso ; congruence).
				--- unfold isBE. unfold s1. cbn. rewrite beqAddrTrue. intuition.
				--- unfold isPADDR. unfold s1. cbn. rewrite beqAddrTrue. intuition.
	}
	set (s3 := {| currentPartition := _ |}).
	assert(Hfreeslotss3 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s3 (nbfreeslots pd2entry) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s2 (nbfreeslots pd2entry)).
	{
				apply getFreeSlotsListRecEqBE ; intuition.
				---	(* Lists are disjoint at s0, so newB <> firstfreeslot pd2entry *)
							destruct HDisjointpdpd2s0 as [optionfreeslotslistpd (optionfreeslotslistpd2 & (Hoptionfreeslotslistpd & (Hwellformedpds0 & (Hoptionfreeslotslistpd2 & (Hwellformedpd2s0 & HDisjointpdpd2s0)))))].
							unfold getFreeSlotsList in Hoptionfreeslotslistpd.
							unfold getFreeSlotsList in Hoptionfreeslotslistpd2.
							rewrite Hpdinsertions0 in *.
							rewrite Hlookuppd1Eq in *.
							assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
							{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
							assert(HnewBFirstFrees0P : firstfreeslot pd2entry = newBlockEntryAddr) by intuition.
							rewrite HnewBFirstFrees0PDT in *.
							rewrite HnewBFirstFrees0P in *.
							destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
								rewrite FreeSlotsListRec_unroll in Hoptionfreeslotslistpd.
								rewrite FreeSlotsListRec_unroll in Hoptionfreeslotslistpd2.
								unfold getFreeSlotsListAux in *.
								induction (maxIdx+1). (* false induction because of fixpoint constraints *)
								** (* N=0 -> NotWellFormed *)
									rewrite Hoptionlist2s0 in *.
									cbn in Hwellformed2s0.
									congruence.
								** (* N>0 *)
									clear IHn.
									rewrite HlookupnewBs0 in *.
									destruct (StateLib.Index.ltb (nbfreeslots pdentry) zero) eqn:Hltb ; try(cbn in * ; congruence).
									destruct (StateLib.Index.ltb (nbfreeslots pd2entry) zero) eqn:Hltb' ; try(cbn in * ; congruence).
									destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred1 ; try(exfalso ; congruence).
									*** destruct (StateLib.Index.pred (nbfreeslots pd2entry)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
											**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd2.
														cbn in *.
														unfold Lib.disjoint in HDisjointpdpd2s0.
														specialize(HDisjointpdpd2s0 newBlockEntryAddr).
														simpl in HDisjointpdpd2s0.
														intuition.
											**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd2.
														cbn in *. congruence.
									*** destruct (StateLib.Index.pred (nbfreeslots pd2entry)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
											**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd2.
														cbn in *.
														unfold Lib.disjoint in HDisjointpdpd2s0.
														specialize(HDisjointpdpd2s0 newBlockEntryAddr).
														simpl in HDisjointpdpd2s0.
														intuition.
											**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd2.
														cbn in *. congruence.
			--- unfold isBE. unfold s3. cbn.
					destruct (beqAddr pdinsertion newBlockEntryAddr) ; try(exfalso ; congruence).
					rewrite beqAddrTrue.
					cbn.
					repeat rewrite removeDupIdentity ; intuition.
			--- subst listoption2.
					rewrite <- Hfreeslotss1 in *. rewrite <- Hfreeslotss2 in *. intuition.
			--- assert(H_NoDups0 : NoDupInFreeSlotsList s0)
							by (unfold consistency in * ; intuition).
					unfold NoDupInFreeSlotsList in *.
					specialize (H_NoDups0 pd2 pd2entry Hlookuppd2s0).
					destruct H_NoDups0 as [optionlist2 (Hoptionlist2 & HwellFormed2' & HNoDup2)].
					unfold getFreeSlotsList in Hoptionlist2.
					rewrite Hlookuppd2s0 in *.
					destruct (beqAddr (firstfreeslot pd2entry) nullAddr) eqn:Hpd2Null ; try(exfalso ; congruence).
					subst optionlist2. subst listoption2.
					rewrite Hfreeslotss1 in *. rewrite Hfreeslotss2 in *. intuition.
			--- rewrite Hfreeslotss2 in *. rewrite Hfreeslotss1 in *.
					(* newB is in freeslots list of pdinsertion, so can't be in other list
							because of Disjoint *)
					(* DUP from previous step *)
					destruct HDisjointpdpd2s0 as [optionfreeslotslistpd (optionfreeslotslistpd2 & (Hoptionfreeslotslistpd & (Hwellformedpds0 & (Hoptionfreeslotslistpd2 & (Hwellformedpd2s0 & HDisjointpdpd2s0)))))].
					unfold getFreeSlotsList in Hoptionfreeslotslistpd.
					unfold getFreeSlotsList in Hoptionfreeslotslistpd2.
					rewrite Hpdinsertions0 in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					rewrite HnewBFirstFrees0PDT in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
					rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
					destruct (beqAddr (firstfreeslot pd2entry) nullAddr) eqn:HfirstfreeNull ; try(exfalso ; congruence).
					(* firstfreeslot p <> NULL *)
					(* if first free of other PD is NOT NULL,
					then newB can't be in the two lists at s0 because of Disjoint -> False *)
					subst listoption2. subst listoption1.
					unfold Lib.disjoint in HDisjointpdpd2s0.
					specialize(HDisjointpdpd2s0 newBlockEntryAddr).
					destruct (HDisjointpdpd2s0).
					* subst optionfreeslotslistpd.
						rewrite FreeSlotsListRec_unroll.
						unfold getFreeSlotsListAux.
						assert(HmaxIdxNextEq :	maxIdx + 1 = S maxIdx) by apply MaxIdxNextEq.
						rewrite HmaxIdxNextEq.
						rewrite HlookupnewBs0.
						assert(HcurrNb : currnbfreeslots = nbfreeslots pdentry).
						{ unfold pdentryNbFreeSlots in *. rewrite Hpdinsertions0 in *. intuition. }
						rewrite <- HcurrNb in *.
						destruct (StateLib.Index.ltb currnbfreeslots zero) eqn:Hltb ; try(exfalso ; congruence).
						** unfold StateLib.Index.ltb in Hltb.
								apply PeanoNat.Nat.ltb_lt in Hltb.
								contradict Hltb. apply PeanoNat.Nat.lt_asymm. intuition.
						**	destruct (StateLib.Index.pred currnbfreeslots) eqn:Hpred ; try(exfalso ; congruence).
								cbn. intuition.
					* subst optionfreeslotslistpd2.
						intuition.
}
	set (s4 := {| currentPartition := currentPartition ?s3; memory := _ |}). simpl in s4. simpl in s3.
	assert(Hfreeslotss4 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s4 (nbfreeslots pd2entry) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s3 (nbfreeslots pd2entry)).
	{
		(* DUP *)
				apply getFreeSlotsListRecEqBE ; intuition.
				---	(* Lists are disjoint at s0, so newB <> firstfreeslot p *)
							destruct HDisjointpdpd2s0 as [optionfreeslotslistpd (optionfreeslotslistpd2 & (Hoptionfreeslotslistpd & (Hwellformedpds0 & (Hoptionfreeslotslistpd2 & (Hwellformedpd2s0 & HDisjointpdpd2s0)))))].
							unfold getFreeSlotsList in Hoptionfreeslotslistpd.
							unfold getFreeSlotsList in Hoptionfreeslotslistpd2.
							rewrite Hpdinsertions0 in *.
							rewrite Hlookuppd1Eq in *.
							assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
							{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
							assert(HnewBFirstFrees0P : firstfreeslot pd2entry = newBlockEntryAddr) by intuition.
							rewrite HnewBFirstFrees0PDT in *.
							rewrite HnewBFirstFrees0P in *.
							destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
								rewrite FreeSlotsListRec_unroll in Hoptionfreeslotslistpd.
								rewrite FreeSlotsListRec_unroll in Hoptionfreeslotslistpd2.
								unfold getFreeSlotsListAux in *.
								induction (maxIdx+1). (* false induction because of fixpoint constraints *)
								** (* N=0 -> NotWellFormed *)
									rewrite Hoptionlist2s0 in *.
									cbn in Hwellformed2s0.
									congruence.
								** (* N>0 *)
									clear IHn.
									rewrite HlookupnewBs0 in *.
									destruct (StateLib.Index.ltb (nbfreeslots pdentry) zero) eqn:Hltb ; try(cbn in * ; congruence).
									destruct (StateLib.Index.ltb (nbfreeslots pd2entry) zero) eqn:Hltb' ; try(cbn in * ; congruence).
									destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred1 ; try(exfalso ; congruence).
									*** destruct (StateLib.Index.pred (nbfreeslots pd2entry)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
											**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd2.
														cbn in *.
														unfold Lib.disjoint in HDisjointpdpd2s0.
														specialize(HDisjointpdpd2s0 newBlockEntryAddr).
														simpl in HDisjointpdpd2s0.
														intuition.
											**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd2.
														cbn in *. congruence.
									*** destruct (StateLib.Index.pred (nbfreeslots pd2entry)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
											**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd2.
														cbn in *.
														unfold Lib.disjoint in HDisjointpdpd2s0.
														specialize(HDisjointpdpd2s0 newBlockEntryAddr).
														simpl in HDisjointpdpd2s0.
														intuition.
											**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd2.
														cbn in *. congruence.
			--- unfold isBE. unfold s4. cbn.
					destruct (beqAddr pdinsertion newBlockEntryAddr) ; try(exfalso ; congruence).
					rewrite beqAddrTrue.
					cbn.
					repeat rewrite removeDupIdentity ; intuition.
			--- subst listoption2.
					rewrite <- Hfreeslotss1 in *. rewrite <- Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. intuition.
			--- assert(H_NoDups0 : NoDupInFreeSlotsList s0)
							by (unfold consistency in * ; intuition).
					unfold NoDupInFreeSlotsList in *.
					specialize (H_NoDups0 pd2 pd2entry Hlookuppd2s0).
					destruct H_NoDups0 as [optionlist2 (Hoptionlist2 & HwellFormed2' & HNoDup2)].
					unfold getFreeSlotsList in Hoptionlist2.
					rewrite Hlookuppd2s0 in *.
					destruct (beqAddr (firstfreeslot pd2entry) nullAddr) eqn:Hpd2Null ; try(exfalso ; congruence).
					subst optionlist2. subst listoption2.
					rewrite Hfreeslotss1 in *. rewrite Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. intuition.
			--- rewrite <- Hfreeslotss3 in *.
					rewrite Hfreeslotss2 in *. rewrite Hfreeslotss1 in *.
					(* newB is in freeslots list of pdinsertion, so can't be in other list
							because of Disjoint *)
					(* DUP from previous step *)
					destruct HDisjointpdpd2s0 as [optionfreeslotslistpd (optionfreeslotslistpd2 & (Hoptionfreeslotslistpd & (Hwellformedpds0 & (Hoptionfreeslotslistpd2 & (Hwellformedpd2s0 & HDisjointpdpd2s0)))))].
					unfold getFreeSlotsList in Hoptionfreeslotslistpd.
					unfold getFreeSlotsList in Hoptionfreeslotslistpd2.
					rewrite Hpdinsertions0 in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					rewrite HnewBFirstFrees0PDT in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
					rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
					destruct (beqAddr (firstfreeslot pd2entry) nullAddr) eqn:HfirstfreeNull ; try(exfalso ; congruence).
					(* firstfreeslot p <> NULL *)
					(* if first free of other PD is NOT NULL,
					then newB can't be in the two lists at s0 because of Disjoint -> False *)
					subst listoption2. subst listoption1.
					unfold Lib.disjoint in HDisjointpdpd2s0.
					specialize(HDisjointpdpd2s0 newBlockEntryAddr).
					destruct (HDisjointpdpd2s0).
					* subst optionfreeslotslistpd.
						rewrite FreeSlotsListRec_unroll.
						unfold getFreeSlotsListAux.
						assert(HmaxIdxNextEq :	maxIdx + 1 = S maxIdx) by apply MaxIdxNextEq.
						rewrite HmaxIdxNextEq.
						rewrite HlookupnewBs0.
						assert(HcurrNb : currnbfreeslots = nbfreeslots pdentry).
						{ unfold pdentryNbFreeSlots in *. rewrite Hpdinsertions0 in *. intuition. }
						rewrite <- HcurrNb in *.
						destruct (StateLib.Index.ltb currnbfreeslots zero) eqn:Hltb ; try(exfalso ; congruence).
						** unfold StateLib.Index.ltb in Hltb.
								apply PeanoNat.Nat.ltb_lt in Hltb.
								contradict Hltb. apply PeanoNat.Nat.lt_asymm. intuition.
						**	destruct (StateLib.Index.pred currnbfreeslots) eqn:Hpred ; try(exfalso ; congruence).
								cbn. intuition.
					* subst optionfreeslotslistpd2.
						intuition.
} fold s1. fold s2. fold s3. fold s4.
	set (s5 := {| currentPartition := currentPartition ?s4; memory := _ |}).
	simpl in s4.
	assert(Hfreeslotss5 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s5 (nbfreeslots pd2entry) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s4 (nbfreeslots pd2entry)).
	{
		(* DUP *)
				apply getFreeSlotsListRecEqBE ; intuition.
				---	(* Lists are disjoint at s0, so newB <> firstfreeslot p *)
							destruct HDisjointpdpd2s0 as [optionfreeslotslistpd (optionfreeslotslistpd2 & (Hoptionfreeslotslistpd & (Hwellformedpds0 & (Hoptionfreeslotslistpd2 & (Hwellformedpd2s0 & HDisjointpdpd2s0)))))].

							unfold getFreeSlotsList in Hoptionfreeslotslistpd.
							unfold getFreeSlotsList in Hoptionfreeslotslistpd2.
							rewrite Hpdinsertions0 in *.
							rewrite Hlookuppd1Eq in *.
							assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
							{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
							assert(HnewBFirstFrees0P : firstfreeslot pd2entry = newBlockEntryAddr) by intuition.
							rewrite HnewBFirstFrees0PDT in *.
							rewrite HnewBFirstFrees0P in *.
							destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
								rewrite FreeSlotsListRec_unroll in Hoptionfreeslotslistpd.
								rewrite FreeSlotsListRec_unroll in Hoptionfreeslotslistpd2.
								unfold getFreeSlotsListAux in *.
								induction (maxIdx+1). (* false induction because of fixpoint constraints *)
								** (* N=0 -> NotWellFormed *)
									rewrite Hoptionlist2s0 in *.
									cbn in Hwellformed2s0.
									congruence.
								** (* N>0 *)
									clear IHn.
									rewrite HlookupnewBs0 in *.
									destruct (StateLib.Index.ltb (nbfreeslots pdentry) zero) eqn:Hltb ; try(cbn in * ; congruence).
									destruct (StateLib.Index.ltb (nbfreeslots pd2entry) zero) eqn:Hltb' ; try(cbn in * ; congruence).
									destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred1 ; try(exfalso ; congruence).
									*** destruct (StateLib.Index.pred (nbfreeslots pd2entry)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
											**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd2.
														cbn in *.
														unfold Lib.disjoint in HDisjointpdpd2s0.
														specialize(HDisjointpdpd2s0 newBlockEntryAddr).
														simpl in HDisjointpdpd2s0.
														intuition.
											**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd2.
														cbn in *. congruence.
									*** destruct (StateLib.Index.pred (nbfreeslots pd2entry)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
											**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd2.
														cbn in *.
														unfold Lib.disjoint in HDisjointpdpd2s0.
														specialize(HDisjointpdpd2s0 newBlockEntryAddr).
														simpl in HDisjointpdpd2s0.
														intuition.
											**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd2.
														cbn in *. congruence.
			--- unfold isBE. unfold s5. cbn.
					destruct (beqAddr pdinsertion newBlockEntryAddr) ; try(exfalso ; congruence).
					rewrite beqAddrTrue.
					cbn.
					repeat rewrite removeDupIdentity ; intuition.
			--- subst listoption2.
					rewrite <- Hfreeslotss1 in *. rewrite <- Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *. intuition.
			--- assert(H_NoDups0 : NoDupInFreeSlotsList s0)
							by (unfold consistency in * ; intuition).
					unfold NoDupInFreeSlotsList in *.
					specialize (H_NoDups0 pd2 pd2entry Hlookuppd2s0).
					destruct H_NoDups0 as [optionlist2 (Hoptionlist2 & HwellFormed2' & HNoDup2)].
					unfold getFreeSlotsList in Hoptionlist2.
					rewrite Hlookuppd2s0 in *.
					destruct (beqAddr (firstfreeslot pd2entry) nullAddr) eqn:Hpd2Null ; try(exfalso ; congruence).
					subst optionlist2. subst listoption2.
					rewrite Hfreeslotss1 in *. rewrite Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *. intuition.
			--- rewrite <- Hfreeslotss4 in *. rewrite <- Hfreeslotss3 in *.
					rewrite Hfreeslotss2 in *. rewrite Hfreeslotss1 in *.
					(* newB is in freeslots list of pdinsertion, so can't be in other list
							because of Disjoint *)
					(* DUP from previous step *)
					destruct HDisjointpdpd2s0 as [optionfreeslotslistpd (optionfreeslotslistpd2 & (Hoptionfreeslotslistpd & (Hwellformedpds0 & (Hoptionfreeslotslistpd2 & (Hwellformedpd2s0 & HDisjointpdpd2s0)))))].
					unfold getFreeSlotsList in Hoptionfreeslotslistpd.
					unfold getFreeSlotsList in Hoptionfreeslotslistpd2.
					rewrite Hpdinsertions0 in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					rewrite HnewBFirstFrees0PDT in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
					rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
					destruct (beqAddr (firstfreeslot pd2entry) nullAddr) eqn:HfirstfreeNull ; try(exfalso ; congruence).
					(* firstfreeslot p <> NULL *)
					(* if first free of other PD is NOT NULL,
					then newB can't be in the two lists at s0 because of Disjoint -> False *)
					subst listoption2. subst listoption1.
					unfold Lib.disjoint in HDisjointpdpd2s0.
					specialize(HDisjointpdpd2s0 newBlockEntryAddr).
					destruct (HDisjointpdpd2s0).
					* subst optionfreeslotslistpd.
						rewrite FreeSlotsListRec_unroll.
						unfold getFreeSlotsListAux.
						assert(HmaxIdxNextEq :	maxIdx + 1 = S maxIdx) by apply MaxIdxNextEq.
						rewrite HmaxIdxNextEq.
						rewrite HlookupnewBs0.
						assert(HcurrNb : currnbfreeslots = nbfreeslots pdentry).
						{ unfold pdentryNbFreeSlots in *. rewrite Hpdinsertions0 in *. intuition. }
						rewrite <- HcurrNb in *.
						destruct (StateLib.Index.ltb currnbfreeslots zero) eqn:Hltb ; try(exfalso ; congruence).
						** unfold StateLib.Index.ltb in Hltb.
								apply PeanoNat.Nat.ltb_lt in Hltb.
								contradict Hltb. apply PeanoNat.Nat.lt_asymm. intuition.
						**	destruct (StateLib.Index.pred currnbfreeslots) eqn:Hpred ; try(exfalso ; congruence).
								cbn. intuition.
					* subst optionfreeslotslistpd2.
						intuition.
}
	fold s1. fold s2. fold s3. fold s4. fold s5.
	set (s6 := {| currentPartition := currentPartition ?s5; memory := _ |}).
	simpl in s4.
	assert(Hfreeslotss6 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s6 (nbfreeslots pd2entry) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s5 (nbfreeslots pd2entry)).
	{
		(* DUP *)
				apply getFreeSlotsListRecEqBE ; intuition.
				---	(* Lists are disjoint at s0, so newB <> firstfreeslot p *)
							destruct HDisjointpdpd2s0 as [optionfreeslotslistpd (optionfreeslotslistpd2 & (Hoptionfreeslotslistpd & (Hwellformedpds0 & (Hoptionfreeslotslistpd2 & (Hwellformedpd2s0 & HDisjointpdpd2s0)))))].

							unfold getFreeSlotsList in Hoptionfreeslotslistpd.
							unfold getFreeSlotsList in Hoptionfreeslotslistpd2.
							rewrite Hpdinsertions0 in *.
							rewrite Hlookuppd1Eq in *.
							assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
							{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
							assert(HnewBFirstFrees0P : firstfreeslot pd2entry = newBlockEntryAddr) by intuition.
							rewrite HnewBFirstFrees0PDT in *.
							rewrite HnewBFirstFrees0P in *.
							destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
								rewrite FreeSlotsListRec_unroll in Hoptionfreeslotslistpd.
								rewrite FreeSlotsListRec_unroll in Hoptionfreeslotslistpd2.
								unfold getFreeSlotsListAux in *.
								induction (maxIdx+1). (* false induction because of fixpoint constraints *)
								** (* N=0 -> NotWellFormed *)
									rewrite Hoptionlist2s0 in *.
									cbn in Hwellformed2s0.
									congruence.
								** (* N>0 *)
									clear IHn.
									rewrite HlookupnewBs0 in *.
									destruct (StateLib.Index.ltb (nbfreeslots pdentry) zero) eqn:Hltb ; try(cbn in * ; congruence).
									destruct (StateLib.Index.ltb (nbfreeslots pd2entry) zero) eqn:Hltb' ; try(cbn in * ; congruence).
									destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred1 ; try(exfalso ; congruence).
									*** destruct (StateLib.Index.pred (nbfreeslots pd2entry)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
											**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd2.
														cbn in *.
														unfold Lib.disjoint in HDisjointpdpd2s0.
														specialize(HDisjointpdpd2s0 newBlockEntryAddr).
														simpl in HDisjointpdpd2s0.
														intuition.
											**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd2.
														cbn in *. congruence.
									*** destruct (StateLib.Index.pred (nbfreeslots pd2entry)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
											**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd2.
														cbn in *.
														unfold Lib.disjoint in HDisjointpdpd2s0.
														specialize(HDisjointpdpd2s0 newBlockEntryAddr).
														simpl in HDisjointpdpd2s0.
														intuition.
											**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd2.
														cbn in *. congruence.
			--- unfold isBE. unfold s6. cbn.
					destruct (beqAddr pdinsertion newBlockEntryAddr) ; try(exfalso ; congruence).
					rewrite beqAddrTrue.
					cbn.
					repeat rewrite removeDupIdentity ; intuition.
			--- subst listoption2.
					rewrite <- Hfreeslotss1 in *. rewrite <- Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *.
					rewrite <- Hfreeslotss5 in *. intuition.
			--- assert(H_NoDups0 : NoDupInFreeSlotsList s0)
							by (unfold consistency in * ; intuition).
					unfold NoDupInFreeSlotsList in *.
					specialize (H_NoDups0 pd2 pd2entry Hlookuppd2s0).
					destruct H_NoDups0 as [optionlist2 (Hoptionlist2 & HwellFormed2' & HNoDup2)].
					unfold getFreeSlotsList in Hoptionlist2.
					rewrite Hlookuppd2s0 in *.
					destruct (beqAddr (firstfreeslot pd2entry) nullAddr) eqn:Hpd2Null ; try(exfalso ; congruence).
					subst optionlist2. subst listoption2.
					rewrite Hfreeslotss1 in *. rewrite Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *.
					rewrite <- Hfreeslotss5 in *. intuition.
			--- rewrite <- Hfreeslotss5 in *.
					rewrite <- Hfreeslotss4 in *. rewrite <- Hfreeslotss3 in *.
					rewrite Hfreeslotss2 in *. rewrite Hfreeslotss1 in *.
					(* newB is in freeslots list of pdinsertion, so can't be in other list
							because of Disjoint *)
					(* DUP from previous step *)
					destruct HDisjointpdpd2s0 as [optionfreeslotslistpd (optionfreeslotslistpd2 & (Hoptionfreeslotslistpd & (Hwellformedpds0 & (Hoptionfreeslotslistpd2 & (Hwellformedpd2s0 & HDisjointpdpd2s0)))))].
					unfold getFreeSlotsList in Hoptionfreeslotslistpd.
					unfold getFreeSlotsList in Hoptionfreeslotslistpd2.
					rewrite Hpdinsertions0 in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					rewrite HnewBFirstFrees0PDT in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
					rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
					destruct (beqAddr (firstfreeslot pd2entry) nullAddr) eqn:HfirstfreeNull ; try(exfalso ; congruence).
					(* firstfreeslot p <> NULL *)
					(* if first free of other PD is NOT NULL,
					then newB can't be in the two lists at s0 because of Disjoint -> False *)
					subst listoption2. subst listoption1.
					unfold Lib.disjoint in HDisjointpdpd2s0.
					specialize(HDisjointpdpd2s0 newBlockEntryAddr).
					destruct (HDisjointpdpd2s0).
					* subst optionfreeslotslistpd.
						rewrite FreeSlotsListRec_unroll.
						unfold getFreeSlotsListAux.
						assert(HmaxIdxNextEq :	maxIdx + 1 = S maxIdx) by apply MaxIdxNextEq.
						rewrite HmaxIdxNextEq.
						rewrite HlookupnewBs0.
						assert(HcurrNb : currnbfreeslots = nbfreeslots pdentry).
						{ unfold pdentryNbFreeSlots in *. rewrite Hpdinsertions0 in *. intuition. }
						rewrite <- HcurrNb in *.
						destruct (StateLib.Index.ltb currnbfreeslots zero) eqn:Hltb ; try(exfalso ; congruence).
						** unfold StateLib.Index.ltb in Hltb.
								apply PeanoNat.Nat.ltb_lt in Hltb.
								contradict Hltb. apply PeanoNat.Nat.lt_asymm. intuition.
						**	destruct (StateLib.Index.pred currnbfreeslots) eqn:Hpred ; try(exfalso ; congruence).
								cbn. intuition.
					* subst optionfreeslotslistpd2.
						intuition.
}
	fold s1. fold s2. fold s3. fold s4. fold s5. fold s6.
	set (s7 := {| currentPartition := currentPartition ?s6; memory := _ |}).
	simpl in s5. simpl in s6.
	assert(Hfreeslotss7 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s7 (nbfreeslots pd2entry) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s6 (nbfreeslots pd2entry)).
	{
		(* DUP *)
				apply getFreeSlotsListRecEqBE ; intuition.
				---	(* Lists are disjoint at s0, so newB <> firstfreeslot p *)
							destruct HDisjointpdpd2s0 as [optionfreeslotslistpd (optionfreeslotslistpd2 & (Hoptionfreeslotslistpd & (Hwellformedpds0 & (Hoptionfreeslotslistpd2 & (Hwellformedpd2s0 & HDisjointpdpd2s0)))))].

							unfold getFreeSlotsList in Hoptionfreeslotslistpd.
							unfold getFreeSlotsList in Hoptionfreeslotslistpd2.
							rewrite Hpdinsertions0 in *.
							rewrite Hlookuppd1Eq in *.
							assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
							{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
							assert(HnewBFirstFrees0P : firstfreeslot pd2entry = newBlockEntryAddr) by intuition.
							rewrite HnewBFirstFrees0PDT in *.
							rewrite HnewBFirstFrees0P in *.
							destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
								rewrite FreeSlotsListRec_unroll in Hoptionfreeslotslistpd.
								rewrite FreeSlotsListRec_unroll in Hoptionfreeslotslistpd2.
								unfold getFreeSlotsListAux in *.
								induction (maxIdx+1). (* false induction because of fixpoint constraints *)
								** (* N=0 -> NotWellFormed *)
									rewrite Hoptionlist2s0 in *.
									cbn in Hwellformed2s0.
									congruence.
								** (* N>0 *)
									clear IHn.
									rewrite HlookupnewBs0 in *.
									destruct (StateLib.Index.ltb (nbfreeslots pdentry) zero) eqn:Hltb ; try(cbn in * ; congruence).
									destruct (StateLib.Index.ltb (nbfreeslots pd2entry) zero) eqn:Hltb' ; try(cbn in * ; congruence).
									destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred1 ; try(exfalso ; congruence).
									*** destruct (StateLib.Index.pred (nbfreeslots pd2entry)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
											**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd2.
														cbn in *.
														unfold Lib.disjoint in HDisjointpdpd2s0.
														specialize(HDisjointpdpd2s0 newBlockEntryAddr).
														simpl in HDisjointpdpd2s0.
														intuition.
											**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd2.
														cbn in *. congruence.
									*** destruct (StateLib.Index.pred (nbfreeslots pd2entry)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
											**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd2.
														cbn in *.
														unfold Lib.disjoint in HDisjointpdpd2s0.
														specialize(HDisjointpdpd2s0 newBlockEntryAddr).
														simpl in HDisjointpdpd2s0.
														intuition.
											**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd2.
														cbn in *. congruence.
			--- unfold isBE. unfold s7. cbn.
					destruct (beqAddr pdinsertion newBlockEntryAddr) ; try(exfalso ; congruence).
					rewrite beqAddrTrue.
					cbn.
					repeat rewrite removeDupIdentity ; intuition.
			--- subst listoption2.
					rewrite <- Hfreeslotss1 in *. rewrite <- Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *.
					rewrite <- Hfreeslotss5 in *. rewrite <- Hfreeslotss6 in *. intuition.
			--- assert(H_NoDups0 : NoDupInFreeSlotsList s0)
							by (unfold consistency in * ; intuition).
					unfold NoDupInFreeSlotsList in *.
					specialize (H_NoDups0 pd2 pd2entry Hlookuppd2s0).
					destruct H_NoDups0 as [optionlist2 (Hoptionlist2 & HwellFormed2' & HNoDup2)].
					unfold getFreeSlotsList in Hoptionlist2.
					rewrite Hlookuppd2s0 in *.
					destruct (beqAddr (firstfreeslot pd2entry) nullAddr) eqn:Hpd2Null ; try(exfalso ; congruence).
					subst optionlist2. subst listoption2.
					rewrite Hfreeslotss1 in *. rewrite Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *.
					rewrite <- Hfreeslotss5 in *. rewrite <- Hfreeslotss6 in *. intuition.
			--- rewrite <- Hfreeslotss6 in *. rewrite <- Hfreeslotss5 in *.
					rewrite <- Hfreeslotss4 in *. rewrite <- Hfreeslotss3 in *.
					rewrite Hfreeslotss2 in *. rewrite Hfreeslotss1 in *.
					(* newB is in freeslots list of pdinsertion, so can't be in other list
							because of Disjoint *)
					(* DUP from previous step *)
					destruct HDisjointpdpd2s0 as [optionfreeslotslistpd (optionfreeslotslistpd2 & (Hoptionfreeslotslistpd & (Hwellformedpds0 & (Hoptionfreeslotslistpd2 & (Hwellformedpd2s0 & HDisjointpdpd2s0)))))].
					unfold getFreeSlotsList in Hoptionfreeslotslistpd.
					unfold getFreeSlotsList in Hoptionfreeslotslistpd2.
					rewrite Hpdinsertions0 in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					rewrite HnewBFirstFrees0PDT in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
					rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
					destruct (beqAddr (firstfreeslot pd2entry) nullAddr) eqn:HfirstfreeNull ; try(exfalso ; congruence).
					(* firstfreeslot p <> NULL *)
					(* if first free of other PD is NOT NULL,
					then newB can't be in the two lists at s0 because of Disjoint -> False *)
					subst listoption2. subst listoption1.
					unfold Lib.disjoint in HDisjointpdpd2s0.
					specialize(HDisjointpdpd2s0 newBlockEntryAddr).
					destruct (HDisjointpdpd2s0).
					* subst optionfreeslotslistpd.
						rewrite FreeSlotsListRec_unroll.
						unfold getFreeSlotsListAux.
						assert(HmaxIdxNextEq :	maxIdx + 1 = S maxIdx) by apply MaxIdxNextEq.
						rewrite HmaxIdxNextEq.
						rewrite HlookupnewBs0.
						assert(HcurrNb : currnbfreeslots = nbfreeslots pdentry).
						{ unfold pdentryNbFreeSlots in *. rewrite Hpdinsertions0 in *. intuition. }
						rewrite <- HcurrNb in *.
						destruct (StateLib.Index.ltb currnbfreeslots zero) eqn:Hltb ; try(exfalso ; congruence).
						** unfold StateLib.Index.ltb in Hltb.
								apply PeanoNat.Nat.ltb_lt in Hltb.
								contradict Hltb. apply PeanoNat.Nat.lt_asymm. intuition.
						**	destruct (StateLib.Index.pred currnbfreeslots) eqn:Hpred ; try(exfalso ; congruence).
								cbn. intuition.
					* subst optionfreeslotslistpd2.
						intuition.
}
	fold s1. fold s2. fold s3. fold s4. fold s5. fold s6. fold s7.
	set (s8 := {| currentPartition := currentPartition ?s7; memory := _ |}).
	simpl in s7.
	assert(Hfreeslotss8 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s8 (nbfreeslots pd2entry) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s7 (nbfreeslots pd2entry)).
	{
		(* DUP *)
		apply getFreeSlotsListRecEqBE ; intuition.
		---	(* Lists are disjoint at s0, so newB <> firstfreeslot p *)
					destruct HDisjointpdpd2s0 as [optionfreeslotslistpd (optionfreeslotslistpd2 & (Hoptionfreeslotslistpd & (Hwellformedpds0 & (Hoptionfreeslotslistpd2 & (Hwellformedpd2s0 & HDisjointpdpd2s0)))))].

					unfold getFreeSlotsList in Hoptionfreeslotslistpd.
					unfold getFreeSlotsList in Hoptionfreeslotslistpd2.
					rewrite Hpdinsertions0 in *.
					rewrite Hlookuppd1Eq in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					assert(HnewBFirstFrees0P : firstfreeslot pd2entry = newBlockEntryAddr) by intuition.
					rewrite HnewBFirstFrees0PDT in *.
					rewrite HnewBFirstFrees0P in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
						rewrite FreeSlotsListRec_unroll in Hoptionfreeslotslistpd.
						rewrite FreeSlotsListRec_unroll in Hoptionfreeslotslistpd2.
						unfold getFreeSlotsListAux in *.
						induction (maxIdx+1). (* false induction because of fixpoint constraints *)
						** (* N=0 -> NotWellFormed *)
							rewrite Hoptionlist2s0 in *.
							cbn in Hwellformed2s0.
							congruence.
						** (* N>0 *)
							clear IHn.
							rewrite HlookupnewBs0 in *.
							destruct (StateLib.Index.ltb (nbfreeslots pdentry) zero) eqn:Hltb ; try(cbn in * ; congruence).
							destruct (StateLib.Index.ltb (nbfreeslots pd2entry) zero) eqn:Hltb' ; try(cbn in * ; congruence).
							destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred1 ; try(exfalso ; congruence).
							*** destruct (StateLib.Index.pred (nbfreeslots pd2entry)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
									**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd2.
												cbn in *.
												unfold Lib.disjoint in HDisjointpdpd2s0.
												specialize(HDisjointpdpd2s0 newBlockEntryAddr).
												simpl in HDisjointpdpd2s0.
												intuition.
									**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd2.
												cbn in *. congruence.
							*** destruct (StateLib.Index.pred (nbfreeslots pd2entry)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
									**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd2.
												cbn in *.
												unfold Lib.disjoint in HDisjointpdpd2s0.
												specialize(HDisjointpdpd2s0 newBlockEntryAddr).
												simpl in HDisjointpdpd2s0.
												intuition.
									**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd2.
												cbn in *. congruence.
			--- unfold isBE. unfold s8. cbn.
					destruct (beqAddr pdinsertion newBlockEntryAddr) ; try(exfalso ; congruence).
					rewrite beqAddrTrue.
					cbn.
					repeat rewrite removeDupIdentity ; intuition.
			--- subst listoption2.
					rewrite <- Hfreeslotss1 in *. rewrite <- Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *.
					rewrite <- Hfreeslotss5 in *. rewrite <- Hfreeslotss6 in *.
					rewrite <- Hfreeslotss7 in *. intuition.
			--- assert(H_NoDups0 : NoDupInFreeSlotsList s0)
							by (unfold consistency in * ; intuition).
					unfold NoDupInFreeSlotsList in *.
					specialize (H_NoDups0 pd2 pd2entry Hlookuppd2s0).
					destruct H_NoDups0 as [optionlist2 (Hoptionlist2 & HwellFormed2' & HNoDup2)].
					unfold getFreeSlotsList in Hoptionlist2.
					rewrite Hlookuppd2s0 in *.
					destruct (beqAddr (firstfreeslot pd2entry) nullAddr) eqn:Hpd2Null ; try(exfalso ; congruence).
					subst optionlist2. subst listoption2.
					rewrite Hfreeslotss1 in *. rewrite Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *.
					rewrite <- Hfreeslotss5 in *. rewrite <- Hfreeslotss6 in *.
					rewrite <- Hfreeslotss7 in *. intuition.
			--- rewrite <- Hfreeslotss7 in *.
					rewrite <- Hfreeslotss6 in *. rewrite <- Hfreeslotss5 in *.
					rewrite <- Hfreeslotss4 in *. rewrite <- Hfreeslotss3 in *.
					rewrite Hfreeslotss2 in *. rewrite Hfreeslotss1 in *.
					(* newB is in freeslots list of pdinsertion, so can't be in other list
							because of Disjoint *)
					(* DUP from previous step *)
					destruct HDisjointpdpd2s0 as [optionfreeslotslistpd (optionfreeslotslistpd2 & (Hoptionfreeslotslistpd & (Hwellformedpds0 & (Hoptionfreeslotslistpd2 & (Hwellformedpd2s0 & HDisjointpdpd2s0)))))].
					unfold getFreeSlotsList in Hoptionfreeslotslistpd.
					unfold getFreeSlotsList in Hoptionfreeslotslistpd2.
					rewrite Hpdinsertions0 in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					rewrite HnewBFirstFrees0PDT in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
					rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
					destruct (beqAddr (firstfreeslot pd2entry) nullAddr) eqn:HfirstfreeNull ; try(exfalso ; congruence).
					(* firstfreeslot p <> NULL *)
					(* if first free of other PD is NOT NULL,
					then newB can't be in the two lists at s0 because of Disjoint -> False *)
					subst listoption2. subst listoption1.
					unfold Lib.disjoint in HDisjointpdpd2s0.
					specialize(HDisjointpdpd2s0 newBlockEntryAddr).
					destruct (HDisjointpdpd2s0).
					* subst optionfreeslotslistpd.
						rewrite FreeSlotsListRec_unroll.
						unfold getFreeSlotsListAux.
						assert(HmaxIdxNextEq :	maxIdx + 1 = S maxIdx) by apply MaxIdxNextEq.
						rewrite HmaxIdxNextEq.
						rewrite HlookupnewBs0.
						assert(HcurrNb : currnbfreeslots = nbfreeslots pdentry).
						{ unfold pdentryNbFreeSlots in *. rewrite Hpdinsertions0 in *. intuition. }
						rewrite <- HcurrNb in *.
						destruct (StateLib.Index.ltb currnbfreeslots zero) eqn:Hltb ; try(exfalso ; congruence).
						** unfold StateLib.Index.ltb in Hltb.
								apply PeanoNat.Nat.ltb_lt in Hltb.
								contradict Hltb. apply PeanoNat.Nat.lt_asymm. intuition.
						**	destruct (StateLib.Index.pred currnbfreeslots) eqn:Hpred ; try(exfalso ; congruence).
								cbn. intuition.
					* subst optionfreeslotslistpd2.
						intuition.
}
	fold s1. fold s2. fold s3. fold s4. fold s5. fold s6. fold s7. fold s8.
	set (s9 := {| currentPartition := currentPartition ?s8; memory := _ |}).
	simpl in s7.
	assert(Hfreeslotss9 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s9 (nbfreeslots pd2entry) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s8 (nbfreeslots pd2entry)).
	{
		(* DUP *)
		apply getFreeSlotsListRecEqBE ; intuition.
		---	(* Lists are disjoint at s0, so newB <> firstfreeslot p *)
					destruct HDisjointpdpd2s0 as [optionfreeslotslistpd (optionfreeslotslistpd2 & (Hoptionfreeslotslistpd & (Hwellformedpds0 & (Hoptionfreeslotslistpd2 & (Hwellformedpd2s0 & HDisjointpdpd2s0)))))].

					unfold getFreeSlotsList in Hoptionfreeslotslistpd.
					unfold getFreeSlotsList in Hoptionfreeslotslistpd2.
					rewrite Hpdinsertions0 in *.
					rewrite Hlookuppd1Eq in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					assert(HnewBFirstFrees0P : firstfreeslot pd2entry = newBlockEntryAddr) by intuition.
					rewrite HnewBFirstFrees0PDT in *.
					rewrite HnewBFirstFrees0P in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
						rewrite FreeSlotsListRec_unroll in Hoptionfreeslotslistpd.
						rewrite FreeSlotsListRec_unroll in Hoptionfreeslotslistpd2.
						unfold getFreeSlotsListAux in *.
						induction (maxIdx+1). (* false induction because of fixpoint constraints *)
						** (* N=0 -> NotWellFormed *)
							rewrite Hoptionlist2s0 in *.
							cbn in Hwellformed2s0.
							congruence.
						** (* N>0 *)
							clear IHn.
							rewrite HlookupnewBs0 in *.
							destruct (StateLib.Index.ltb (nbfreeslots pdentry) zero) eqn:Hltb ; try(cbn in * ; congruence).
							destruct (StateLib.Index.ltb (nbfreeslots pd2entry) zero) eqn:Hltb' ; try(cbn in * ; congruence).
							destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred1 ; try(exfalso ; congruence).
							*** destruct (StateLib.Index.pred (nbfreeslots pd2entry)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
									**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd2.
												cbn in *.
												unfold Lib.disjoint in HDisjointpdpd2s0.
												specialize(HDisjointpdpd2s0 newBlockEntryAddr).
												simpl in HDisjointpdpd2s0.
												intuition.
									**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd2.
												cbn in *. congruence.
							*** destruct (StateLib.Index.pred (nbfreeslots pd2entry)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
									**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd2.
												cbn in *.
												unfold Lib.disjoint in HDisjointpdpd2s0.
												specialize(HDisjointpdpd2s0 newBlockEntryAddr).
												simpl in HDisjointpdpd2s0.
												intuition.
									**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd2.
												cbn in *. congruence.
			--- unfold isBE. unfold s9. cbn.
					destruct (beqAddr pdinsertion newBlockEntryAddr) ; try(exfalso ; congruence).
					rewrite beqAddrTrue.
					cbn.
					repeat rewrite removeDupIdentity ; intuition.
			--- subst listoption2.
					rewrite <- Hfreeslotss1 in *. rewrite <- Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *.
					rewrite <- Hfreeslotss5 in *. rewrite <- Hfreeslotss6 in *.
					rewrite <- Hfreeslotss7 in *. rewrite <- Hfreeslotss8 in *. intuition.
			--- assert(H_NoDups0 : NoDupInFreeSlotsList s0)
							by (unfold consistency in * ; intuition).
					unfold NoDupInFreeSlotsList in *.
					specialize (H_NoDups0 pd2 pd2entry Hlookuppd2s0).
					destruct H_NoDups0 as [optionlist2 (Hoptionlist2 & HwellFormed2' & HNoDup2)].
					unfold getFreeSlotsList in Hoptionlist2.
					rewrite Hlookuppd2s0 in *.
					destruct (beqAddr (firstfreeslot pd2entry) nullAddr) eqn:Hpd2Null ; try(exfalso ; congruence).
					subst optionlist2. subst listoption2.
					rewrite Hfreeslotss1 in *. rewrite Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *.
					rewrite <- Hfreeslotss5 in *. rewrite <- Hfreeslotss6 in *.
					rewrite <- Hfreeslotss7 in *. rewrite <- Hfreeslotss8 in *. intuition.
			--- rewrite <- Hfreeslotss8 in *. rewrite <- Hfreeslotss7 in *.
					rewrite <- Hfreeslotss6 in *. rewrite <- Hfreeslotss5 in *.
					rewrite <- Hfreeslotss4 in *. rewrite <- Hfreeslotss3 in *.
					rewrite Hfreeslotss2 in *. rewrite Hfreeslotss1 in *.
					(* newB is in freeslots list of pdinsertion, so can't be in other list
							because of Disjoint *)
					(* DUP from previous step *)
					destruct HDisjointpdpd2s0 as [optionfreeslotslistpd (optionfreeslotslistpd2 & (Hoptionfreeslotslistpd & (Hwellformedpds0 & (Hoptionfreeslotslistpd2 & (Hwellformedpd2s0 & HDisjointpdpd2s0)))))].
					unfold getFreeSlotsList in Hoptionfreeslotslistpd.
					unfold getFreeSlotsList in Hoptionfreeslotslistpd2.
					rewrite Hpdinsertions0 in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					rewrite HnewBFirstFrees0PDT in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
					rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
					destruct (beqAddr (firstfreeslot pd2entry) nullAddr) eqn:HfirstfreeNull ; try(exfalso ; congruence).
					(* firstfreeslot p <> NULL *)
					(* if first free of other PD is NOT NULL,
					then newB can't be in the two lists at s0 because of Disjoint -> False *)
					subst listoption2. subst listoption1.
					unfold Lib.disjoint in HDisjointpdpd2s0.
					specialize(HDisjointpdpd2s0 newBlockEntryAddr).
					destruct (HDisjointpdpd2s0).
					* subst optionfreeslotslistpd.
						rewrite FreeSlotsListRec_unroll.
						unfold getFreeSlotsListAux.
						assert(HmaxIdxNextEq :	maxIdx + 1 = S maxIdx) by apply MaxIdxNextEq.
						rewrite HmaxIdxNextEq.
						rewrite HlookupnewBs0.
						assert(HcurrNb : currnbfreeslots = nbfreeslots pdentry).
						{ unfold pdentryNbFreeSlots in *. rewrite Hpdinsertions0 in *. intuition. }
						rewrite <- HcurrNb in *.
						destruct (StateLib.Index.ltb currnbfreeslots zero) eqn:Hltb ; try(exfalso ; congruence).
						** unfold StateLib.Index.ltb in Hltb.
								apply PeanoNat.Nat.ltb_lt in Hltb.
								contradict Hltb. apply PeanoNat.Nat.lt_asymm. intuition.
						**	destruct (StateLib.Index.pred currnbfreeslots) eqn:Hpred ; try(exfalso ; congruence).
								cbn. intuition.
					* subst optionfreeslotslistpd2.
						intuition.
}
	fold s1. fold s2. fold s3. fold s4. fold s5. fold s6. fold s7. fold s8. fold s9.
	set (s10 := {| currentPartition := currentPartition ?s9; memory := _ |}).
	simpl in s8. simpl in s9.
	assert(Hfreeslotss10 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s10 (nbfreeslots pd2entry) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s9 (nbfreeslots pd2entry)).
	{			assert(HSCEs9 : isSCE sceaddr s9).
				{ unfold isSCE. unfold s9. cbn. rewrite beqAddrTrue.
					destruct (beqAddr newBlockEntryAddr sceaddr) eqn:Hf ; try(exfalso ; congruence).
					rewrite <- beqAddrFalse in *.
					repeat rewrite removeDupIdentity ; intuition.
					destruct (beqAddr pdinsertion newBlockEntryAddr) eqn:Hff ; try(exfalso ; congruence).
					rewrite <- DependentTypeLemmas.beqAddrTrue in Hff. congruence.
					cbn.
					destruct (beqAddr pdinsertion sceaddr) eqn:Hfff ; try(exfalso ; congruence).
					rewrite <- DependentTypeLemmas.beqAddrTrue in Hfff. congruence.
					rewrite beqAddrTrue.
					rewrite <- beqAddrFalse in *.
					repeat rewrite removeDupIdentity ; intuition.
				}
				apply getFreeSlotsListRecEqSCE.
				--- 	intro Hfirstsceeq.
						assert(HFirstFreeSlotPointerIsBEAndFreeSlots0 : FirstFreeSlotPointerIsBEAndFreeSlot s0)
							by (unfold consistency in * ; intuition).
						unfold FirstFreeSlotPointerIsBEAndFreeSlot in *.
						specialize (HFirstFreeSlotPointerIsBEAndFreeSlots0 pd2 pd2entry Hlookuppd2s0).
						destruct HFirstFreeSlotPointerIsBEAndFreeSlots0.
						---- intro HfirstfreeNull.
								assert(HnullAddrExistss0 : nullAddrExists s0)
									by (unfold consistency in * ; intuition).
								unfold nullAddrExists in *.
								unfold isSCE in *.
								unfold isPADDR in *.
								rewrite HfirstfreeNull in *. rewrite <- Hfirstsceeq in *.
								destruct (lookup nullAddr (memory s0) beqAddr) ; try(exfalso ; congruence).
								destruct v ; try(exfalso ; congruence).
						---- rewrite Hfirstsceeq in *.
								unfold isSCE in *.
								unfold isBE in *.
								destruct (lookup sceaddr (memory s0) beqAddr) ; try (exfalso ; congruence).
								destruct v ; try(exfalso ; congruence).
				--- unfold isBE. unfold isSCE in HSCEs9.
						destruct (lookup sceaddr (memory s9) beqAddr) eqn:Hlookupsces9 ; try(exfalso ; congruence).
						destruct v ; try(exfalso ; congruence).
						intuition.
				--- unfold isPADDR. unfold isSCE in HSCEs9.
						destruct (lookup sceaddr (memory s9) beqAddr) eqn:Hlookupsces9 ; try(exfalso ; congruence).
						destruct v ; try(exfalso ; congruence).
						intuition.
}
	fold s1. fold s2. fold s3. fold s4. fold s5. fold s6. fold s7. fold s8. fold s9.
	fold s10.

	intuition.
	assert(HcurrLtmaxIdx : nbfreeslots pd2entry <= maxIdx).
	{ intuition. apply IdxLtMaxIdx. }
	lia.
}
														destruct Hfreeslotspd2Eq as [s1 (s2 & (s3 & (s4 & (s5 & (s6 & (s7 & (s8 & (s9 & (s10 &
																							(n1 & (nbleft & (Hnbleft & Hstates))))))))))))].
														assert(HsEq : s10 = s).
														{ intuition. subst s1. subst s2. subst s3. subst s4. subst s5. subst s6.
															subst s7. subst s8. subst s9. subst s10.
															rewrite Hs. f_equal.
														}
														rewrite HsEq in *.
														assert(HfreeslotsEq : getFreeSlotsListRec n1 (firstfreeslot pd2entry) s (nbfreeslots pd2entry) =
																									getFreeSlotsListRec (maxIdx+1) (firstfreeslot pd2entry) s0 (nbfreeslots pd2entry)).
														{
															intuition.
															subst nbleft.
															(* rewrite all previous getFreeSlotsListRec equalities *)
															rewrite <- H33. rewrite <- H36. rewrite <- H38.
															rewrite <- H40. rewrite <- H42. rewrite <- H44.
															rewrite <- H46. rewrite <- H48. rewrite <- H50.
															rewrite <- H53.
															reflexivity.
														}
														assert (HfreeslotsEqn1 : getFreeSlotsListRec n1 (firstfreeslot pd2entry) s (nbfreeslots pd2entry)
																											= getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s (nbfreeslots pd2entry)).
														{ eapply getFreeSlotsListRecEqN ; intuition.
															subst nbleft. lia.
															assert (HnbLtmaxIdx : nbfreeslots pd2entry <= maxIdx) by apply IdxLtMaxIdx.
															lia.
														}
														rewrite <- HfreeslotsEqn1. rewrite HfreeslotsEq. intuition.

										------- (* listoption1 <> NIL *)
														(* show equality beween listoption1 at s0 and at s
																-> if equality, then show listoption2 has not changed either
																		-> if listoption1 and listoption2 stayed the same
																				and they were disjoint at s0, then they
																				are still disjoint at s*)

														assert(Hfreeslotspd1Eq : exists s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 n1 nbleft,
nbleft = (nbfreeslots pd1entry) /\
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
                     vidtBlock := vidtBlock pdentry
                   |}) (memory s0) beqAddr |} /\
getFreeSlotsListRec n1 (firstfreeslot pd1entry) s1 nbleft =
getFreeSlotsListRec (maxIdx+1) (firstfreeslot pd1entry) s0 nbleft
			 /\
	n1 <= maxIdx+1 /\ nbleft < n1
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
		                vidtBlock := vidtBlock pdentry0
		              |}
                 ) (memory s1) beqAddr |} /\
getFreeSlotsListRec n1 (firstfreeslot pd1entry) s2 nbleft =
			getFreeSlotsListRec n1 (firstfreeslot pd1entry) s1 nbleft
/\ s3 = {|
     currentPartition := currentPartition s2;
     memory := add newBlockEntryAddr
	            (BE
	               (CBlockEntry (read bentry) 
	                  (write bentry) (exec bentry) 
	                  (present bentry) (accessible bentry)
	                  (blockindex bentry)
	                  (CBlock startaddr (endAddr (blockrange bentry))))
                 ) (memory s2) beqAddr |} /\
getFreeSlotsListRec n1 (firstfreeslot pd1entry) s3 nbleft =
			getFreeSlotsListRec n1 (firstfreeslot pd1entry) s2 nbleft
/\ s4 = {|
     currentPartition := currentPartition s3;
     memory := add newBlockEntryAddr
               (BE
                  (CBlockEntry (read bentry0) 
                     (write bentry0) (exec bentry0) 
                     (present bentry0) (accessible bentry0)
                     (blockindex bentry0)
                     (CBlock (startAddr (blockrange bentry0)) endaddr))
                 ) (memory s3) beqAddr |} /\
getFreeSlotsListRec n1 (firstfreeslot pd1entry) s4 nbleft =
			getFreeSlotsListRec n1 (firstfreeslot pd1entry) s3 nbleft
/\ s5 = {|
     currentPartition := currentPartition s4;
     memory := add newBlockEntryAddr
              (BE
                 (CBlockEntry (read bentry1) 
                    (write bentry1) (exec bentry1) 
                    (present bentry1) true (blockindex bentry1)
                    (blockrange bentry1))
                 ) (memory s4) beqAddr |} /\
getFreeSlotsListRec n1 (firstfreeslot pd1entry) s5 nbleft =
			getFreeSlotsListRec n1 (firstfreeslot pd1entry) s4 nbleft
/\ s6 = {|
     currentPartition := currentPartition s5;
     memory := add newBlockEntryAddr
               (BE
                  (CBlockEntry (read bentry2) (write bentry2) 
                     (exec bentry2) true (accessible bentry2)
                     (blockindex bentry2) (blockrange bentry2))
                 ) (memory s5) beqAddr |} /\
getFreeSlotsListRec n1 (firstfreeslot pd1entry) s6 nbleft =
			getFreeSlotsListRec n1 (firstfreeslot pd1entry) s5 nbleft
/\ s7 = {|
     currentPartition := currentPartition s6;
     memory := add newBlockEntryAddr
              (BE
                 (CBlockEntry r (write bentry3) (exec bentry3)
                    (present bentry3) (accessible bentry3) 
                    (blockindex bentry3) (blockrange bentry3))
                 ) (memory s6) beqAddr |} /\
getFreeSlotsListRec n1 (firstfreeslot pd1entry) s7 nbleft =
			getFreeSlotsListRec n1 (firstfreeslot pd1entry) s6 nbleft
/\ s8 = {|
     currentPartition := currentPartition s7;
     memory := add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry4) w (exec bentry4) 
                       (present bentry4) (accessible bentry4) 
                       (blockindex bentry4) (blockrange bentry4))
                 ) (memory s7) beqAddr |} /\
getFreeSlotsListRec n1(firstfreeslot pd1entry) s8 nbleft =
			getFreeSlotsListRec n1 (firstfreeslot pd1entry) s7 nbleft
/\ s9 = {|
     currentPartition := currentPartition s8;
     memory := add newBlockEntryAddr
              (BE
                 (CBlockEntry (read bentry5) (write bentry5) e 
                    (present bentry5) (accessible bentry5) 
                    (blockindex bentry5) (blockrange bentry5))
                 ) (memory s8) beqAddr |} /\
getFreeSlotsListRec n1 (firstfreeslot pd1entry) s9 nbleft =
			getFreeSlotsListRec n1 (firstfreeslot pd1entry) s8 nbleft
/\ s10 = {|
     currentPartition := currentPartition s9;
     memory := add sceaddr 
								(SCE {| origin := origin; next := next scentry |}
                 ) (memory s9) beqAddr |} /\
getFreeSlotsListRec n1 (firstfreeslot pd1entry) s10 nbleft =
			getFreeSlotsListRec n1 (firstfreeslot pd1entry) s9 nbleft
).
{
	eexists ?[s1]. eexists ?[s2]. eexists ?[s3]. eexists ?[s4]. eexists ?[s5].
	eexists ?[s6]. eexists ?[s7]. eexists ?[s8]. eexists ?[s9].
	eexists ?[s10]. eexists ?[n1]. eexists.
	split. intuition.
	split. intuition.
	set (s1 := {| currentPartition := _ |}).
	(* prove outside *)
	assert(Hfreeslotss1 : getFreeSlotsListRec ?n1 (firstfreeslot pd1entry) s1 (nbfreeslots pd1entry) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd1entry) s0 (nbfreeslots pd1entry)).
	{
		apply getFreeSlotsListRecEqPDT.
		-- 	intro Hfirstpdeq.
				assert(HFirstFreeSlotPointerIsBEAndFreeSlots0 : FirstFreeSlotPointerIsBEAndFreeSlot s0)
					by (unfold consistency in * ; intuition).
				unfold FirstFreeSlotPointerIsBEAndFreeSlot in *.
				specialize (HFirstFreeSlotPointerIsBEAndFreeSlots0 pd1 pd1entry Hlookuppd1s0).
				destruct HFirstFreeSlotPointerIsBEAndFreeSlots0.
				--- intro HfirstfreeNull.
						assert(HnullAddrExistss0 : nullAddrExists s0)
							by (unfold consistency in * ; intuition).
						unfold nullAddrExists in *.
						unfold isPADDR in *.
						rewrite HfirstfreeNull in *. rewrite <- Hfirstpdeq in *.
						destruct (lookup nullAddr (memory s0) beqAddr) ; try(exfalso ; congruence).
						destruct v ; try(exfalso ; congruence).
				--- rewrite Hfirstpdeq in *.
						unfold isBE in *.
						destruct (lookup pdinsertion (memory s0) beqAddr) ; try (exfalso ; congruence).
						destruct v ; try(exfalso ; congruence).
		-- unfold isBE. rewrite Hpdinsertions0. intuition.
		-- unfold isPADDR. rewrite Hpdinsertions0. intuition.
	}
	set (s2 := {| currentPartition := _ |}).
	assert(Hfreeslotss2 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd1entry) s2 (nbfreeslots pd1entry) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd1entry) s1 (nbfreeslots pd1entry)).
	{
		apply getFreeSlotsListRecEqPDT.
		--- 	intro Hfirstpdeq.
				assert(HFirstFreeSlotPointerIsBEAndFreeSlots0 : FirstFreeSlotPointerIsBEAndFreeSlot s0)
					by (unfold consistency in * ; intuition).
				unfold FirstFreeSlotPointerIsBEAndFreeSlot in *.
				specialize (HFirstFreeSlotPointerIsBEAndFreeSlots0 pd1 pd1entry Hlookuppd1s0).
				destruct HFirstFreeSlotPointerIsBEAndFreeSlots0.
				---- intro HfirstfreeNull.
						assert(HnullAddrExistss0 : nullAddrExists s0)
							by (unfold consistency in * ; intuition).
						unfold nullAddrExists in *.
						unfold isPADDR in *.
						rewrite HfirstfreeNull in *. rewrite <- Hfirstpdeq in *.
						destruct (lookup nullAddr (memory s0) beqAddr) ; try(exfalso ; congruence).
						destruct v ; try(exfalso ; congruence).
				---- rewrite Hfirstpdeq in *.
						unfold isBE in *.
						destruct (lookup pdinsertion (memory s0) beqAddr) ; try (exfalso ; congruence).
						destruct v ; try(exfalso ; congruence).
		--- unfold isBE. unfold s1. cbn. rewrite beqAddrTrue. intuition.
		--- unfold isPADDR. unfold s1. cbn. rewrite beqAddrTrue. intuition.
	}
	set (s3 := {| currentPartition := _ |}).
	assert(Hfreeslotss3 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd1entry) s3 (nbfreeslots pd1entry) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd1entry) s2 (nbfreeslots pd1entry)).
	{
		apply getFreeSlotsListRecEqBE ; intuition.
		---	(* Lists are disjoint at s0, so newB <> firstfreeslot pd1entry *)
					destruct HDisjointpdpd1s0 as [optionfreeslotslistpd (optionfreeslotslistpd1 & (Hoptionfreeslotslistpd & (Hwellformedpds0 & (Hoptionfreeslotslistpd1 & (Hwellformedpd1s0 & HDisjointpdpd1s0)))))].

					unfold getFreeSlotsList in Hoptionfreeslotslistpd.
					unfold getFreeSlotsList in Hoptionfreeslotslistpd1.
					rewrite Hpdinsertions0 in *.
					rewrite Hlookuppd1s0 in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					assert(HnewBFirstFrees0P : firstfreeslot pd1entry = newBlockEntryAddr) by intuition.
					rewrite HnewBFirstFrees0PDT in *.
					rewrite HnewBFirstFrees0P in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
						rewrite FreeSlotsListRec_unroll in Hoptionfreeslotslistpd.
						rewrite FreeSlotsListRec_unroll in Hoptionfreeslotslistpd1.
						unfold getFreeSlotsListAux in *.
						induction (maxIdx+1). (* false induction because of fixpoint constraints *)
						** (* N=0 -> NotWellFormed *)
							rewrite Hoptionlist1s0 in *.
							cbn in Hwellformed1s0.
							congruence.
						** (* N>0 *)
							clear IHn.
							rewrite HlookupnewBs0 in *.
							destruct (StateLib.Index.ltb (nbfreeslots pdentry) zero) eqn:Hltb ; try(cbn in * ; congruence).
							destruct (StateLib.Index.ltb (nbfreeslots pd1entry) zero) eqn:Hltb' ; try(cbn in * ; congruence).
							destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred1 ; try(exfalso ; congruence).
							*** destruct (StateLib.Index.pred (nbfreeslots pd1entry)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
									**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd1.
												cbn in *.
												unfold Lib.disjoint in HDisjointpdpd1s0.
												specialize(HDisjointpdpd1s0 newBlockEntryAddr).
												simpl in HDisjointpdpd1s0.
												intuition.
									**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd1.
												cbn in *. congruence.
							*** destruct (StateLib.Index.pred (nbfreeslots pd1entry)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
									**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd1.
												cbn in *.
												unfold Lib.disjoint in HDisjointpdpd1s0.
												specialize(HDisjointpdpd1s0 newBlockEntryAddr).
												simpl in HDisjointpdpd1s0.
												intuition.
									**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd1.
												cbn in *. congruence.
			--- unfold isBE. unfold s3. cbn.
					destruct (beqAddr pdinsertion newBlockEntryAddr) ; try(exfalso ; congruence).
					rewrite beqAddrTrue.
					cbn.
					repeat rewrite removeDupIdentity ; intuition.
			--- subst listoption1.
					rewrite <- Hfreeslotss1 in *. rewrite <- Hfreeslotss2 in *. intuition.
			--- assert(H_NoDups0 : NoDupInFreeSlotsList s0)
							by (unfold consistency in * ; intuition).
					unfold NoDupInFreeSlotsList in *.
					specialize (H_NoDups0 pd1 pd1entry Hlookuppd1s0).
					destruct H_NoDups0 as [optionlist1 (Hoptionlist1 & HwellFormed1' & HNoDup1)].
					unfold getFreeSlotsList in Hoptionlist1.
					rewrite Hlookuppd1s0 in *.
					destruct (beqAddr (firstfreeslot pd1entry) nullAddr)  ; try(exfalso ; congruence).
					subst optionlist1. subst listoption1.
					rewrite Hfreeslotss1 in *. rewrite Hfreeslotss2 in *. intuition.
			--- rewrite Hfreeslotss2 in *. rewrite Hfreeslotss1 in *.
					(* newB is in freeslots list of pdinsertion, so can't be in other list
							because of Disjoint *)
					(* DUP from previous step *)
					destruct HDisjointpdpd1s0 as [optionfreeslotslistpd (optionfreeslotslistpd1 & (Hoptionfreeslotslistpd & (Hwellformedpds0 & (Hoptionfreeslotslistpd1 & (Hwellformedpd1s0 & HDisjointpdpd1s0)))))].
					unfold getFreeSlotsList in Hoptionfreeslotslistpd.
					unfold getFreeSlotsList in Hoptionfreeslotslistpd1.
					rewrite Hpdinsertions0 in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					rewrite HnewBFirstFrees0PDT in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
					rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
					destruct (beqAddr (firstfreeslot pd1entry) nullAddr) eqn:HfirstfreeNull ; try(exfalso ; congruence).
					(* firstfreeslot p <> NULL *)
					(* if first free of other PD is NOT NULL,
					then newB can't be in the two lists at s0 because of Disjoint -> False *)
					subst listoption2. subst listoption1.
					rewrite Hlookuppd1s0 in *.
					unfold Lib.disjoint in HDisjointpdpd1s0.
					specialize(HDisjointpdpd1s0 newBlockEntryAddr).
					destruct (HDisjointpdpd1s0).
					* subst optionfreeslotslistpd.
						rewrite FreeSlotsListRec_unroll.
						unfold getFreeSlotsListAux.
						assert(HmaxIdxNextEq :	maxIdx + 1 = S maxIdx) by apply MaxIdxNextEq.
						rewrite HmaxIdxNextEq.
						rewrite HlookupnewBs0.
						assert(HcurrNb : currnbfreeslots = nbfreeslots pdentry).
						{ unfold pdentryNbFreeSlots in *. rewrite Hpdinsertions0 in *. intuition. }
						rewrite <- HcurrNb in *.
						destruct (StateLib.Index.ltb currnbfreeslots zero) eqn:Hltb ; try(exfalso ; congruence).
						** unfold StateLib.Index.ltb in Hltb.
								apply PeanoNat.Nat.ltb_lt in Hltb.
								contradict Hltb. apply PeanoNat.Nat.lt_asymm. intuition.
						**	destruct (StateLib.Index.pred currnbfreeslots) eqn:Hpred ; try(exfalso ; congruence).
								cbn. intuition.
					* subst optionfreeslotslistpd1.
						destruct (beqAddr (firstfreeslot pd1entry) nullAddr) ; try(exfalso ; congruence).
						intuition.
}
	set (s4 := {| currentPartition := currentPartition ?s3; memory := _ |}). simpl in s4. simpl in s3.
	assert(Hfreeslotss4 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd1entry) s4 (nbfreeslots pd1entry) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd1entry) s3 (nbfreeslots pd1entry)).
	{
		(* DUP *)
		apply getFreeSlotsListRecEqBE ; intuition.
		---	(* Lists are disjoint at s0, so newB <> firstfreeslot p *)
					destruct HDisjointpdpd1s0 as [optionfreeslotslistpd (optionfreeslotslistpd1 & (Hoptionfreeslotslistpd & (Hwellformedpds0 & (Hoptionfreeslotslistpd1 & (Hwellformedpd1s0 & HDisjointpdpd1s0)))))].

					unfold getFreeSlotsList in Hoptionfreeslotslistpd.
					unfold getFreeSlotsList in Hoptionfreeslotslistpd1.
					rewrite Hpdinsertions0 in *.
					rewrite Hlookuppd1s0 in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					assert(HnewBFirstFrees0P : firstfreeslot pd1entry = newBlockEntryAddr) by intuition.
					rewrite HnewBFirstFrees0PDT in *.
					rewrite HnewBFirstFrees0P in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
						rewrite FreeSlotsListRec_unroll in Hoptionfreeslotslistpd.
						rewrite FreeSlotsListRec_unroll in Hoptionfreeslotslistpd1.
						unfold getFreeSlotsListAux in *.
						induction (maxIdx+1). (* false induction because of fixpoint constraints *)
						** (* N=0 -> NotWellFormed *)
							rewrite Hoptionlist1s0 in *.
							cbn in Hwellformed1s0.
							congruence.
						** (* N>0 *)
							clear IHn.
							rewrite HlookupnewBs0 in *.
							destruct (StateLib.Index.ltb (nbfreeslots pdentry) zero) eqn:Hltb ; try(cbn in * ; congruence).
							destruct (StateLib.Index.ltb (nbfreeslots pd1entry) zero) eqn:Hltb' ; try(cbn in * ; congruence).
							destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred1 ; try(exfalso ; congruence).
							*** destruct (StateLib.Index.pred (nbfreeslots pd1entry)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
									**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd1.
												cbn in *.
												unfold Lib.disjoint in HDisjointpdpd1s0.
												specialize(HDisjointpdpd1s0 newBlockEntryAddr).
												simpl in HDisjointpdpd1s0.
												intuition.
									**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd1.
												cbn in *. congruence.
							*** destruct (StateLib.Index.pred (nbfreeslots pd1entry)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
									**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd1.
												cbn in *.
												unfold Lib.disjoint in HDisjointpdpd1s0.
												specialize(HDisjointpdpd1s0 newBlockEntryAddr).
												simpl in HDisjointpdpd1s0.
												intuition.
									**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd1.
												cbn in *. congruence.
			--- unfold isBE. unfold s4. cbn.
					destruct (beqAddr pdinsertion newBlockEntryAddr) ; try(exfalso ; congruence).
					rewrite beqAddrTrue.
					cbn.
					repeat rewrite removeDupIdentity ; intuition.
			--- subst listoption1.
					rewrite <- Hfreeslotss1 in *. rewrite <- Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. intuition.
			--- assert(H_NoDups0 : NoDupInFreeSlotsList s0)
							by (unfold consistency in * ; intuition).
					unfold NoDupInFreeSlotsList in *.
					specialize (H_NoDups0 pd1 pd1entry Hlookuppd1s0).
					destruct H_NoDups0 as [optionlist1 (Hoptionlist1 & HwellFormed1' & HNoDup1)].
					unfold getFreeSlotsList in Hoptionlist1.
					rewrite Hlookuppd1s0 in *.
					destruct (beqAddr (firstfreeslot pd1entry) nullAddr)  ; try(exfalso ; congruence).
					subst optionlist1. subst listoption1.
					rewrite Hfreeslotss1 in *. rewrite Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. intuition.
			--- rewrite <- Hfreeslotss3 in *.
					rewrite Hfreeslotss2 in *. rewrite Hfreeslotss1 in *.
					(* newB is in freeslots list of pdinsertion, so can't be in other list
							because of Disjoint *)
					(* DUP from previous step *)
					destruct HDisjointpdpd1s0 as [optionfreeslotslistpd (optionfreeslotslistpd1 & (Hoptionfreeslotslistpd & (Hwellformedpds0 & (Hoptionfreeslotslistpd1 & (Hwellformedpd1s0 & HDisjointpdpd1s0)))))].
					unfold getFreeSlotsList in Hoptionfreeslotslistpd.
					unfold getFreeSlotsList in Hoptionfreeslotslistpd1.
					rewrite Hpdinsertions0 in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					rewrite HnewBFirstFrees0PDT in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
					rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
					destruct (beqAddr (firstfreeslot pd1entry) nullAddr) eqn:HfirstfreeNull ; try(exfalso ; congruence).
					(* firstfreeslot p <> NULL *)
					(* if first free of other PD is NOT NULL,
					then newB can't be in the two lists at s0 because of Disjoint -> False *)
					subst listoption2. subst listoption1.
					rewrite Hlookuppd1s0 in *.
					unfold Lib.disjoint in HDisjointpdpd1s0.
					specialize(HDisjointpdpd1s0 newBlockEntryAddr).
					destruct (HDisjointpdpd1s0).
					* subst optionfreeslotslistpd.
						rewrite FreeSlotsListRec_unroll.
						unfold getFreeSlotsListAux.
						assert(HmaxIdxNextEq :	maxIdx + 1 = S maxIdx) by apply MaxIdxNextEq.
						rewrite HmaxIdxNextEq.
						rewrite HlookupnewBs0.
						assert(HcurrNb : currnbfreeslots = nbfreeslots pdentry).
						{ unfold pdentryNbFreeSlots in *. rewrite Hpdinsertions0 in *. intuition. }
						rewrite <- HcurrNb in *.
						destruct (StateLib.Index.ltb currnbfreeslots zero) eqn:Hltb ; try(exfalso ; congruence).
						** unfold StateLib.Index.ltb in Hltb.
								apply PeanoNat.Nat.ltb_lt in Hltb.
								contradict Hltb. apply PeanoNat.Nat.lt_asymm. intuition.
						**	destruct (StateLib.Index.pred currnbfreeslots) eqn:Hpred ; try(exfalso ; congruence).
								cbn. intuition.
					* subst optionfreeslotslistpd1.
						destruct (beqAddr (firstfreeslot pd1entry) nullAddr) ; try(exfalso ; congruence).
						intuition.
} fold s1. fold s2. fold s3. fold s4.
	set (s5 := {| currentPartition := currentPartition ?s4; memory := _ |}).
	simpl in s4.
	assert(Hfreeslotss5 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd1entry) s5 (nbfreeslots pd1entry) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd1entry) s4 (nbfreeslots pd1entry)).
	{
		(* DUP *)
		apply getFreeSlotsListRecEqBE ; intuition.
		---	(* Lists are disjoint at s0, so newB <> firstfreeslot p *)
					destruct HDisjointpdpd1s0 as [optionfreeslotslistpd (optionfreeslotslistpd1 & (Hoptionfreeslotslistpd & (Hwellformedpds0 & (Hoptionfreeslotslistpd1 & (Hwellformedpd1s0 & HDisjointpdpd1s0)))))].

					unfold getFreeSlotsList in Hoptionfreeslotslistpd.
					unfold getFreeSlotsList in Hoptionfreeslotslistpd1.
					rewrite Hpdinsertions0 in *.
					rewrite Hlookuppd1s0 in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					assert(HnewBFirstFrees0P : firstfreeslot pd1entry = newBlockEntryAddr) by intuition.
					rewrite HnewBFirstFrees0PDT in *.
					rewrite HnewBFirstFrees0P in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
						rewrite FreeSlotsListRec_unroll in Hoptionfreeslotslistpd.
						rewrite FreeSlotsListRec_unroll in Hoptionfreeslotslistpd1.
						unfold getFreeSlotsListAux in *.
						induction (maxIdx+1). (* false induction because of fixpoint constraints *)
						** (* N=0 -> NotWellFormed *)
							rewrite Hoptionlist1s0 in *.
							cbn in Hwellformed1s0.
							congruence.
						** (* N>0 *)
							clear IHn.
							rewrite HlookupnewBs0 in *.
							destruct (StateLib.Index.ltb (nbfreeslots pdentry) zero) eqn:Hltb ; try(cbn in * ; congruence).
							destruct (StateLib.Index.ltb (nbfreeslots pd1entry) zero) eqn:Hltb' ; try(cbn in * ; congruence).
							destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred1 ; try(exfalso ; congruence).
							*** destruct (StateLib.Index.pred (nbfreeslots pd1entry)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
									**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd1.
												cbn in *.
												unfold Lib.disjoint in HDisjointpdpd1s0.
												specialize(HDisjointpdpd1s0 newBlockEntryAddr).
												simpl in HDisjointpdpd1s0.
												intuition.
									**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd1.
												cbn in *. congruence.
							*** destruct (StateLib.Index.pred (nbfreeslots pd1entry)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
									**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd1.
												cbn in *.
												unfold Lib.disjoint in HDisjointpdpd1s0.
												specialize(HDisjointpdpd1s0 newBlockEntryAddr).
												simpl in HDisjointpdpd1s0.
												intuition.
									**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd1.
												cbn in *. congruence.
			--- unfold isBE. unfold s5. cbn.
					destruct (beqAddr pdinsertion newBlockEntryAddr) ; try(exfalso ; congruence).
					rewrite beqAddrTrue.
					cbn.
					repeat rewrite removeDupIdentity ; intuition.
			--- subst listoption1.
					rewrite <- Hfreeslotss1 in *. rewrite <- Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *. intuition.
			--- assert(H_NoDups0 : NoDupInFreeSlotsList s0)
							by (unfold consistency in * ; intuition).
					unfold NoDupInFreeSlotsList in *.
					specialize (H_NoDups0 pd1 pd1entry Hlookuppd1s0).
					destruct H_NoDups0 as [optionlist1 (Hoptionlist1 & HwellFormed1' & HNoDup1)].
					unfold getFreeSlotsList in Hoptionlist1.
					rewrite Hlookuppd1s0 in *.
					destruct (beqAddr (firstfreeslot pd1entry) nullAddr)  ; try(exfalso ; congruence).
					subst optionlist1. subst listoption1.
					rewrite Hfreeslotss1 in *. rewrite Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *. intuition.
			--- rewrite <- Hfreeslotss4 in *. rewrite <- Hfreeslotss3 in *.
					rewrite Hfreeslotss2 in *. rewrite Hfreeslotss1 in *.
					(* newB is in freeslots list of pdinsertion, so can't be in other list
							because of Disjoint *)
					(* DUP from previous step *)
					destruct HDisjointpdpd1s0 as [optionfreeslotslistpd (optionfreeslotslistpd1 & (Hoptionfreeslotslistpd & (Hwellformedpds0 & (Hoptionfreeslotslistpd1 & (Hwellformedpd1s0 & HDisjointpdpd1s0)))))].
					unfold getFreeSlotsList in Hoptionfreeslotslistpd.
					unfold getFreeSlotsList in Hoptionfreeslotslistpd1.
					rewrite Hpdinsertions0 in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					rewrite HnewBFirstFrees0PDT in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
					rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
					destruct (beqAddr (firstfreeslot pd1entry) nullAddr) eqn:HfirstfreeNull ; try(exfalso ; congruence).
					(* firstfreeslot p <> NULL *)
					(* if first free of other PD is NOT NULL,
					then newB can't be in the two lists at s0 because of Disjoint -> False *)
					subst listoption2. subst listoption1.
					rewrite Hlookuppd1s0 in *.
					unfold Lib.disjoint in HDisjointpdpd1s0.
					specialize(HDisjointpdpd1s0 newBlockEntryAddr).
					destruct (HDisjointpdpd1s0).
					* subst optionfreeslotslistpd.
						rewrite FreeSlotsListRec_unroll.
						unfold getFreeSlotsListAux.
						assert(HmaxIdxNextEq :	maxIdx + 1 = S maxIdx) by apply MaxIdxNextEq.
						rewrite HmaxIdxNextEq.
						rewrite HlookupnewBs0.
						assert(HcurrNb : currnbfreeslots = nbfreeslots pdentry).
						{ unfold pdentryNbFreeSlots in *. rewrite Hpdinsertions0 in *. intuition. }
						rewrite <- HcurrNb in *.
						destruct (StateLib.Index.ltb currnbfreeslots zero) eqn:Hltb ; try(exfalso ; congruence).
						** unfold StateLib.Index.ltb in Hltb.
								apply PeanoNat.Nat.ltb_lt in Hltb.
								contradict Hltb. apply PeanoNat.Nat.lt_asymm. intuition.
						**	destruct (StateLib.Index.pred currnbfreeslots) eqn:Hpred ; try(exfalso ; congruence).
								cbn. intuition.
					* subst optionfreeslotslistpd1.
						destruct (beqAddr (firstfreeslot pd1entry) nullAddr) ; try(exfalso ; congruence).
						intuition.
}
	fold s1. fold s2. fold s3. fold s4. fold s5.
	set (s6 := {| currentPartition := currentPartition ?s5; memory := _ |}).
	simpl in s4.
	assert(Hfreeslotss6 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd1entry) s6 (nbfreeslots pd1entry) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd1entry) s5 (nbfreeslots pd1entry)).
	{
		(* DUP *)
		apply getFreeSlotsListRecEqBE ; intuition.
		---	(* Lists are disjoint at s0, so newB <> firstfreeslot p *)
					destruct HDisjointpdpd1s0 as [optionfreeslotslistpd (optionfreeslotslistpd1 & (Hoptionfreeslotslistpd & (Hwellformedpds0 & (Hoptionfreeslotslistpd1 & (Hwellformedpd1s0 & HDisjointpdpd1s0)))))].

					unfold getFreeSlotsList in Hoptionfreeslotslistpd.
					unfold getFreeSlotsList in Hoptionfreeslotslistpd1.
					rewrite Hpdinsertions0 in *.
					rewrite Hlookuppd1s0 in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					assert(HnewBFirstFrees0P : firstfreeslot pd1entry = newBlockEntryAddr) by intuition.
					rewrite HnewBFirstFrees0PDT in *.
					rewrite HnewBFirstFrees0P in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
						rewrite FreeSlotsListRec_unroll in Hoptionfreeslotslistpd.
						rewrite FreeSlotsListRec_unroll in Hoptionfreeslotslistpd1.
						unfold getFreeSlotsListAux in *.
						induction (maxIdx+1). (* false induction because of fixpoint constraints *)
						** (* N=0 -> NotWellFormed *)
							rewrite Hoptionlist1s0 in *.
							cbn in Hwellformed1s0.
							congruence.
						** (* N>0 *)
							clear IHn.
							rewrite HlookupnewBs0 in *.
							destruct (StateLib.Index.ltb (nbfreeslots pdentry) zero) eqn:Hltb ; try(cbn in * ; congruence).
							destruct (StateLib.Index.ltb (nbfreeslots pd1entry) zero) eqn:Hltb' ; try(cbn in * ; congruence).
							destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred1 ; try(exfalso ; congruence).
							*** destruct (StateLib.Index.pred (nbfreeslots pd1entry)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
									**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd1.
												cbn in *.
												unfold Lib.disjoint in HDisjointpdpd1s0.
												specialize(HDisjointpdpd1s0 newBlockEntryAddr).
												simpl in HDisjointpdpd1s0.
												intuition.
									**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd1.
												cbn in *. congruence.
							*** destruct (StateLib.Index.pred (nbfreeslots pd1entry)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
									**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd1.
												cbn in *.
												unfold Lib.disjoint in HDisjointpdpd1s0.
												specialize(HDisjointpdpd1s0 newBlockEntryAddr).
												simpl in HDisjointpdpd1s0.
												intuition.
									**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd1.
												cbn in *. congruence.
			--- unfold isBE. unfold s6. cbn.
					destruct (beqAddr pdinsertion newBlockEntryAddr) ; try(exfalso ; congruence).
					rewrite beqAddrTrue.
					cbn.
					repeat rewrite removeDupIdentity ; intuition.
			--- subst listoption1.
					rewrite <- Hfreeslotss1 in *. rewrite <- Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *.
					rewrite <- Hfreeslotss5 in *. intuition.
			--- assert(H_NoDups0 : NoDupInFreeSlotsList s0)
							by (unfold consistency in * ; intuition).
					unfold NoDupInFreeSlotsList in *.
					specialize (H_NoDups0 pd1 pd1entry Hlookuppd1s0).
					destruct H_NoDups0 as [optionlist1 (Hoptionlist1 & HwellFormed1' & HNoDup1)].
					unfold getFreeSlotsList in Hoptionlist1.
					rewrite Hlookuppd1s0 in *.
					destruct (beqAddr (firstfreeslot pd1entry) nullAddr)  ; try(exfalso ; congruence).
					subst optionlist1. subst listoption1.
					rewrite Hfreeslotss1 in *. rewrite Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *.
					rewrite <- Hfreeslotss5 in *. intuition.
			--- rewrite <- Hfreeslotss5 in *.
					rewrite <- Hfreeslotss4 in *. rewrite <- Hfreeslotss3 in *.
					rewrite Hfreeslotss2 in *. rewrite Hfreeslotss1 in *.
					(* newB is in freeslots list of pdinsertion, so can't be in other list
							because of Disjoint *)
					(* DUP from previous step *)
					destruct HDisjointpdpd1s0 as [optionfreeslotslistpd (optionfreeslotslistpd1 & (Hoptionfreeslotslistpd & (Hwellformedpds0 & (Hoptionfreeslotslistpd1 & (Hwellformedpd1s0 & HDisjointpdpd1s0)))))].
					unfold getFreeSlotsList in Hoptionfreeslotslistpd.
					unfold getFreeSlotsList in Hoptionfreeslotslistpd1.
					rewrite Hpdinsertions0 in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					rewrite HnewBFirstFrees0PDT in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
					rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
					destruct (beqAddr (firstfreeslot pd1entry) nullAddr) eqn:HfirstfreeNull ; try(exfalso ; congruence).
					(* firstfreeslot p <> NULL *)
					(* if first free of other PD is NOT NULL,
					then newB can't be in the two lists at s0 because of Disjoint -> False *)
					subst listoption2. subst listoption1.
					rewrite Hlookuppd1s0 in *.
					unfold Lib.disjoint in HDisjointpdpd1s0.
					specialize(HDisjointpdpd1s0 newBlockEntryAddr).
					destruct (HDisjointpdpd1s0).
					* subst optionfreeslotslistpd.
						rewrite FreeSlotsListRec_unroll.
						unfold getFreeSlotsListAux.
						assert(HmaxIdxNextEq :	maxIdx + 1 = S maxIdx) by apply MaxIdxNextEq.
						rewrite HmaxIdxNextEq.
						rewrite HlookupnewBs0.
						assert(HcurrNb : currnbfreeslots = nbfreeslots pdentry).
						{ unfold pdentryNbFreeSlots in *. rewrite Hpdinsertions0 in *. intuition. }
						rewrite <- HcurrNb in *.
						destruct (StateLib.Index.ltb currnbfreeslots zero) eqn:Hltb ; try(exfalso ; congruence).
						** unfold StateLib.Index.ltb in Hltb.
								apply PeanoNat.Nat.ltb_lt in Hltb.
								contradict Hltb. apply PeanoNat.Nat.lt_asymm. intuition.
						**	destruct (StateLib.Index.pred currnbfreeslots) eqn:Hpred ; try(exfalso ; congruence).
								cbn. intuition.
					* subst optionfreeslotslistpd1.
						destruct (beqAddr (firstfreeslot pd1entry) nullAddr) ; try(exfalso ; congruence).
						intuition.
}
	fold s1. fold s2. fold s3. fold s4. fold s5. fold s6.
	set (s7 := {| currentPartition := currentPartition ?s6; memory := _ |}).
	simpl in s5. simpl in s6.
	assert(Hfreeslotss7 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd1entry) s7 (nbfreeslots pd1entry) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd1entry) s6 (nbfreeslots pd1entry)).
	{
		(* DUP *)
		apply getFreeSlotsListRecEqBE ; intuition.
		---	(* Lists are disjoint at s0, so newB <> firstfreeslot p *)
					destruct HDisjointpdpd1s0 as [optionfreeslotslistpd (optionfreeslotslistpd1 & (Hoptionfreeslotslistpd & (Hwellformedpds0 & (Hoptionfreeslotslistpd1 & (Hwellformedpd1s0 & HDisjointpdpd1s0)))))].

					unfold getFreeSlotsList in Hoptionfreeslotslistpd.
					unfold getFreeSlotsList in Hoptionfreeslotslistpd1.
					rewrite Hpdinsertions0 in *.
					rewrite Hlookuppd1s0 in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					assert(HnewBFirstFrees0P : firstfreeslot pd1entry = newBlockEntryAddr) by intuition.
					rewrite HnewBFirstFrees0PDT in *.
					rewrite HnewBFirstFrees0P in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
						rewrite FreeSlotsListRec_unroll in Hoptionfreeslotslistpd.
						rewrite FreeSlotsListRec_unroll in Hoptionfreeslotslistpd1.
						unfold getFreeSlotsListAux in *.
						induction (maxIdx+1). (* false induction because of fixpoint constraints *)
						** (* N=0 -> NotWellFormed *)
							rewrite Hoptionlist1s0 in *.
							cbn in Hwellformed1s0.
							congruence.
						** (* N>0 *)
							clear IHn.
							rewrite HlookupnewBs0 in *.
							destruct (StateLib.Index.ltb (nbfreeslots pdentry) zero) eqn:Hltb ; try(cbn in * ; congruence).
							destruct (StateLib.Index.ltb (nbfreeslots pd1entry) zero) eqn:Hltb' ; try(cbn in * ; congruence).
							destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred1 ; try(exfalso ; congruence).
							*** destruct (StateLib.Index.pred (nbfreeslots pd1entry)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
									**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd1.
												cbn in *.
												unfold Lib.disjoint in HDisjointpdpd1s0.
												specialize(HDisjointpdpd1s0 newBlockEntryAddr).
												simpl in HDisjointpdpd1s0.
												intuition.
									**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd1.
												cbn in *. congruence.
							*** destruct (StateLib.Index.pred (nbfreeslots pd1entry)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
									**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd1.
												cbn in *.
												unfold Lib.disjoint in HDisjointpdpd1s0.
												specialize(HDisjointpdpd1s0 newBlockEntryAddr).
												simpl in HDisjointpdpd1s0.
												intuition.
									**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd1.
												cbn in *. congruence.
			--- unfold isBE. unfold s7. cbn.
					destruct (beqAddr pdinsertion newBlockEntryAddr) ; try(exfalso ; congruence).
					rewrite beqAddrTrue.
					cbn.
					repeat rewrite removeDupIdentity ; intuition.
			--- subst listoption1.
					rewrite <- Hfreeslotss1 in *. rewrite <- Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *.
					rewrite <- Hfreeslotss5 in *. rewrite <- Hfreeslotss6 in *. intuition.
			--- assert(H_NoDups0 : NoDupInFreeSlotsList s0)
							by (unfold consistency in * ; intuition).
					unfold NoDupInFreeSlotsList in *.
					specialize (H_NoDups0 pd1 pd1entry Hlookuppd1s0).
					destruct H_NoDups0 as [optionlist1 (Hoptionlist1 & HwellFormed1' & HNoDup1)].
					unfold getFreeSlotsList in Hoptionlist1.
					rewrite Hlookuppd1s0 in *.
					destruct (beqAddr (firstfreeslot pd1entry) nullAddr)  ; try(exfalso ; congruence).
					subst optionlist1. subst listoption1.
					rewrite Hfreeslotss1 in *. rewrite Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *.
					rewrite <- Hfreeslotss5 in *. rewrite <- Hfreeslotss6 in *. intuition.
			--- rewrite <- Hfreeslotss6 in *. rewrite <- Hfreeslotss5 in *.
					rewrite <- Hfreeslotss4 in *. rewrite <- Hfreeslotss3 in *.
					rewrite Hfreeslotss2 in *. rewrite Hfreeslotss1 in *.
					(* newB is in freeslots list of pdinsertion, so can't be in other list
							because of Disjoint *)
					(* DUP from previous step *)
					destruct HDisjointpdpd1s0 as [optionfreeslotslistpd (optionfreeslotslistpd1 & (Hoptionfreeslotslistpd & (Hwellformedpds0 & (Hoptionfreeslotslistpd1 & (Hwellformedpd1s0 & HDisjointpdpd1s0)))))].
					unfold getFreeSlotsList in Hoptionfreeslotslistpd.
					unfold getFreeSlotsList in Hoptionfreeslotslistpd1.
					rewrite Hpdinsertions0 in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					rewrite HnewBFirstFrees0PDT in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
					rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
					destruct (beqAddr (firstfreeslot pd1entry) nullAddr) eqn:HfirstfreeNull ; try(exfalso ; congruence).
					(* firstfreeslot p <> NULL *)
					(* if first free of other PD is NOT NULL,
					then newB can't be in the two lists at s0 because of Disjoint -> False *)
					subst listoption2. subst listoption1.
					rewrite Hlookuppd1s0 in *.
					unfold Lib.disjoint in HDisjointpdpd1s0.
					specialize(HDisjointpdpd1s0 newBlockEntryAddr).
					destruct (HDisjointpdpd1s0).
					* subst optionfreeslotslistpd.
						rewrite FreeSlotsListRec_unroll.
						unfold getFreeSlotsListAux.
						assert(HmaxIdxNextEq :	maxIdx + 1 = S maxIdx) by apply MaxIdxNextEq.
						rewrite HmaxIdxNextEq.
						rewrite HlookupnewBs0.
						assert(HcurrNb : currnbfreeslots = nbfreeslots pdentry).
						{ unfold pdentryNbFreeSlots in *. rewrite Hpdinsertions0 in *. intuition. }
						rewrite <- HcurrNb in *.
						destruct (StateLib.Index.ltb currnbfreeslots zero) eqn:Hltb ; try(exfalso ; congruence).
						** unfold StateLib.Index.ltb in Hltb.
								apply PeanoNat.Nat.ltb_lt in Hltb.
								contradict Hltb. apply PeanoNat.Nat.lt_asymm. intuition.
						**	destruct (StateLib.Index.pred currnbfreeslots) eqn:Hpred ; try(exfalso ; congruence).
								cbn. intuition.
					* subst optionfreeslotslistpd1.
						destruct (beqAddr (firstfreeslot pd1entry) nullAddr) ; try(exfalso ; congruence).
						intuition.
}
	fold s1. fold s2. fold s3. fold s4. fold s5. fold s6. fold s7.
	set (s8 := {| currentPartition := currentPartition ?s7; memory := _ |}).
	simpl in s7.
	assert(Hfreeslotss8 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd1entry) s8 (nbfreeslots pd1entry) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd1entry) s7 (nbfreeslots pd1entry)).
	{
		(* DUP *)
		apply getFreeSlotsListRecEqBE ; intuition.
		---	(* Lists are disjoint at s0, so newB <> firstfreeslot p *)
					destruct HDisjointpdpd1s0 as [optionfreeslotslistpd (optionfreeslotslistpd1 & (Hoptionfreeslotslistpd & (Hwellformedpds0 & (Hoptionfreeslotslistpd1 & (Hwellformedpd1s0 & HDisjointpdpd1s0)))))].

					unfold getFreeSlotsList in Hoptionfreeslotslistpd.
					unfold getFreeSlotsList in Hoptionfreeslotslistpd1.
					rewrite Hpdinsertions0 in *.
					rewrite Hlookuppd1s0 in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					assert(HnewBFirstFrees0P : firstfreeslot pd1entry = newBlockEntryAddr) by intuition.
					rewrite HnewBFirstFrees0PDT in *.
					rewrite HnewBFirstFrees0P in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
						rewrite FreeSlotsListRec_unroll in Hoptionfreeslotslistpd.
						rewrite FreeSlotsListRec_unroll in Hoptionfreeslotslistpd1.
						unfold getFreeSlotsListAux in *.
						induction (maxIdx+1). (* false induction because of fixpoint constraints *)
						** (* N=0 -> NotWellFormed *)
							rewrite Hoptionlist1s0 in *.
							cbn in Hwellformed1s0.
							congruence.
						** (* N>0 *)
							clear IHn.
							rewrite HlookupnewBs0 in *.
							destruct (StateLib.Index.ltb (nbfreeslots pdentry) zero) eqn:Hltb ; try(cbn in * ; congruence).
							destruct (StateLib.Index.ltb (nbfreeslots pd1entry) zero) eqn:Hltb' ; try(cbn in * ; congruence).
							destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred1 ; try(exfalso ; congruence).
							*** destruct (StateLib.Index.pred (nbfreeslots pd1entry)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
									**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd1.
												cbn in *.
												unfold Lib.disjoint in HDisjointpdpd1s0.
												specialize(HDisjointpdpd1s0 newBlockEntryAddr).
												simpl in HDisjointpdpd1s0.
												intuition.
									**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd1.
												cbn in *. congruence.
							*** destruct (StateLib.Index.pred (nbfreeslots pd1entry)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
									**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd1.
												cbn in *.
												unfold Lib.disjoint in HDisjointpdpd1s0.
												specialize(HDisjointpdpd1s0 newBlockEntryAddr).
												simpl in HDisjointpdpd1s0.
												intuition.
									**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd1.
												cbn in *. congruence.
			--- unfold isBE. unfold s8. cbn.
					destruct (beqAddr pdinsertion newBlockEntryAddr) ; try(exfalso ; congruence).
					rewrite beqAddrTrue.
					cbn.
					repeat rewrite removeDupIdentity ; intuition.
			--- subst listoption1.
					rewrite <- Hfreeslotss1 in *. rewrite <- Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *.
					rewrite <- Hfreeslotss5 in *. rewrite <- Hfreeslotss6 in *.
					rewrite <- Hfreeslotss7 in *. intuition.
			--- assert(H_NoDups0 : NoDupInFreeSlotsList s0)
							by (unfold consistency in * ; intuition).
					unfold NoDupInFreeSlotsList in *.
					specialize (H_NoDups0 pd1 pd1entry Hlookuppd1s0).
					destruct H_NoDups0 as [optionlist1 (Hoptionlist1 & HwellFormed1' & HNoDup1)].
					unfold getFreeSlotsList in Hoptionlist1.
					rewrite Hlookuppd1s0 in *.
					destruct (beqAddr (firstfreeslot pd1entry) nullAddr)  ; try(exfalso ; congruence).
					subst optionlist1. subst listoption1.
					rewrite Hfreeslotss1 in *. rewrite Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *.
					rewrite <- Hfreeslotss5 in *. rewrite <- Hfreeslotss6 in *.
					rewrite <- Hfreeslotss7 in *. intuition.
			--- rewrite <- Hfreeslotss7 in *.
					rewrite <- Hfreeslotss6 in *. rewrite <- Hfreeslotss5 in *.
					rewrite <- Hfreeslotss4 in *. rewrite <- Hfreeslotss3 in *.
					rewrite Hfreeslotss2 in *. rewrite Hfreeslotss1 in *.
					(* newB is in freeslots list of pdinsertion, so can't be in other list
							because of Disjoint *)
					(* DUP from previous step *)
					destruct HDisjointpdpd1s0 as [optionfreeslotslistpd (optionfreeslotslistpd1 & (Hoptionfreeslotslistpd & (Hwellformedpds0 & (Hoptionfreeslotslistpd1 & (Hwellformedpd1s0 & HDisjointpdpd1s0)))))].
					unfold getFreeSlotsList in Hoptionfreeslotslistpd.
					unfold getFreeSlotsList in Hoptionfreeslotslistpd1.
					rewrite Hpdinsertions0 in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					rewrite HnewBFirstFrees0PDT in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
					rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
					destruct (beqAddr (firstfreeslot pd1entry) nullAddr) eqn:HfirstfreeNull ; try(exfalso ; congruence).
					(* firstfreeslot p <> NULL *)
					(* if first free of other PD is NOT NULL,
					then newB can't be in the two lists at s0 because of Disjoint -> False *)
					subst listoption2. subst listoption1.
					rewrite Hlookuppd1s0 in *.
					unfold Lib.disjoint in HDisjointpdpd1s0.
					specialize(HDisjointpdpd1s0 newBlockEntryAddr).
					destruct (HDisjointpdpd1s0).
					* subst optionfreeslotslistpd.
						rewrite FreeSlotsListRec_unroll.
						unfold getFreeSlotsListAux.
						assert(HmaxIdxNextEq :	maxIdx + 1 = S maxIdx) by apply MaxIdxNextEq.
						rewrite HmaxIdxNextEq.
						rewrite HlookupnewBs0.
						assert(HcurrNb : currnbfreeslots = nbfreeslots pdentry).
						{ unfold pdentryNbFreeSlots in *. rewrite Hpdinsertions0 in *. intuition. }
						rewrite <- HcurrNb in *.
						destruct (StateLib.Index.ltb currnbfreeslots zero) eqn:Hltb ; try(exfalso ; congruence).
						** unfold StateLib.Index.ltb in Hltb.
								apply PeanoNat.Nat.ltb_lt in Hltb.
								contradict Hltb. apply PeanoNat.Nat.lt_asymm. intuition.
						**	destruct (StateLib.Index.pred currnbfreeslots) eqn:Hpred ; try(exfalso ; congruence).
								cbn. intuition.
					* subst optionfreeslotslistpd1.
						destruct (beqAddr (firstfreeslot pd1entry) nullAddr) ; try(exfalso ; congruence).
						intuition.
}
	fold s1. fold s2. fold s3. fold s4. fold s5. fold s6. fold s7. fold s8.
	set (s9 := {| currentPartition := currentPartition ?s8; memory := _ |}).
	simpl in s7.
	assert(Hfreeslotss9 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd1entry) s9 (nbfreeslots pd1entry) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd1entry) s8 (nbfreeslots pd1entry)).
	{
		(* DUP *)
		apply getFreeSlotsListRecEqBE ; intuition.
		---	(* Lists are disjoint at s0, so newB <> firstfreeslot p *)
					destruct HDisjointpdpd1s0 as [optionfreeslotslistpd (optionfreeslotslistpd1 & (Hoptionfreeslotslistpd & (Hwellformedpds0 & (Hoptionfreeslotslistpd1 & (Hwellformedpd1s0 & HDisjointpdpd1s0)))))].

					unfold getFreeSlotsList in Hoptionfreeslotslistpd.
					unfold getFreeSlotsList in Hoptionfreeslotslistpd1.
					rewrite Hpdinsertions0 in *.
					rewrite Hlookuppd1s0 in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					assert(HnewBFirstFrees0P : firstfreeslot pd1entry = newBlockEntryAddr) by intuition.
					rewrite HnewBFirstFrees0PDT in *.
					rewrite HnewBFirstFrees0P in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
						rewrite FreeSlotsListRec_unroll in Hoptionfreeslotslistpd.
						rewrite FreeSlotsListRec_unroll in Hoptionfreeslotslistpd1.
						unfold getFreeSlotsListAux in *.
						induction (maxIdx+1). (* false induction because of fixpoint constraints *)
						** (* N=0 -> NotWellFormed *)
							rewrite Hoptionlist1s0 in *.
							cbn in Hwellformed1s0.
							congruence.
						** (* N>0 *)
							clear IHn.
							rewrite HlookupnewBs0 in *.
							destruct (StateLib.Index.ltb (nbfreeslots pdentry) zero) eqn:Hltb ; try(cbn in * ; congruence).
							destruct (StateLib.Index.ltb (nbfreeslots pd1entry) zero) eqn:Hltb' ; try(cbn in * ; congruence).
							destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred1 ; try(exfalso ; congruence).
							*** destruct (StateLib.Index.pred (nbfreeslots pd1entry)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
									**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd1.
												cbn in *.
												unfold Lib.disjoint in HDisjointpdpd1s0.
												specialize(HDisjointpdpd1s0 newBlockEntryAddr).
												simpl in HDisjointpdpd1s0.
												intuition.
									**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd1.
												cbn in *. congruence.
							*** destruct (StateLib.Index.pred (nbfreeslots pd1entry)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
									**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd1.
												cbn in *.
												unfold Lib.disjoint in HDisjointpdpd1s0.
												specialize(HDisjointpdpd1s0 newBlockEntryAddr).
												simpl in HDisjointpdpd1s0.
												intuition.
									**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd1.
												cbn in *. congruence.
			--- unfold isBE. unfold s9. cbn.
					destruct (beqAddr pdinsertion newBlockEntryAddr) ; try(exfalso ; congruence).
					rewrite beqAddrTrue.
					cbn.
					repeat rewrite removeDupIdentity ; intuition.
			--- subst listoption1.
					rewrite <- Hfreeslotss1 in *. rewrite <- Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *.
					rewrite <- Hfreeslotss5 in *. rewrite <- Hfreeslotss6 in *.
					rewrite <- Hfreeslotss7 in *. rewrite <- Hfreeslotss8 in *. intuition.
			--- assert(H_NoDups0 : NoDupInFreeSlotsList s0)
							by (unfold consistency in * ; intuition).
					unfold NoDupInFreeSlotsList in *.
					specialize (H_NoDups0 pd1 pd1entry Hlookuppd1s0).
					destruct H_NoDups0 as [optionlist1 (Hoptionlist1 & HwellFormed1' & HNoDup1)].
					unfold getFreeSlotsList in Hoptionlist1.
					rewrite Hlookuppd1s0 in *.
					destruct (beqAddr (firstfreeslot pd1entry) nullAddr)  ; try(exfalso ; congruence).
					subst optionlist1. subst listoption1.
					rewrite Hfreeslotss1 in *. rewrite Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *.
					rewrite <- Hfreeslotss5 in *. rewrite <- Hfreeslotss6 in *.
					rewrite <- Hfreeslotss7 in *. rewrite <- Hfreeslotss8 in *. intuition.
			--- rewrite <- Hfreeslotss8 in *. rewrite <- Hfreeslotss7 in *.
					rewrite <- Hfreeslotss6 in *. rewrite <- Hfreeslotss5 in *.
					rewrite <- Hfreeslotss4 in *. rewrite <- Hfreeslotss3 in *.
					rewrite Hfreeslotss2 in *. rewrite Hfreeslotss1 in *.
					(* newB is in freeslots list of pdinsertion, so can't be in other list
							because of Disjoint *)
					(* DUP from previous step *)
					destruct HDisjointpdpd1s0 as [optionfreeslotslistpd (optionfreeslotslistpd1 & (Hoptionfreeslotslistpd & (Hwellformedpds0 & (Hoptionfreeslotslistpd1 & (Hwellformedpd1s0 & HDisjointpdpd1s0)))))].
					unfold getFreeSlotsList in Hoptionfreeslotslistpd.
					unfold getFreeSlotsList in Hoptionfreeslotslistpd1.
					rewrite Hpdinsertions0 in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					rewrite HnewBFirstFrees0PDT in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
					rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
					destruct (beqAddr (firstfreeslot pd1entry) nullAddr) eqn:HfirstfreeNull ; try(exfalso ; congruence).
					(* firstfreeslot p <> NULL *)
					(* if first free of other PD is NOT NULL,
					then newB can't be in the two lists at s0 because of Disjoint -> False *)
					subst listoption2. subst listoption1.
					rewrite Hlookuppd1s0 in *.
					unfold Lib.disjoint in HDisjointpdpd1s0.
					specialize(HDisjointpdpd1s0 newBlockEntryAddr).
					destruct (HDisjointpdpd1s0).
					* subst optionfreeslotslistpd.
						rewrite FreeSlotsListRec_unroll.
						unfold getFreeSlotsListAux.
						assert(HmaxIdxNextEq :	maxIdx + 1 = S maxIdx) by apply MaxIdxNextEq.
						rewrite HmaxIdxNextEq.
						rewrite HlookupnewBs0.
						assert(HcurrNb : currnbfreeslots = nbfreeslots pdentry).
						{ unfold pdentryNbFreeSlots in *. rewrite Hpdinsertions0 in *. intuition. }
						rewrite <- HcurrNb in *.
						destruct (StateLib.Index.ltb currnbfreeslots zero) eqn:Hltb ; try(exfalso ; congruence).
						** unfold StateLib.Index.ltb in Hltb.
								apply PeanoNat.Nat.ltb_lt in Hltb.
								contradict Hltb. apply PeanoNat.Nat.lt_asymm. intuition.
						**	destruct (StateLib.Index.pred currnbfreeslots) eqn:Hpred ; try(exfalso ; congruence).
								cbn. intuition.
					* subst optionfreeslotslistpd1.
						destruct (beqAddr (firstfreeslot pd1entry) nullAddr) ; try(exfalso ; congruence).
						intuition.
}
	fold s1. fold s2. fold s3. fold s4. fold s5. fold s6. fold s7. fold s8. fold s9.
	set (s10 := {| currentPartition := currentPartition ?s9; memory := _ |}).
	simpl in s8. simpl in s9.
	assert(Hfreeslotss10 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd1entry) s10 (nbfreeslots pd1entry) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd1entry) s9 (nbfreeslots pd1entry)).
	{			assert(HSCEs9 : isSCE sceaddr s9).
				{ unfold isSCE. unfold s9. cbn. rewrite beqAddrTrue.
					destruct (beqAddr newBlockEntryAddr sceaddr) eqn:Hf ; try(exfalso ; congruence).
					rewrite <- beqAddrFalse in *.
					repeat rewrite removeDupIdentity ; intuition.
					destruct (beqAddr pdinsertion newBlockEntryAddr) eqn:Hff ; try(exfalso ; congruence).
					rewrite <- DependentTypeLemmas.beqAddrTrue in Hff. congruence.
					cbn.
					destruct (beqAddr pdinsertion sceaddr) eqn:Hfff ; try(exfalso ; congruence).
					rewrite <- DependentTypeLemmas.beqAddrTrue in Hfff. congruence.
					rewrite beqAddrTrue.
					rewrite <- beqAddrFalse in *.
					repeat rewrite removeDupIdentity ; intuition.
				}
				apply getFreeSlotsListRecEqSCE.
				--- 	intro Hfirstsceeq.
						assert(HFirstFreeSlotPointerIsBEAndFreeSlots0 : FirstFreeSlotPointerIsBEAndFreeSlot s0)
							by (unfold consistency in * ; intuition).
						unfold FirstFreeSlotPointerIsBEAndFreeSlot in *.
						specialize (HFirstFreeSlotPointerIsBEAndFreeSlots0 pd1 pd1entry Hlookuppd1s0).
						destruct HFirstFreeSlotPointerIsBEAndFreeSlots0.
						---- intro HfirstfreeNull.
								assert(HnullAddrExistss0 : nullAddrExists s0)
									by (unfold consistency in * ; intuition).
								unfold nullAddrExists in *.
								unfold isSCE in *.
								unfold isPADDR in *.
								rewrite HfirstfreeNull in *. rewrite <- Hfirstsceeq in *.
								destruct (lookup nullAddr (memory s0) beqAddr) ; try(exfalso ; congruence).
								destruct v ; try(exfalso ; congruence).
						---- rewrite Hfirstsceeq in *.
								unfold isSCE in *.
								unfold isBE in *.
								destruct (lookup sceaddr (memory s0) beqAddr) ; try (exfalso ; congruence).
								destruct v ; try(exfalso ; congruence).
				--- unfold isBE. unfold isSCE in HSCEs9.
						destruct (lookup sceaddr (memory s9) beqAddr) eqn:Hlookupsces9 ; try(exfalso ; congruence).
						destruct v ; try(exfalso ; congruence).
						intuition.
				--- unfold isPADDR. unfold isSCE in HSCEs9.
						destruct (lookup sceaddr (memory s9) beqAddr) eqn:Hlookupsces9 ; try(exfalso ; congruence).
						destruct v ; try(exfalso ; congruence).
						intuition.
}
	fold s1. fold s2. fold s3. fold s4. fold s5. fold s6. fold s7. fold s8. fold s9.
	fold s10.

	intuition.
	assert(HcurrLtmaxIdx : nbfreeslots pd1entry <= maxIdx).
	{ intuition. apply IdxLtMaxIdx. }
	lia.
}
														destruct Hfreeslotspd1Eq as [s1 (s2 & (s3 & (s4 & (s5 & (s6 & (s7 & (s8 & (s9 & (s10 &
																													(n1 & (nbleft & (Hnbleft & Hstates))))))))))))].
														assert(HsEq : s10 = s).
														{ intuition. subst s1. subst s2. subst s3. subst s4. subst s5. subst s6.
															subst s7. subst s8. subst s9. subst s10.
															rewrite Hs. f_equal.
														}
														rewrite HsEq in *.
														assert(HfreeslotsEq : getFreeSlotsListRec n1 (firstfreeslot pd1entry) s (nbfreeslots pd1entry) =
																									getFreeSlotsListRec (maxIdx+1) (firstfreeslot pd1entry) s0 (nbfreeslots pd1entry)).
														{
															intuition.
															subst nbleft.
															(* rewrite all previous getFreeSlotsListRec equalities *)
															rewrite <- H33. rewrite <- H36. rewrite <- H38.
															rewrite <- H40. rewrite <- H42. rewrite <- H44.
															rewrite <- H46. rewrite <- H48. rewrite <- H50.
															rewrite <- H53.
															reflexivity.
														}
														assert (HfreeslotsEqn1 : getFreeSlotsListRec n1 (firstfreeslot pd1entry) s (nbfreeslots pd1entry)
																											= getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd1entry) s (nbfreeslots pd1entry)).
														{ eapply getFreeSlotsListRecEqN ; intuition.
															subst nbleft. lia.
															assert (HnbLtmaxIdx : nbfreeslots pd1entry <= maxIdx) by apply IdxLtMaxIdx.
															lia.
														}
														(* specialize disjoint for pd1 and pd2 at s0 *)
														assert(HDisjointpd1pd2s0 : DisjointFreeSlotsLists s0)
															by (unfold consistency in * ; intuition).
														unfold DisjointFreeSlotsLists in *.
														assert(HPDTpd1s0 : isPDT pd1 s0) by (unfold isPDT ; rewrite Hlookuppd1s0 ; intuition).
														specialize (HDisjointpd1pd2s0 pd1 pd2 HPDTpd1s0 HPDTpd2s0 Hpd1pd2NotEq).
														apply isPDTLookupEq in HPDTpd2s0. destruct HPDTpd2s0 as [pd2entry Hlookuppd2s0].

														destruct HDisjointpd1pd2s0 as [optionfreeslotslistpd1 (optionfreeslotslistpd2 & (Hoptionfreeslotslistpd1 & (Hwellformedpd1s0 & (Hoptionfreeslotslistpd2 & (Hwellformedpd2s0 & HDisjointpd1pd2s0)))))].
														(* we expect identical lists at s0 and s *)
														exists optionfreeslotslistpd1. exists optionfreeslotslistpd2.
														unfold getFreeSlotsList.
														unfold getFreeSlotsList in Hoptionfreeslotslistpd1.
														unfold getFreeSlotsList in Hoptionfreeslotslistpd2.
														rewrite Hlookuppd1Eq. rewrite Hlookuppd2Eq.
														rewrite Hlookuppd1s0 in *.
														rewrite Hlookuppd2s0 in *.
														destruct (beqAddr (firstfreeslot pd1entry) nullAddr) eqn:HfirstfreeNullpd1 ; try(exfalso ; congruence).
														destruct (beqAddr (firstfreeslot pd2entry) nullAddr) eqn:HfirstfreeNullpd2 ; try(exfalso ; congruence).
														+ (* listoption2 = NIL *)
															(* always disjoint with nil *)
															subst optionfreeslotslistpd1.
															intuition.
															(* we are in the case listoption1 is equal at s and s0 *)
															rewrite <- HfreeslotsEqn1. subst nbleft.
															rewrite H53. rewrite H50. rewrite H48. rewrite H46.
															rewrite H44. rewrite H42. rewrite H40. rewrite H38.
															rewrite H36. rewrite H33.
															reflexivity.
														+ (* listoption2 = NIL *)
															(* show list equality for listoption2 *)
															subst optionfreeslotslistpd1. subst optionfreeslotslistpd2.
															intuition.
															rewrite <- HfreeslotsEqn1. subst nbleft.
															rewrite H53. rewrite H50. rewrite H48. rewrite H46.
															rewrite H44. rewrite H42. rewrite H40. rewrite H38.
															rewrite H36. rewrite H33.
															reflexivity.

															(* state already cut into intermediate states *)
															assert(Hfreeslotspd2Eq : exists n1 nbleft,
nbleft = (nbfreeslots pd2entry) /\
getFreeSlotsListRec n1 (firstfreeslot pd2entry) s1 nbleft =
getFreeSlotsListRec (maxIdx+1) (firstfreeslot pd2entry) s0 nbleft
			 /\
	n1 <= maxIdx+1 /\ nbleft < n1
/\
getFreeSlotsListRec n1 (firstfreeslot pd2entry) s2 nbleft =
			getFreeSlotsListRec n1 (firstfreeslot pd2entry) s1 nbleft
/\
getFreeSlotsListRec n1 (firstfreeslot pd2entry) s3 nbleft =
			getFreeSlotsListRec n1 (firstfreeslot pd2entry) s2 nbleft
/\
getFreeSlotsListRec n1 (firstfreeslot pd2entry) s4 nbleft =
			getFreeSlotsListRec n1 (firstfreeslot pd2entry) s3 nbleft
/\
getFreeSlotsListRec n1 (firstfreeslot pd2entry) s5 nbleft =
			getFreeSlotsListRec n1 (firstfreeslot pd2entry) s4 nbleft
/\
getFreeSlotsListRec n1 (firstfreeslot pd2entry) s6 nbleft =
			getFreeSlotsListRec n1 (firstfreeslot pd2entry) s5 nbleft
/\
getFreeSlotsListRec n1 (firstfreeslot pd2entry) s7 nbleft =
			getFreeSlotsListRec n1 (firstfreeslot pd2entry) s6 nbleft
/\
getFreeSlotsListRec n1(firstfreeslot pd2entry) s8 nbleft =
			getFreeSlotsListRec n1 (firstfreeslot pd2entry) s7 nbleft
/\
getFreeSlotsListRec n1 (firstfreeslot pd2entry) s9 nbleft =
			getFreeSlotsListRec n1 (firstfreeslot pd2entry) s8 nbleft
/\
getFreeSlotsListRec n1 (firstfreeslot pd2entry) s10 nbleft =
			getFreeSlotsListRec n1 (firstfreeslot pd2entry) s9 nbleft
).
{
	eexists ?[n1]. eexists.
	split. intuition.
	(* prove outside *)
	assert(Hfreeslotss1 : getFreeSlotsListRec ?n1 (firstfreeslot pd2entry) s1 (nbfreeslots pd2entry) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s0 (nbfreeslots pd2entry)).
	{	subst s1.
		apply getFreeSlotsListRecEqPDT.
		-- 	intro Hfirstpdeq.
				assert(HFirstFreeSlotPointerIsBEAndFreeSlots0 : FirstFreeSlotPointerIsBEAndFreeSlot s0)
					by (unfold consistency in * ; intuition).
				unfold FirstFreeSlotPointerIsBEAndFreeSlot in *.
				specialize (HFirstFreeSlotPointerIsBEAndFreeSlots0 pd2 pd2entry Hlookuppd2s0).
				destruct HFirstFreeSlotPointerIsBEAndFreeSlots0.
				--- intro HfirstfreeNull.
						assert(HnullAddrExistss0 : nullAddrExists s0)
							by (unfold consistency in * ; intuition).
						unfold nullAddrExists in *.
						unfold isPADDR in *.
						rewrite HfirstfreeNull in *. rewrite <- Hfirstpdeq in *.
						destruct (lookup nullAddr (memory s0) beqAddr) ; try(exfalso ; congruence).
						destruct v ; try(exfalso ; congruence).
				--- rewrite Hfirstpdeq in *.
						unfold isBE in *.
						destruct (lookup pdinsertion (memory s0) beqAddr) ; try (exfalso ; congruence).
						destruct v ; try(exfalso ; congruence).
		-- unfold isBE. rewrite Hpdinsertions0. intuition.
		-- unfold isPADDR. rewrite Hpdinsertions0. intuition.
	}
	assert(Hfreeslotss2 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s2 (nbfreeslots pd2entry) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s1 (nbfreeslots pd2entry)).
	{ subst s2.
				apply getFreeSlotsListRecEqPDT.
				--- 	intro Hfirstpdeq.
						assert(HFirstFreeSlotPointerIsBEAndFreeSlots0 : FirstFreeSlotPointerIsBEAndFreeSlot s0)
							by (unfold consistency in * ; intuition).
						unfold FirstFreeSlotPointerIsBEAndFreeSlot in *.
						specialize (HFirstFreeSlotPointerIsBEAndFreeSlots0 pd2 pd2entry Hlookuppd2s0).
						destruct HFirstFreeSlotPointerIsBEAndFreeSlots0.
						---- intro HfirstfreeNull.
								assert(HnullAddrExistss0 : nullAddrExists s0)
									by (unfold consistency in * ; intuition).
								unfold nullAddrExists in *.
								unfold isPADDR in *.
								rewrite HfirstfreeNull in *. rewrite <- Hfirstpdeq in *.
								destruct (lookup nullAddr (memory s0) beqAddr) ; try(exfalso ; congruence).
								destruct v ; try(exfalso ; congruence).
						---- rewrite Hfirstpdeq in *.
								unfold isBE in *.
								destruct (lookup pdinsertion (memory s0) beqAddr) ; try (exfalso ; congruence).
								destruct v ; try(exfalso ; congruence).
				--- unfold isBE. subst s1. cbn. rewrite beqAddrTrue. intuition.
				--- unfold isPADDR. subst s1. cbn. rewrite beqAddrTrue. intuition.
	}
	assert(Hfreeslotss3 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s3 (nbfreeslots pd2entry) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s2 (nbfreeslots pd2entry)).
	{	subst s3.
				apply getFreeSlotsListRecEqBE ; intuition.
				---	(* Lists are disjoint at s0, so newB <> firstfreeslot pd2entry *)
							destruct HDisjointpdpd2s0 as [optionfreeslotslistpd (optionfreeslotslistpd2 & (Hoptionfreeslotslistpd & (Hwellformedpds0 & (Hoptionfreeslotslistpd2 & (Hwellformedpd2s0' & HDisjointpdpd2s0)))))].

							unfold getFreeSlotsList in Hoptionfreeslotslistpd.
							unfold getFreeSlotsList in Hoptionfreeslotslistpd2.
							rewrite Hpdinsertions0 in *.
							rewrite Hlookuppd2s0 in *.
							assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
							{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
							assert(HnewBFirstFrees0P : firstfreeslot pd2entry = newBlockEntryAddr) by intuition.
							rewrite HnewBFirstFrees0PDT in *.
							rewrite HnewBFirstFrees0P in *.
							destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
								rewrite FreeSlotsListRec_unroll in Hoptionfreeslotslistpd.
								rewrite FreeSlotsListRec_unroll in Hoptionfreeslotslistpd2.
								unfold getFreeSlotsListAux in *.
								induction (maxIdx+1). (* false induction because of fixpoint constraints *)
								** (* N=0 -> NotWellFormed *)
									rewrite Hoptionlist1s0 in *.
									cbn in Hwellformed1s0.
									congruence.
								** (* N>0 *)
									clear IHn.
									rewrite HlookupnewBs0 in *.
									destruct (StateLib.Index.ltb (nbfreeslots pdentry) zero) eqn:Hltb ; try(cbn in * ; congruence).
									destruct (StateLib.Index.ltb (nbfreeslots pd2entry) zero) eqn:Hltb' ; try(cbn in * ; congruence).
									destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred1 ; try(exfalso ; congruence).
									*** destruct (StateLib.Index.pred (nbfreeslots pd2entry)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
											**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd2.
														cbn in *.
														unfold Lib.disjoint in HDisjointpdpd2s0.
														specialize(HDisjointpdpd2s0 newBlockEntryAddr).
														simpl in HDisjointpdpd2s0.
														intuition.
											**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd2.
														cbn in *. congruence.
									*** destruct (StateLib.Index.pred (nbfreeslots pd2entry)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
											**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd2.
														cbn in *.
														unfold Lib.disjoint in HDisjointpdpd2s0.
														specialize(HDisjointpdpd2s0 newBlockEntryAddr).
														simpl in HDisjointpdpd2s0.
														intuition.
											**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd2.
														cbn in *. congruence.
			--- unfold isBE. subst s2. subst s1. cbn.
					destruct (beqAddr pdinsertion newBlockEntryAddr) ; try(exfalso ; congruence).
					rewrite beqAddrTrue.
					cbn.
					repeat rewrite removeDupIdentity ; intuition.
			--- subst listoption2.
					rewrite <- Hfreeslotss1 in *. rewrite <- Hfreeslotss2 in *. intuition.
			--- assert(H_NoDups0 : NoDupInFreeSlotsList s0)
							by (unfold consistency in * ; intuition).
					unfold NoDupInFreeSlotsList in *.
					specialize (H_NoDups0 pd2 pd2entry Hlookuppd2s0).
					destruct H_NoDups0 as [optionlist2 (Hoptionlist2 & HwellFormed2' & HNoDup2)].
					unfold getFreeSlotsList in Hoptionlist2.
					rewrite Hlookuppd2s0 in *.
					destruct (beqAddr (firstfreeslot pd2entry) nullAddr) eqn:Hpd2Null ; try(exfalso ; congruence).
					subst optionlist2. subst listoption2.
					rewrite Hfreeslotss1 in *. rewrite Hfreeslotss2 in *. intuition.
			--- rewrite Hfreeslotss2 in *. rewrite Hfreeslotss1 in *.
					(* newB is in freeslots list of pdinsertion, so can't be in other list
							because of Disjoint *)
					(* DUP from previous step *)
					destruct HDisjointpdpd2s0 as [optionfreeslotslistpd (optionfreeslotslistpd2 & (Hoptionfreeslotslistpd & (Hwellformedpds0 & (Hoptionfreeslotslistpd2 & (Hwellformedpd2s0' & HDisjointpdpd2s0)))))].
					unfold getFreeSlotsList in Hoptionfreeslotslistpd.
					unfold getFreeSlotsList in Hoptionfreeslotslistpd2.
					rewrite Hpdinsertions0 in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					rewrite HnewBFirstFrees0PDT in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
					rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
					destruct (beqAddr (firstfreeslot pd2entry) nullAddr) eqn:HfirstfreeNull ; try(exfalso ; congruence).
					(* firstfreeslot p <> NULL *)
					(* if first free of other PD is NOT NULL,
					then newB can't be in the two lists at s0 because of Disjoint -> False *)
					subst listoption2. subst listoption1.
					unfold Lib.disjoint in HDisjointpdpd2s0.
					specialize(HDisjointpdpd2s0 newBlockEntryAddr).
					destruct (HDisjointpdpd2s0).
					* subst optionfreeslotslistpd.
						rewrite FreeSlotsListRec_unroll.
						unfold getFreeSlotsListAux.
						assert(HmaxIdxNextEq :	maxIdx + 1 = S maxIdx) by apply MaxIdxNextEq.
						rewrite HmaxIdxNextEq.
						rewrite HlookupnewBs0.
						assert(HcurrNb : currnbfreeslots = nbfreeslots pdentry).
						{ unfold pdentryNbFreeSlots in *. rewrite Hpdinsertions0 in *. intuition. }
						rewrite <- HcurrNb in *.
						destruct (StateLib.Index.ltb currnbfreeslots zero) eqn:Hltb ; try(exfalso ; congruence).
						** unfold StateLib.Index.ltb in Hltb.
								apply PeanoNat.Nat.ltb_lt in Hltb.
								contradict Hltb. apply PeanoNat.Nat.lt_asymm. intuition.
						**	destruct (StateLib.Index.pred currnbfreeslots) eqn:Hpred ; try(exfalso ; congruence).
								cbn. intuition.
					* subst optionfreeslotslistpd2. rewrite Hlookuppd2s0.
						destruct (beqAddr (firstfreeslot pd2entry) nullAddr) ; try(exfalso ; congruence).
						intuition.
}
	simpl in s4. simpl in s3.
	assert(Hfreeslotss4 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s4 (nbfreeslots pd2entry) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s3 (nbfreeslots pd2entry)).
	{	subst s4.
		(* DUP *)
				apply getFreeSlotsListRecEqBE ; intuition.
				---	(* Lists are disjoint at s0, so newB <> firstfreeslot p *)
							destruct HDisjointpdpd2s0 as [optionfreeslotslistpd (optionfreeslotslistpd2 & (Hoptionfreeslotslistpd & (Hwellformedpds0 & (Hoptionfreeslotslistpd2 & (Hwellformedpd2s0' & HDisjointpdpd2s0)))))].

							unfold getFreeSlotsList in Hoptionfreeslotslistpd.
							unfold getFreeSlotsList in Hoptionfreeslotslistpd2.
							rewrite Hpdinsertions0 in *.
							rewrite Hlookuppd2s0 in *.
							assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
							{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
							assert(HnewBFirstFrees0P : firstfreeslot pd2entry = newBlockEntryAddr) by intuition.
							rewrite HnewBFirstFrees0PDT in *.
							rewrite HnewBFirstFrees0P in *.
							destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
								rewrite FreeSlotsListRec_unroll in Hoptionfreeslotslistpd.
								rewrite FreeSlotsListRec_unroll in Hoptionfreeslotslistpd2.
								unfold getFreeSlotsListAux in *.
								induction (maxIdx+1). (* false induction because of fixpoint constraints *)
								** (* N=0 -> NotWellFormed *)
									rewrite Hoptionlist1s0 in *.
									cbn in Hwellformed1s0.
									congruence.
								** (* N>0 *)
									clear IHn.
									rewrite HlookupnewBs0 in *.
									destruct (StateLib.Index.ltb (nbfreeslots pdentry) zero) eqn:Hltb ; try(cbn in * ; congruence).
									destruct (StateLib.Index.ltb (nbfreeslots pd2entry) zero) eqn:Hltb' ; try(cbn in * ; congruence).
									destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred1 ; try(exfalso ; congruence).
									*** destruct (StateLib.Index.pred (nbfreeslots pd2entry)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
											**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd2.
														cbn in *.
														unfold Lib.disjoint in HDisjointpdpd2s0.
														specialize(HDisjointpdpd2s0 newBlockEntryAddr).
														simpl in HDisjointpdpd2s0.
														intuition.
											**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd2.
														cbn in *. congruence.
									*** destruct (StateLib.Index.pred (nbfreeslots pd2entry)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
											**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd2.
														cbn in *.
														unfold Lib.disjoint in HDisjointpdpd2s0.
														specialize(HDisjointpdpd2s0 newBlockEntryAddr).
														simpl in HDisjointpdpd2s0.
														intuition.
											**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd2.
														cbn in *. congruence.
			--- unfold isBE. subst s3. subst s2. subst s1. cbn.
					destruct (beqAddr pdinsertion newBlockEntryAddr) ; try(exfalso ; congruence).
					rewrite beqAddrTrue.
					cbn.
					repeat rewrite removeDupIdentity ; intuition.
			--- subst listoption2.
					rewrite <- Hfreeslotss1 in *. rewrite <- Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. intuition.
			--- assert(H_NoDups0 : NoDupInFreeSlotsList s0)
							by (unfold consistency in * ; intuition).
					unfold NoDupInFreeSlotsList in *.
					specialize (H_NoDups0 pd2 pd2entry Hlookuppd2s0).
					destruct H_NoDups0 as [optionlist2 (Hoptionlist2 & HwellFormed2' & HNoDup2)].
					unfold getFreeSlotsList in Hoptionlist2.
					rewrite Hlookuppd2s0 in *.
					destruct (beqAddr (firstfreeslot pd2entry) nullAddr) eqn:Hpd2Null ; try(exfalso ; congruence).
					subst optionlist2. subst listoption2.
					rewrite Hfreeslotss1 in *. rewrite Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. intuition.
			--- rewrite <- Hfreeslotss3 in *.
					rewrite Hfreeslotss2 in *. rewrite Hfreeslotss1 in *.
					(* newB is in freeslots list of pdinsertion, so can't be in other list
							because of Disjoint *)
					(* DUP from previous step *)
					destruct HDisjointpdpd2s0 as [optionfreeslotslistpd (optionfreeslotslistpd2 & (Hoptionfreeslotslistpd & (Hwellformedpds0 & (Hoptionfreeslotslistpd2 & (Hwellformedpd2s0' & HDisjointpdpd2s0)))))].
					unfold getFreeSlotsList in Hoptionfreeslotslistpd.
					unfold getFreeSlotsList in Hoptionfreeslotslistpd2.
					rewrite Hpdinsertions0 in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					rewrite HnewBFirstFrees0PDT in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
					rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
					destruct (beqAddr (firstfreeslot pd2entry) nullAddr) eqn:HfirstfreeNull ; try(exfalso ; congruence).
					(* firstfreeslot p <> NULL *)
					(* if first free of other PD is NOT NULL,
					then newB can't be in the two lists at s0 because of Disjoint -> False *)
					subst listoption2. subst listoption1.
					unfold Lib.disjoint in HDisjointpdpd2s0.
					specialize(HDisjointpdpd2s0 newBlockEntryAddr).
					destruct (HDisjointpdpd2s0).
					* subst optionfreeslotslistpd.
						rewrite FreeSlotsListRec_unroll.
						unfold getFreeSlotsListAux.
						assert(HmaxIdxNextEq :	maxIdx + 1 = S maxIdx) by apply MaxIdxNextEq.
						rewrite HmaxIdxNextEq.
						rewrite HlookupnewBs0.
						assert(HcurrNb : currnbfreeslots = nbfreeslots pdentry).
						{ unfold pdentryNbFreeSlots in *. rewrite Hpdinsertions0 in *. intuition. }
						rewrite <- HcurrNb in *.
						destruct (StateLib.Index.ltb currnbfreeslots zero) eqn:Hltb ; try(exfalso ; congruence).
						** unfold StateLib.Index.ltb in Hltb.
								apply PeanoNat.Nat.ltb_lt in Hltb.
								contradict Hltb. apply PeanoNat.Nat.lt_asymm. intuition.
						**	destruct (StateLib.Index.pred currnbfreeslots) eqn:Hpred ; try(exfalso ; congruence).
								cbn. intuition.
					* subst optionfreeslotslistpd2. rewrite Hlookuppd2s0.
						destruct (beqAddr (firstfreeslot pd2entry) nullAddr) ; try(exfalso ; congruence).
						intuition.
}
	simpl in s4.
	assert(Hfreeslotss5 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s5 (nbfreeslots pd2entry) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s4 (nbfreeslots pd2entry)).
	{	subst s5.
		(* DUP *)
				apply getFreeSlotsListRecEqBE ; intuition.
				---	(* Lists are disjoint at s0, so newB <> firstfreeslot p *)
							destruct HDisjointpdpd2s0 as [optionfreeslotslistpd (optionfreeslotslistpd2 & (Hoptionfreeslotslistpd & (Hwellformedpds0 & (Hoptionfreeslotslistpd2 & (Hwellformedpd2s0' & HDisjointpdpd2s0)))))].

							unfold getFreeSlotsList in Hoptionfreeslotslistpd.
							unfold getFreeSlotsList in Hoptionfreeslotslistpd2.
							rewrite Hpdinsertions0 in *.
							rewrite Hlookuppd2s0 in *.
							assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
							{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
							assert(HnewBFirstFrees0P : firstfreeslot pd2entry = newBlockEntryAddr) by intuition.
							rewrite HnewBFirstFrees0PDT in *.
							rewrite HnewBFirstFrees0P in *.
							destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
								rewrite FreeSlotsListRec_unroll in Hoptionfreeslotslistpd.
								rewrite FreeSlotsListRec_unroll in Hoptionfreeslotslistpd2.
								unfold getFreeSlotsListAux in *.
								induction (maxIdx+1). (* false induction because of fixpoint constraints *)
								** (* N=0 -> NotWellFormed *)
									rewrite Hoptionlist1s0 in *.
									cbn in Hwellformed1s0.
									congruence.
								** (* N>0 *)
									clear IHn.
									rewrite HlookupnewBs0 in *.
									destruct (StateLib.Index.ltb (nbfreeslots pdentry) zero) eqn:Hltb ; try(cbn in * ; congruence).
									destruct (StateLib.Index.ltb (nbfreeslots pd2entry) zero) eqn:Hltb' ; try(cbn in * ; congruence).
									destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred1 ; try(exfalso ; congruence).
									*** destruct (StateLib.Index.pred (nbfreeslots pd2entry)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
											**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd2.
														cbn in *.
														unfold Lib.disjoint in HDisjointpdpd2s0.
														specialize(HDisjointpdpd2s0 newBlockEntryAddr).
														simpl in HDisjointpdpd2s0.
														intuition.
											**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd2.
														cbn in *. congruence.
									*** destruct (StateLib.Index.pred (nbfreeslots pd2entry)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
											**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd2.
														cbn in *.
														unfold Lib.disjoint in HDisjointpdpd2s0.
														specialize(HDisjointpdpd2s0 newBlockEntryAddr).
														simpl in HDisjointpdpd2s0.
														intuition.
											**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd2.
														cbn in *. congruence.
			--- unfold isBE. subst s4. subst s3. subst s2. subst s1. cbn.
					destruct (beqAddr pdinsertion newBlockEntryAddr) ; try(exfalso ; congruence).
					rewrite beqAddrTrue.
					cbn.
					repeat rewrite removeDupIdentity ; intuition.
			--- subst listoption2.
					rewrite <- Hfreeslotss1 in *. rewrite <- Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *. intuition.
			--- assert(H_NoDups0 : NoDupInFreeSlotsList s0)
							by (unfold consistency in * ; intuition).
					unfold NoDupInFreeSlotsList in *.
					specialize (H_NoDups0 pd2 pd2entry Hlookuppd2s0).
					destruct H_NoDups0 as [optionlist2 (Hoptionlist2 & HwellFormed2' & HNoDup2)].
					unfold getFreeSlotsList in Hoptionlist2.
					rewrite Hlookuppd2s0 in *.
					destruct (beqAddr (firstfreeslot pd2entry) nullAddr) eqn:Hpd2Null ; try(exfalso ; congruence).
					subst optionlist2. subst listoption2.
					rewrite Hfreeslotss1 in *. rewrite Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *. intuition.
			--- rewrite <- Hfreeslotss4 in *. rewrite <- Hfreeslotss3 in *.
					rewrite Hfreeslotss2 in *. rewrite Hfreeslotss1 in *.
					(* newB is in freeslots list of pdinsertion, so can't be in other list
							because of Disjoint *)
					(* DUP from previous step *)
					destruct HDisjointpdpd2s0 as [optionfreeslotslistpd (optionfreeslotslistpd2 & (Hoptionfreeslotslistpd & (Hwellformedpds0 & (Hoptionfreeslotslistpd2 & (Hwellformedpd2s0' & HDisjointpdpd2s0)))))].
					unfold getFreeSlotsList in Hoptionfreeslotslistpd.
					unfold getFreeSlotsList in Hoptionfreeslotslistpd2.
					rewrite Hpdinsertions0 in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					rewrite HnewBFirstFrees0PDT in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
					rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
					destruct (beqAddr (firstfreeslot pd2entry) nullAddr) eqn:HfirstfreeNull ; try(exfalso ; congruence).
					(* firstfreeslot p <> NULL *)
					(* if first free of other PD is NOT NULL,
					then newB can't be in the two lists at s0 because of Disjoint -> False *)
					subst listoption2. subst listoption1.
					unfold Lib.disjoint in HDisjointpdpd2s0.
					specialize(HDisjointpdpd2s0 newBlockEntryAddr).
					destruct (HDisjointpdpd2s0).
					* subst optionfreeslotslistpd.
						rewrite FreeSlotsListRec_unroll.
						unfold getFreeSlotsListAux.
						assert(HmaxIdxNextEq :	maxIdx + 1 = S maxIdx) by apply MaxIdxNextEq.
						rewrite HmaxIdxNextEq.
						rewrite HlookupnewBs0.
						assert(HcurrNb : currnbfreeslots = nbfreeslots pdentry).
						{ unfold pdentryNbFreeSlots in *. rewrite Hpdinsertions0 in *. intuition. }
						rewrite <- HcurrNb in *.
						destruct (StateLib.Index.ltb currnbfreeslots zero) eqn:Hltb ; try(exfalso ; congruence).
						** unfold StateLib.Index.ltb in Hltb.
								apply PeanoNat.Nat.ltb_lt in Hltb.
								contradict Hltb. apply PeanoNat.Nat.lt_asymm. intuition.
						**	destruct (StateLib.Index.pred currnbfreeslots) eqn:Hpred ; try(exfalso ; congruence).
								cbn. intuition.
					* subst optionfreeslotslistpd2. rewrite Hlookuppd2s0.
						destruct (beqAddr (firstfreeslot pd2entry) nullAddr) ; try(exfalso ; congruence).
						intuition.
}
	simpl in s4.
	assert(Hfreeslotss6 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s6 (nbfreeslots pd2entry) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s5 (nbfreeslots pd2entry)).
	{	subst s6.
		(* DUP *)
				apply getFreeSlotsListRecEqBE ; intuition.
				---	(* Lists are disjoint at s0, so newB <> firstfreeslot p *)
							destruct HDisjointpdpd2s0 as [optionfreeslotslistpd (optionfreeslotslistpd2 & (Hoptionfreeslotslistpd & (Hwellformedpds0 & (Hoptionfreeslotslistpd2 & (Hwellformedpd2s0' & HDisjointpdpd2s0)))))].

							unfold getFreeSlotsList in Hoptionfreeslotslistpd.
							unfold getFreeSlotsList in Hoptionfreeslotslistpd2.
							rewrite Hpdinsertions0 in *.
							rewrite Hlookuppd2s0 in *.
							assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
							{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
							assert(HnewBFirstFrees0P : firstfreeslot pd2entry = newBlockEntryAddr) by intuition.
							rewrite HnewBFirstFrees0PDT in *.
							rewrite HnewBFirstFrees0P in *.
							destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
								rewrite FreeSlotsListRec_unroll in Hoptionfreeslotslistpd.
								rewrite FreeSlotsListRec_unroll in Hoptionfreeslotslistpd2.
								unfold getFreeSlotsListAux in *.
								induction (maxIdx+1). (* false induction because of fixpoint constraints *)
								** (* N=0 -> NotWellFormed *)
									rewrite Hoptionlist1s0 in *.
									cbn in Hwellformed1s0.
									congruence.
								** (* N>0 *)
									clear IHn.
									rewrite HlookupnewBs0 in *.
									destruct (StateLib.Index.ltb (nbfreeslots pdentry) zero) eqn:Hltb ; try(cbn in * ; congruence).
									destruct (StateLib.Index.ltb (nbfreeslots pd2entry) zero) eqn:Hltb' ; try(cbn in * ; congruence).
									destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred1 ; try(exfalso ; congruence).
									*** destruct (StateLib.Index.pred (nbfreeslots pd2entry)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
											**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd2.
														cbn in *.
														unfold Lib.disjoint in HDisjointpdpd2s0.
														specialize(HDisjointpdpd2s0 newBlockEntryAddr).
														simpl in HDisjointpdpd2s0.
														intuition.
											**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd2.
														cbn in *. congruence.
									*** destruct (StateLib.Index.pred (nbfreeslots pd2entry)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
											**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd2.
														cbn in *.
														unfold Lib.disjoint in HDisjointpdpd2s0.
														specialize(HDisjointpdpd2s0 newBlockEntryAddr).
														simpl in HDisjointpdpd2s0.
														intuition.
											**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd2.
														cbn in *. congruence.
			--- unfold isBE. subst s5. subst s4. subst s3. subst s2. subst s1. cbn.
					destruct (beqAddr pdinsertion newBlockEntryAddr) ; try(exfalso ; congruence).
					rewrite beqAddrTrue.
					cbn.
					repeat rewrite removeDupIdentity ; intuition.
			--- subst listoption2.
					rewrite <- Hfreeslotss1 in *. rewrite <- Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *.
					rewrite <- Hfreeslotss5 in *. intuition.
			--- assert(H_NoDups0 : NoDupInFreeSlotsList s0)
							by (unfold consistency in * ; intuition).
					unfold NoDupInFreeSlotsList in *.
					specialize (H_NoDups0 pd2 pd2entry Hlookuppd2s0).
					destruct H_NoDups0 as [optionlist2 (Hoptionlist2 & HwellFormed2' & HNoDup2)].
					unfold getFreeSlotsList in Hoptionlist2.
					rewrite Hlookuppd2s0 in *.
					destruct (beqAddr (firstfreeslot pd2entry) nullAddr) eqn:Hpd2Null ; try(exfalso ; congruence).
					subst optionlist2. subst listoption2.
					rewrite Hfreeslotss1 in *. rewrite Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *.
					rewrite <- Hfreeslotss5 in *. intuition.
			--- rewrite <- Hfreeslotss5 in *.
					rewrite <- Hfreeslotss4 in *. rewrite <- Hfreeslotss3 in *.
					rewrite Hfreeslotss2 in *. rewrite Hfreeslotss1 in *.
					(* newB is in freeslots list of pdinsertion, so can't be in other list
							because of Disjoint *)
					(* DUP from previous step *)
					destruct HDisjointpdpd2s0 as [optionfreeslotslistpd (optionfreeslotslistpd2 & (Hoptionfreeslotslistpd & (Hwellformedpds0 & (Hoptionfreeslotslistpd2 & (Hwellformedpd2s0' & HDisjointpdpd2s0)))))].
					unfold getFreeSlotsList in Hoptionfreeslotslistpd.
					unfold getFreeSlotsList in Hoptionfreeslotslistpd2.
					rewrite Hpdinsertions0 in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					rewrite HnewBFirstFrees0PDT in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
					rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
					destruct (beqAddr (firstfreeslot pd2entry) nullAddr) eqn:HfirstfreeNull ; try(exfalso ; congruence).
					(* firstfreeslot p <> NULL *)
					(* if first free of other PD is NOT NULL,
					then newB can't be in the two lists at s0 because of Disjoint -> False *)
					subst listoption2. subst listoption1.
					unfold Lib.disjoint in HDisjointpdpd2s0.
					specialize(HDisjointpdpd2s0 newBlockEntryAddr).
					destruct (HDisjointpdpd2s0).
					* subst optionfreeslotslistpd.
						rewrite FreeSlotsListRec_unroll.
						unfold getFreeSlotsListAux.
						assert(HmaxIdxNextEq :	maxIdx + 1 = S maxIdx) by apply MaxIdxNextEq.
						rewrite HmaxIdxNextEq.
						rewrite HlookupnewBs0.
						assert(HcurrNb : currnbfreeslots = nbfreeslots pdentry).
						{ unfold pdentryNbFreeSlots in *. rewrite Hpdinsertions0 in *. intuition. }
						rewrite <- HcurrNb in *.
						destruct (StateLib.Index.ltb currnbfreeslots zero) eqn:Hltb ; try(exfalso ; congruence).
						** unfold StateLib.Index.ltb in Hltb.
								apply PeanoNat.Nat.ltb_lt in Hltb.
								contradict Hltb. apply PeanoNat.Nat.lt_asymm. intuition.
						**	destruct (StateLib.Index.pred currnbfreeslots) eqn:Hpred ; try(exfalso ; congruence).
								cbn. intuition.
					* subst optionfreeslotslistpd2. rewrite Hlookuppd2s0.
						destruct (beqAddr (firstfreeslot pd2entry) nullAddr) ; try(exfalso ; congruence).
						intuition.
}
	simpl in s5. simpl in s6.
	assert(Hfreeslotss7 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s7 (nbfreeslots pd2entry) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s6 (nbfreeslots pd2entry)).
	{	subst s7.
		(* DUP *)
				apply getFreeSlotsListRecEqBE ; intuition.
				---	(* Lists are disjoint at s0, so newB <> firstfreeslot p *)
							destruct HDisjointpdpd2s0 as [optionfreeslotslistpd (optionfreeslotslistpd2 & (Hoptionfreeslotslistpd & (Hwellformedpds0 & (Hoptionfreeslotslistpd2 & (Hwellformedpd2s0' & HDisjointpdpd2s0)))))].
							unfold getFreeSlotsList in Hoptionfreeslotslistpd.
							unfold getFreeSlotsList in Hoptionfreeslotslistpd2.
							rewrite Hpdinsertions0 in *.
							rewrite Hlookuppd2s0 in *.
							assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
							{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
							assert(HnewBFirstFrees0P : firstfreeslot pd2entry = newBlockEntryAddr) by intuition.
							rewrite HnewBFirstFrees0PDT in *.
							rewrite HnewBFirstFrees0P in *.
							destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
								rewrite FreeSlotsListRec_unroll in Hoptionfreeslotslistpd.
								rewrite FreeSlotsListRec_unroll in Hoptionfreeslotslistpd2.
								unfold getFreeSlotsListAux in *.
								induction (maxIdx+1). (* false induction because of fixpoint constraints *)
								** (* N=0 -> NotWellFormed *)
									rewrite Hoptionlist1s0 in *.
									cbn in Hwellformed1s0.
									congruence.
								** (* N>0 *)
									clear IHn.
									rewrite HlookupnewBs0 in *.
									destruct (StateLib.Index.ltb (nbfreeslots pdentry) zero) eqn:Hltb ; try(cbn in * ; congruence).
									destruct (StateLib.Index.ltb (nbfreeslots pd2entry) zero) eqn:Hltb' ; try(cbn in * ; congruence).
									destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred1 ; try(exfalso ; congruence).
									*** destruct (StateLib.Index.pred (nbfreeslots pd2entry)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
											**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd2.
														cbn in *.
														unfold Lib.disjoint in HDisjointpdpd2s0.
														specialize(HDisjointpdpd2s0 newBlockEntryAddr).
														simpl in HDisjointpdpd2s0.
														intuition.
											**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd2.
														cbn in *. congruence.
									*** destruct (StateLib.Index.pred (nbfreeslots pd2entry)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
											**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd2.
														cbn in *.
														unfold Lib.disjoint in HDisjointpdpd2s0.
														specialize(HDisjointpdpd2s0 newBlockEntryAddr).
														simpl in HDisjointpdpd2s0.
														intuition.
											**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd2.
														cbn in *. congruence.
			--- unfold isBE. subst s6. subst s5. subst s4. subst s3. subst s2. subst s1. cbn.
					destruct (beqAddr pdinsertion newBlockEntryAddr) ; try(exfalso ; congruence).
					rewrite beqAddrTrue.
					cbn.
					repeat rewrite removeDupIdentity ; intuition.
			--- subst listoption2.
					rewrite <- Hfreeslotss1 in *. rewrite <- Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *.
					rewrite <- Hfreeslotss5 in *. rewrite <- Hfreeslotss6 in *. intuition.
			--- assert(H_NoDups0 : NoDupInFreeSlotsList s0)
							by (unfold consistency in * ; intuition).
					unfold NoDupInFreeSlotsList in *.
					specialize (H_NoDups0 pd2 pd2entry Hlookuppd2s0).
					destruct H_NoDups0 as [optionlist2 (Hoptionlist2 & HwellFormed2' & HNoDup2)].
					unfold getFreeSlotsList in Hoptionlist2.
					rewrite Hlookuppd2s0 in *.
					destruct (beqAddr (firstfreeslot pd2entry) nullAddr) eqn:Hpd2Null ; try(exfalso ; congruence).
					subst optionlist2. subst listoption2.
					rewrite Hfreeslotss1 in *. rewrite Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *.
					rewrite <- Hfreeslotss5 in *. rewrite <- Hfreeslotss6 in *. intuition.
			--- rewrite <- Hfreeslotss6 in *. rewrite <- Hfreeslotss5 in *.
					rewrite <- Hfreeslotss4 in *. rewrite <- Hfreeslotss3 in *.
					rewrite Hfreeslotss2 in *. rewrite Hfreeslotss1 in *.
					(* newB is in freeslots list of pdinsertion, so can't be in other list
							because of Disjoint *)
					(* DUP from previous step *)
					destruct HDisjointpdpd2s0 as [optionfreeslotslistpd (optionfreeslotslistpd2 & (Hoptionfreeslotslistpd & (Hwellformedpds0 & (Hoptionfreeslotslistpd2 & (Hwellformedpd2s0' & HDisjointpdpd2s0)))))].
					unfold getFreeSlotsList in Hoptionfreeslotslistpd.
					unfold getFreeSlotsList in Hoptionfreeslotslistpd2.
					rewrite Hpdinsertions0 in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					rewrite HnewBFirstFrees0PDT in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
					rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
					destruct (beqAddr (firstfreeslot pd2entry) nullAddr) eqn:HfirstfreeNull ; try(exfalso ; congruence).
					(* firstfreeslot p <> NULL *)
					(* if first free of other PD is NOT NULL,
					then newB can't be in the two lists at s0 because of Disjoint -> False *)
					subst listoption2. subst listoption1.
					unfold Lib.disjoint in HDisjointpdpd2s0.
					specialize(HDisjointpdpd2s0 newBlockEntryAddr).
					destruct (HDisjointpdpd2s0).
					* subst optionfreeslotslistpd.
						rewrite FreeSlotsListRec_unroll.
						unfold getFreeSlotsListAux.
						assert(HmaxIdxNextEq :	maxIdx + 1 = S maxIdx) by apply MaxIdxNextEq.
						rewrite HmaxIdxNextEq.
						rewrite HlookupnewBs0.
						assert(HcurrNb : currnbfreeslots = nbfreeslots pdentry).
						{ unfold pdentryNbFreeSlots in *. rewrite Hpdinsertions0 in *. intuition. }
						rewrite <- HcurrNb in *.
						destruct (StateLib.Index.ltb currnbfreeslots zero) eqn:Hltb ; try(exfalso ; congruence).
						** unfold StateLib.Index.ltb in Hltb.
								apply PeanoNat.Nat.ltb_lt in Hltb.
								contradict Hltb. apply PeanoNat.Nat.lt_asymm. intuition.
						**	destruct (StateLib.Index.pred currnbfreeslots) eqn:Hpred ; try(exfalso ; congruence).
								cbn. intuition.
					* subst optionfreeslotslistpd2. rewrite Hlookuppd2s0.
						destruct (beqAddr (firstfreeslot pd2entry) nullAddr) ; try(exfalso ; congruence).
						intuition.
}
	simpl in s7.
	assert(Hfreeslotss8 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s8 (nbfreeslots pd2entry) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s7 (nbfreeslots pd2entry)).
	{	subst s8.
		(* DUP *)
				apply getFreeSlotsListRecEqBE ; intuition.
				---	(* Lists are disjoint at s0, so newB <> firstfreeslot p *)
							destruct HDisjointpdpd2s0 as [optionfreeslotslistpd (optionfreeslotslistpd2 & (Hoptionfreeslotslistpd & (Hwellformedpds0 & (Hoptionfreeslotslistpd2 & (Hwellformedpd2s0' & HDisjointpdpd2s0)))))].
							unfold getFreeSlotsList in Hoptionfreeslotslistpd.
							unfold getFreeSlotsList in Hoptionfreeslotslistpd2.
							rewrite Hpdinsertions0 in *.
							rewrite Hlookuppd2s0 in *.
							assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
							{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
							assert(HnewBFirstFrees0P : firstfreeslot pd2entry = newBlockEntryAddr) by intuition.
							rewrite HnewBFirstFrees0PDT in *.
							rewrite HnewBFirstFrees0P in *.
							destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
								rewrite FreeSlotsListRec_unroll in Hoptionfreeslotslistpd.
								rewrite FreeSlotsListRec_unroll in Hoptionfreeslotslistpd2.
								unfold getFreeSlotsListAux in *.
								induction (maxIdx+1). (* false induction because of fixpoint constraints *)
								** (* N=0 -> NotWellFormed *)
									rewrite Hoptionlist1s0 in *.
									cbn in Hwellformed1s0.
									congruence.
								** (* N>0 *)
									clear IHn.
									rewrite HlookupnewBs0 in *.
									destruct (StateLib.Index.ltb (nbfreeslots pdentry) zero) eqn:Hltb ; try(cbn in * ; congruence).
									destruct (StateLib.Index.ltb (nbfreeslots pd2entry) zero) eqn:Hltb' ; try(cbn in * ; congruence).
									destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred1 ; try(exfalso ; congruence).
									*** destruct (StateLib.Index.pred (nbfreeslots pd2entry)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
											**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd2.
														cbn in *.
														unfold Lib.disjoint in HDisjointpdpd2s0.
														specialize(HDisjointpdpd2s0 newBlockEntryAddr).
														simpl in HDisjointpdpd2s0.
														intuition.
											**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd2.
														cbn in *. congruence.
									*** destruct (StateLib.Index.pred (nbfreeslots pd2entry)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
											**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd2.
														cbn in *.
														unfold Lib.disjoint in HDisjointpdpd2s0.
														specialize(HDisjointpdpd2s0 newBlockEntryAddr).
														simpl in HDisjointpdpd2s0.
														intuition.
											**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd2.
														cbn in *. congruence.
			--- unfold isBE. subst s7.
					subst s6. subst s5. subst s4. subst s3. subst s2. subst s1. cbn.
					destruct (beqAddr pdinsertion newBlockEntryAddr) ; try(exfalso ; congruence).
					rewrite beqAddrTrue.
					cbn.
					repeat rewrite removeDupIdentity ; intuition.
			--- subst listoption2.
					rewrite <- Hfreeslotss1 in *. rewrite <- Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *.
					rewrite <- Hfreeslotss5 in *. rewrite <- Hfreeslotss6 in *.
					rewrite <- Hfreeslotss7 in *. intuition.
			--- assert(H_NoDups0 : NoDupInFreeSlotsList s0)
							by (unfold consistency in * ; intuition).
					unfold NoDupInFreeSlotsList in *.
					specialize (H_NoDups0 pd2 pd2entry Hlookuppd2s0).
					destruct H_NoDups0 as [optionlist2 (Hoptionlist2 & HwellFormed2' & HNoDup2)].
					unfold getFreeSlotsList in Hoptionlist2.
					rewrite Hlookuppd2s0 in *.
					destruct (beqAddr (firstfreeslot pd2entry) nullAddr) eqn:Hpd2Null ; try(exfalso ; congruence).
					subst optionlist2. subst listoption2.
					rewrite Hfreeslotss1 in *. rewrite Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *.
					rewrite <- Hfreeslotss5 in *. rewrite <- Hfreeslotss6 in *.
					rewrite <- Hfreeslotss7 in *. intuition.
			--- rewrite <- Hfreeslotss7 in *.
					rewrite <- Hfreeslotss6 in *. rewrite <- Hfreeslotss5 in *.
					rewrite <- Hfreeslotss4 in *. rewrite <- Hfreeslotss3 in *.
					rewrite Hfreeslotss2 in *. rewrite Hfreeslotss1 in *.
					(* newB is in freeslots list of pdinsertion, so can't be in other list
							because of Disjoint *)
					(* DUP from previous step *)
					destruct HDisjointpdpd2s0 as [optionfreeslotslistpd (optionfreeslotslistpd2 & (Hoptionfreeslotslistpd & (Hwellformedpds0 & (Hoptionfreeslotslistpd2 & (Hwellformedpd2s0' & HDisjointpdpd2s0)))))].
					unfold getFreeSlotsList in Hoptionfreeslotslistpd.
					unfold getFreeSlotsList in Hoptionfreeslotslistpd2.
					rewrite Hpdinsertions0 in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					rewrite HnewBFirstFrees0PDT in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
					rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
					destruct (beqAddr (firstfreeslot pd2entry) nullAddr) eqn:HfirstfreeNull ; try(exfalso ; congruence).
					(* firstfreeslot p <> NULL *)
					(* if first free of other PD is NOT NULL,
					then newB can't be in the two lists at s0 because of Disjoint -> False *)
					subst listoption2. subst listoption1.
					unfold Lib.disjoint in HDisjointpdpd2s0.
					specialize(HDisjointpdpd2s0 newBlockEntryAddr).
					destruct (HDisjointpdpd2s0).
					* subst optionfreeslotslistpd.
						rewrite FreeSlotsListRec_unroll.
						unfold getFreeSlotsListAux.
						assert(HmaxIdxNextEq :	maxIdx + 1 = S maxIdx) by apply MaxIdxNextEq.
						rewrite HmaxIdxNextEq.
						rewrite HlookupnewBs0.
						assert(HcurrNb : currnbfreeslots = nbfreeslots pdentry).
						{ unfold pdentryNbFreeSlots in *. rewrite Hpdinsertions0 in *. intuition. }
						rewrite <- HcurrNb in *.
						destruct (StateLib.Index.ltb currnbfreeslots zero) eqn:Hltb ; try(exfalso ; congruence).
						** unfold StateLib.Index.ltb in Hltb.
								apply PeanoNat.Nat.ltb_lt in Hltb.
								contradict Hltb. apply PeanoNat.Nat.lt_asymm. intuition.
						**	destruct (StateLib.Index.pred currnbfreeslots) eqn:Hpred ; try(exfalso ; congruence).
								cbn. intuition.
					* subst optionfreeslotslistpd2. rewrite Hlookuppd2s0.
						destruct (beqAddr (firstfreeslot pd2entry) nullAddr) ; try(exfalso ; congruence).
						intuition.
}
	simpl in s7.
	assert(Hfreeslotss9 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s9 (nbfreeslots pd2entry) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s8 (nbfreeslots pd2entry)).
	{ subst s9.
		(* DUP *)
				apply getFreeSlotsListRecEqBE ; intuition.
				---	(* Lists are disjoint at s0, so newB <> firstfreeslot p *)
							destruct HDisjointpdpd2s0 as [optionfreeslotslistpd (optionfreeslotslistpd2 & (Hoptionfreeslotslistpd & (Hwellformedpds0 & (Hoptionfreeslotslistpd2 & (Hwellformedpd2s0' & HDisjointpdpd2s0)))))].

							unfold getFreeSlotsList in Hoptionfreeslotslistpd.
							unfold getFreeSlotsList in Hoptionfreeslotslistpd2.
							rewrite Hpdinsertions0 in *.
							rewrite Hlookuppd2s0 in *.
							assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
							{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
							assert(HnewBFirstFrees0P : firstfreeslot pd2entry = newBlockEntryAddr) by intuition.
							rewrite HnewBFirstFrees0PDT in *.
							rewrite HnewBFirstFrees0P in *.
							destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
								rewrite FreeSlotsListRec_unroll in Hoptionfreeslotslistpd.
								rewrite FreeSlotsListRec_unroll in Hoptionfreeslotslistpd2.
								unfold getFreeSlotsListAux in *.
								induction (maxIdx+1). (* false induction because of fixpoint constraints *)
								** (* N=0 -> NotWellFormed *)
									rewrite Hoptionlist1s0 in *.
									cbn in Hwellformed1s0.
									congruence.
								** (* N>0 *)
									clear IHn.
									rewrite HlookupnewBs0 in *.
									destruct (StateLib.Index.ltb (nbfreeslots pdentry) zero) eqn:Hltb ; try(cbn in * ; congruence).
									destruct (StateLib.Index.ltb (nbfreeslots pd2entry) zero) eqn:Hltb' ; try(cbn in * ; congruence).
									destruct (StateLib.Index.pred (nbfreeslots pdentry)) eqn:Hpred1 ; try(exfalso ; congruence).
									*** destruct (StateLib.Index.pred (nbfreeslots pd2entry)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
											**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd2.
														cbn in *.
														unfold Lib.disjoint in HDisjointpdpd2s0.
														specialize(HDisjointpdpd2s0 newBlockEntryAddr).
														simpl in HDisjointpdpd2s0.
														intuition.
											**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd2.
														cbn in *. congruence.
									*** destruct (StateLib.Index.pred (nbfreeslots pd2entry)) eqn:Hpred2 ; try(subst listoption2 ; intuition).
											**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd2.
														cbn in *.
														unfold Lib.disjoint in HDisjointpdpd2s0.
														specialize(HDisjointpdpd2s0 newBlockEntryAddr).
														simpl in HDisjointpdpd2s0.
														intuition.
											**** 	subst optionfreeslotslistpd. subst optionfreeslotslistpd2.
														cbn in *. congruence.
			--- unfold isBE. subst s8. subst s7.
					subst s6. subst s5. subst s4. subst s3. subst s2. subst s1. cbn.
					destruct (beqAddr pdinsertion newBlockEntryAddr) ; try(exfalso ; congruence).
					rewrite beqAddrTrue.
					cbn.
					repeat rewrite removeDupIdentity ; intuition.
			--- subst listoption2.
					rewrite <- Hfreeslotss1 in *. rewrite <- Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *.
					rewrite <- Hfreeslotss5 in *. rewrite <- Hfreeslotss6 in *.
					rewrite <- Hfreeslotss7 in *. rewrite <- Hfreeslotss8 in *. intuition.
			--- assert(H_NoDups0 : NoDupInFreeSlotsList s0)
							by (unfold consistency in * ; intuition).
					unfold NoDupInFreeSlotsList in *.
					specialize (H_NoDups0 pd2 pd2entry Hlookuppd2s0).
					destruct H_NoDups0 as [optionlist2 (Hoptionlist2 & HwellFormed2' & HNoDup2)].
					unfold getFreeSlotsList in Hoptionlist2.
					rewrite Hlookuppd2s0 in *.
					destruct (beqAddr (firstfreeslot pd2entry) nullAddr) eqn:Hpd2Null ; try(exfalso ; congruence).
					subst optionlist2. subst listoption2.
					rewrite Hfreeslotss1 in *. rewrite Hfreeslotss2 in *.
					rewrite <- Hfreeslotss3 in *. rewrite <- Hfreeslotss4 in *.
					rewrite <- Hfreeslotss5 in *. rewrite <- Hfreeslotss6 in *.
					rewrite <- Hfreeslotss7 in *. rewrite <- Hfreeslotss8 in *. intuition.
			--- rewrite <- Hfreeslotss8 in *. rewrite <- Hfreeslotss7 in *.
					rewrite <- Hfreeslotss6 in *. rewrite <- Hfreeslotss5 in *.
					rewrite <- Hfreeslotss4 in *. rewrite <- Hfreeslotss3 in *.
					rewrite Hfreeslotss2 in *. rewrite Hfreeslotss1 in *.
					(* newB is in freeslots list of pdinsertion, so can't be in other list
							because of Disjoint *)
					(* DUP from previous step *)
					destruct HDisjointpdpd2s0 as [optionfreeslotslistpd (optionfreeslotslistpd2 & (Hoptionfreeslotslistpd & (Hwellformedpds0 & (Hoptionfreeslotslistpd2 & (Hwellformedpd2s0' & HDisjointpdpd2s0)))))].
					unfold getFreeSlotsList in Hoptionfreeslotslistpd.
					unfold getFreeSlotsList in Hoptionfreeslotslistpd2.
					rewrite Hpdinsertions0 in *.
					assert(HnewBFirstFrees0PDT : firstfreeslot pdentry = newBlockEntryAddr).
					{ unfold pdentryFirstFreeSlot in *. rewrite Hpdinsertions0 in *. intuition. }
					rewrite HnewBFirstFrees0PDT in *.
					destruct (beqAddr newBlockEntryAddr nullAddr) eqn:Hf ; try(exfalso ; congruence).
					rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
					destruct (beqAddr (firstfreeslot pd2entry) nullAddr) eqn:HfirstfreeNull ; try(exfalso ; congruence).
					(* firstfreeslot p <> NULL *)
					(* if first free of other PD is NOT NULL,
					then newB can't be in the two lists at s0 because of Disjoint -> False *)
					subst listoption2. subst listoption1.
					unfold Lib.disjoint in HDisjointpdpd2s0.
					specialize(HDisjointpdpd2s0 newBlockEntryAddr).
					destruct (HDisjointpdpd2s0).
					* subst optionfreeslotslistpd.
						rewrite FreeSlotsListRec_unroll.
						unfold getFreeSlotsListAux.
						assert(HmaxIdxNextEq :	maxIdx + 1 = S maxIdx) by apply MaxIdxNextEq.
						rewrite HmaxIdxNextEq.
						rewrite HlookupnewBs0.
						assert(HcurrNb : currnbfreeslots = nbfreeslots pdentry).
						{ unfold pdentryNbFreeSlots in *. rewrite Hpdinsertions0 in *. intuition. }
						rewrite <- HcurrNb in *.
						destruct (StateLib.Index.ltb currnbfreeslots zero) eqn:Hltb ; try(exfalso ; congruence).
						** unfold StateLib.Index.ltb in Hltb.
								apply PeanoNat.Nat.ltb_lt in Hltb.
								contradict Hltb. apply PeanoNat.Nat.lt_asymm. intuition.
						**	destruct (StateLib.Index.pred currnbfreeslots) eqn:Hpred ; try(exfalso ; congruence).
								cbn. intuition.
					* subst optionfreeslotslistpd2. rewrite Hlookuppd2s0.
						destruct (beqAddr (firstfreeslot pd2entry) nullAddr) ; try(exfalso ; congruence).
						intuition.
}
	simpl in s8. simpl in s9.
	assert(Hfreeslotss10 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s10 (nbfreeslots pd2entry) =
getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s9 (nbfreeslots pd2entry)).
	{			assert(HSCEs9 : isSCE sceaddr s9).
				{ unfold isSCE. subst s9. subst s8. subst s7. subst s6. subst s5.
					subst s4. subst s3. subst s2. subst s1. cbn. rewrite beqAddrTrue.
					destruct (beqAddr newBlockEntryAddr sceaddr) eqn:Hf ; try(exfalso ; congruence).
					rewrite <- beqAddrFalse in *.
					repeat rewrite removeDupIdentity ; intuition.
					destruct (beqAddr pdinsertion newBlockEntryAddr) eqn:Hff ; try(exfalso ; congruence).
					rewrite <- DependentTypeLemmas.beqAddrTrue in Hff. congruence.
					cbn.
					destruct (beqAddr pdinsertion sceaddr) eqn:Hfff ; try(exfalso ; congruence).
					rewrite <- DependentTypeLemmas.beqAddrTrue in Hfff. congruence.
					rewrite beqAddrTrue.
					rewrite <- beqAddrFalse in *.
					repeat rewrite removeDupIdentity ; intuition.
				}
				subst s10. rewrite H51. (* s = currentPartition s9  ...*)
				apply getFreeSlotsListRecEqSCE.
				--- 	intro Hfirstsceeq.
						assert(HFirstFreeSlotPointerIsBEAndFreeSlots0 : FirstFreeSlotPointerIsBEAndFreeSlot s0)
							by (unfold consistency in * ; intuition).
						unfold FirstFreeSlotPointerIsBEAndFreeSlot in *.
						specialize (HFirstFreeSlotPointerIsBEAndFreeSlots0 pd2 pd2entry Hlookuppd2s0).
						destruct HFirstFreeSlotPointerIsBEAndFreeSlots0.
						---- intro HfirstfreeNull.
								assert(HnullAddrExistss0 : nullAddrExists s0)
									by (unfold consistency in * ; intuition).
								unfold nullAddrExists in *.
								unfold isSCE in *.
								unfold isPADDR in *.
								rewrite HfirstfreeNull in *. rewrite <- Hfirstsceeq in *.
								destruct (lookup nullAddr (memory s0) beqAddr) ; try(exfalso ; congruence).
								destruct v ; try(exfalso ; congruence).
						---- rewrite Hfirstsceeq in *.
								unfold isSCE in *.
								unfold isBE in *.
								destruct (lookup sceaddr (memory s0) beqAddr) ; try (exfalso ; congruence).
								destruct v ; try(exfalso ; congruence).
				--- unfold isBE. unfold isSCE in HSCEs9.
						destruct (lookup sceaddr (memory s9) beqAddr) eqn:Hlookupsces9 ; try(exfalso ; congruence).
						destruct v ; try(exfalso ; congruence).
						intuition.
				--- unfold isPADDR. unfold isSCE in HSCEs9.
						destruct (lookup sceaddr (memory s9) beqAddr) eqn:Hlookupsces9 ; try(exfalso ; congruence).
						destruct v ; try(exfalso ; congruence).
						intuition.
	}
	intuition.
	assert(HcurrLtmaxIdx : nbfreeslots pd2entry <= maxIdx).
	{ intuition. apply IdxLtMaxIdx. }
	intuition.
	assert(Hmax : maxIdx + 1 = S maxIdx) by (apply MaxIdxNextEq).
	rewrite Hmax. apply Lt.le_lt_n_Sm. intuition.
}
															destruct Hfreeslotspd2Eq as [n1' (nbleft' & Hstates)].
															rewrite HsEq in *.
															assert(HfreeslotsEqpd2 : getFreeSlotsListRec n1' (firstfreeslot pd2entry) s (nbfreeslots pd2entry) =
																										getFreeSlotsListRec (maxIdx+1) (firstfreeslot pd2entry) s0 (nbfreeslots pd2entry)).
															{
																intuition.
																subst nbleft'.
																(* rewrite all previous getFreeSlotsListRec equalities *)
																rewrite H66. rewrite H64. rewrite H63. rewrite H62.
																rewrite H61. rewrite H60. rewrite H59. rewrite H58.
																rewrite H57. rewrite H55.
																reflexivity.
															}
															assert (HfreeslotsEqn1' : getFreeSlotsListRec n1' (firstfreeslot pd2entry) s (nbfreeslots pd2entry)
																												= getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s (nbfreeslots pd2entry)).
															{ eapply getFreeSlotsListRecEqN ; intuition.
																subst nbleft'. lia.
																assert (HnbLtmaxIdx : nbfreeslots pd2entry <= maxIdx) by apply IdxLtMaxIdx.
																lia.
															}
															rewrite <- HfreeslotsEqn1'. rewrite HfreeslotsEqpd2. intuition.
} (* end of DisjointFreeSlotsLists *)

	- (* Final state *)
		(*intuition.
		exists s0.*) exists pdentry. exists pdentry0. exists pdentry1.
		exists bentry. exists bentry0. exists bentry1. exists bentry2. exists bentry3.
		exists bentry4. exists bentry5. exists bentry6. exists sceaddr. exists scentry.
		exists newBlockEntryAddr. exists newFirstFreeSlotAddr. exists predCurrentNbFreeSlots.
		intuition. (*exists pdentry. intuition.*)
		-- (* sceaddr = newBlockEntryAddr *)
				assert(Hfalse : sceaddr = newBlockEntryAddr) by intuition.
				rewrite <- Hfalse in *.
				unfold isSCE in *.
				destruct (lookup sceaddr (memory s0) beqAddr) eqn:Hf; try(exfalso ; congruence).
				destruct v ; try(exfalso ; congruence).
		-- (* sceaddr = pdinsertion *)
				assert(Hfalse : sceaddr = pdinsertion) by intuition.
				rewrite <- Hfalse in *.
				unfold isSCE in *.
				unfold isPDT in *.
				destruct (lookup sceaddr (memory s0) beqAddr) eqn:Hf; try(exfalso ; congruence).
				destruct v ; try(exfalso ; congruence).
		-- 	(* sceaddr = newFirstFreeSlotAddr *)
				assert(newFsceNotEq : newFirstFreeSlotAddr <> sceaddr).
				{ apply isSCELookupEq in HSCEs0. destruct HSCEs0 as [scentrys0 HSCEs0].
					subst sceaddr.
					apply (@newFirstSCENotEq (CPaddr (newBlockEntryAddr + scoffset))
																		scentrys0
																		newBlockEntryAddr
																		newFirstFreeSlotAddr
																		pdinsertion pdentry s0) ; intuition.
				}
				congruence.
		--	(* intermediate states *)
				eexists. eexists. eexists. eexists. eexists. eexists. eexists. eexists.
				eexists. eexists. intuition.
Qed.


}


----------------------------------------------------------
2: { intros.
		eapply bindRev.
		2: { intros. eapply weaken. eapply WP.ret.
		intros. simpl. exact H3.
			}
	intros. eapply weaken. eapply writeSh1InChildLocationFromBlockEntryAddr.
	intros. simpl. exact H3.
	}
	eapply weaken. apply writeSh1PDChildFromBlockEntryAddr.
	intros. simpl.
	unfold consistency in *. intuition.
	unfold wellFormedFstShadowIfBlockEntry in *.
	specialize (H6 blockToShareInCurrPartAddr H7).
	apply isSHELookupEq in H6.
	destruct H6. exists x.
	split. assumption.
	intuition. simpl. set (blockToShareAddrInSh1 := (CPaddr (blockToShareInCurrPartAddr + sh1offset))).
	eexists. assert(beqAddr blockToShareAddrInSh1 blockToShareAddrInSh1 = true).
 	destruct blockToShareAddrInSh1. simpl.
	unfold beqAddr. apply PeanoNat.Nat.eqb_refl.
	rewrite H14. split.
	f_equal. intuition.
- (*partitionsIsolation*)
	unfold partitionsIsolation. intros. simpl.
	unfold getUsedBlocks. unfold getConfigBlocks.
	unfold getMappedBlocks. set (s' := {|
       currentPartition := currentPartition s;
       memory := _ |}) in *.
	admit.
- (* kernelDataIsolation*)
	admit.
- unfold verticalSharing. intros. simpl.
	unfold getUsedBlocks. unfold getConfigBlocks.
	unfold getMappedBlocks.
	set (s' := {|
       currentPartition := currentPartition s;
       memory := _ |}) in *.
	destruct (monadToValue (readPDStructurePointer child) s') eqn:Hstucturepointer.
