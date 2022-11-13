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
Require Import Core.Services.

Require Import Proof.Isolation Proof.Hoare Proof.Consistency Proof.WeakestPreconditions
Proof.StateLib Proof.DependentTypeLemmas Proof.InternalLemmas.

Require Import Invariants checkChildOfCurrPart insertNewEntry AddMemoryBlockSecProps.

Require Import Bool List EqNat Lia Compare_dec Coq.Logic.ProofIrrelevance.
Import List.ListNotations.

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
	cbn. intros. exact H.
}
intro currentPart.
eapply WP.bindRev.
{ (** findBlockInKSWithAddr **)
	eapply weaken. eapply findBlockInKSWithAddr.findBlockInKSWithAddr.
	intros. simpl.
	(* add PDT currentPart in common hypothesis *)
	assert(HPDTcurrPart : isPDT currentPart s) by admit. (*
	{ 	intuition. subst currentPart. eapply currentPartIsPDT ; intuition.
			unfold consistency in * ; unfold consistency1 in * ; unfold consistency1 in * ; intuition.
	}*)
	split.
	pose (H' := conj H HPDTcurrPart). apply H'. intuition.
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
					assert(HPDTIfPDFlag : PDTIfPDFlag s)
							by (unfold consistency in * ; unfold consistency1 in * ; intuition).
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
						by (unfold consistency in * ; unfold consistency1 in * ; intuition).
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
												{	(** readSh1PDChildFromBlockEntryAddr **)
													eapply weaken. apply readSh1PDChildFromBlockEntryAddr.
													intros. simpl. split. apply H6.
													intuition.
												}
												intro PDChildAddr.
												eapply bindRev.
												{ (** compareAddrToNull **)
													eapply weaken. apply Invariants.compareAddrToNull.
													intros. simpl. apply H6.
												}
												intro pdchildIsNull.
												case_eq (negb pdchildIsNull).
												------- (* case_eq negb pdchildIsNull = true *)
																intros.
																{ (** ret **)
																	eapply WP.weaken. apply WP.ret.
																	simpl. intros. intuition.
																}
												------- (* case_eq neb pdchildIsNull = false *)
																intros.
																eapply bindRev.
															{	(** readPDVidt **)
																eapply weaken. apply readPDVidt.
																intros. simpl. split. apply H7.
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
																		intros. simpl. split. apply H7.
																		repeat rewrite <- beqAddrFalse in *.
																		unfold isBE. intuition.
																		assert(HblockToShare : exists entry : BlockEntry,
																				lookup blockToShareInCurrPartAddr (memory s) beqAddr = Some (BE entry) /\
																				blockToShareInCurrPartAddr = idBlockToShare /\
        																bentryPFlag blockToShareInCurrPartAddr true s)
																			by intuition.
																		destruct HblockToShare as [blocktoshareentry (Hlookupblocktoshare & (HblocktoshqreEq & HblockPFlgaTrue))].
																		subst. rewrite Hlookupblocktoshare. trivial.
																	}
																	intro blockstart.
																	eapply bindRev.
																	{	(** readBlockEndFromBlockEntryAddr **)
																		eapply weaken. apply readBlockEndFromBlockEntryAddr.
																		intros. simpl. split. apply H7.
																		repeat rewrite <- beqAddrFalse in *.
																		unfold isBE. intuition.
																		assert(HblockToShare : exists entry : BlockEntry,
																				lookup blockToShareInCurrPartAddr (memory s) beqAddr = Some (BE entry) /\
																				blockToShareInCurrPartAddr = idBlockToShare /\
        																bentryPFlag blockToShareInCurrPartAddr true s)
																			by intuition.
																		destruct HblockToShare as [blocktoshareentry (Hlookupblocktoshare & (HblocktoshqreEq & HblockPFlgaTrue))].
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
	pose (Hconj := conj H7 HnfbfreeslotsNotZero).
	apply Hconj.
}
intro blockToShareChildEntryAddr. simpl.
eapply bindRev.
{ (** MAL.writeSh1PDChildFromBlockEntryAddr **)
	eapply weaken. apply writeSh1PDChildFromBlockEntryAddr.
	intros. simpl.
	assert(HBEbts : isBE blockToShareInCurrPartAddr s).
	{ destruct H7 as [s0 Hprops].
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
					by (unfold consistency in * ; unfold consistency1 in * ; intuition).
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
					by (unfold consistency in * ; unfold consistency1 in * ; intuition).
				unfold wellFormedFstShadowIfBlockEntry in *.
				assert(HwellFormedSCnewBs0 : wellFormedShadowCutIfBlockEntry s0)
					by (unfold consistency in * ; unfold consistency1 in * ; intuition).
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
	destruct H7 as [s0 Hprops].
	assert(HwellFormedFstShadowIfBlockEntry : wellFormedFstShadowIfBlockEntry s)
			by (unfold consistency in * ; unfold consistency1 in * ; intuition).
	specialize (HwellFormedFstShadowIfBlockEntry blockToShareInCurrPartAddr HBEbts).
	apply isSHELookupEq in HwellFormedFstShadowIfBlockEntry as [sh1entrybts HSHEbtss].
	exists sh1entrybts. split. intuition.
	assert(Hcons_conj : wellFormedFstShadowIfBlockEntry s
							/\ KernelStructureStartFromBlockEntryAddrIsKS s)
		by (unfold consistency in * ; unfold consistency1 in * ; intuition).
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
                             blockToShareInCurrPartAddr = idBlockToShare /\
        										bentryPFlag blockToShareInCurrPartAddr true s0)) /\
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
						 (exists (sh1entry : Sh1Entry) (sh1entryaddr : paddr),
												  lookup sh1entryaddr (memory s0) beqAddr = Some (SHE sh1entry) /\
												  sh1entryPDchild sh1entryaddr PDChildAddr s0 /\
													sh1entryAddr blockToShareInCurrPartAddr sh1entryaddr s0) /\
								beqAddr nullAddr PDChildAddr = pdchildIsNull /\
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
bentry3 = (CBlockEntry (read bentry2) (write bentry2) (exec bentry2)
                       (present bentry2) true (blockindex bentry2) (blockrange bentry2))
/\
bentry2 = (CBlockEntry (read bentry1) (write bentry1) (exec bentry1) true
                       (accessible bentry1) (blockindex bentry1) (blockrange bentry1))
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
	(* pdinsertion's new free slots list and ksentries and relation with lists at s0 *)
	/\ ( exists (optionfreeslotslist : list optionPaddr) (s2 : state)
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
				     optionentrieslist = getKSEntries globalIdPDChild s2 /\
				     getKSEntries globalIdPDChild s = optionentrieslist /\
				     optionentrieslist = getKSEntries globalIdPDChild s0 /\
							(* newB in free slots list at s0, so in optionentrieslist *)
							In newBlockEntryAddr (filterOptionPaddr optionentrieslist) )
				)


			/\ (	isPDT multiplexer s
					/\ getPartitions multiplexer s2 = getPartitions multiplexer s0
					/\ getPartitions multiplexer s = getPartitions multiplexer s2
					/\ getChildren globalIdPDChild s2 = getChildren globalIdPDChild s0
					/\ getChildren globalIdPDChild s = getChildren globalIdPDChild s2
					/\ getConfigBlocks globalIdPDChild s2 = getConfigBlocks globalIdPDChild s0
					/\ getConfigBlocks globalIdPDChild s = getConfigBlocks globalIdPDChild s2
					/\ getConfigPaddr globalIdPDChild s2 = getConfigPaddr globalIdPDChild s0
					/\ getConfigPaddr globalIdPDChild s = getConfigPaddr globalIdPDChild s2
					/\ (forall block, In block (getMappedBlocks globalIdPDChild s2) <->
										In block (newBlockEntryAddr:: (getMappedBlocks globalIdPDChild s0)))
					/\ (forall block, In block (getMappedBlocks globalIdPDChild s) <->
										In block (newBlockEntryAddr:: (getMappedBlocks globalIdPDChild s0)))
					/\ (forall addr, In addr (getMappedPaddr globalIdPDChild s2) <->
								In addr (getAllPaddrBlock (startAddr (blockrange bentry6)) (endAddr (blockrange bentry6))
									 ++ getMappedPaddr globalIdPDChild s0))
					/\ ((forall addr, In addr (getMappedPaddr globalIdPDChild s) <->
								In addr (getAllPaddrBlock (startAddr (blockrange bentry6)) (endAddr (blockrange bentry6))
									 ++ getMappedPaddr globalIdPDChild s0)) /\
								length (getMappedPaddr globalIdPDChild s) =
								length (getAllPaddrBlock (startAddr (blockrange bentry6))
     									(endAddr (blockrange bentry6)) ++ getMappedPaddr globalIdPDChild s0))
					/\ (forall block, In block (getAccessibleMappedBlocks globalIdPDChild s) <->
										In block (newBlockEntryAddr:: (getAccessibleMappedBlocks globalIdPDChild s0)))
					/\ (forall addr, In addr (getAccessibleMappedPaddr globalIdPDChild s) <->
								In addr (getAllPaddrBlock (startAddr (blockrange bentry6)) (endAddr (blockrange bentry6))
									 ++ getAccessibleMappedPaddr globalIdPDChild s0))

					/\ (* if not concerned *)
						(forall partition : paddr,
								partition <> globalIdPDChild ->
								isPDT partition s0 ->
								getKSEntries partition s = getKSEntries partition s0)
					/\ (forall partition : paddr,
								partition <> globalIdPDChild ->
								isPDT partition s0 ->
								 getMappedPaddr partition s = getMappedPaddr partition s0)
					/\ (forall partition : paddr,
								partition <> globalIdPDChild ->
								isPDT partition s0 ->
								getConfigPaddr partition s = getConfigPaddr partition s0)
					/\ (forall partition : paddr,
															partition <> globalIdPDChild ->
															isPDT partition s0 ->
															getPartitions partition s = getPartitions partition s0)
					/\ (forall partition : paddr,
															partition <> globalIdPDChild ->
															isPDT partition s0 ->
															getChildren partition s = getChildren partition s0)
					/\ (forall partition : paddr,
															partition <> globalIdPDChild ->
															isPDT partition s0 ->
															getMappedBlocks partition s = getMappedBlocks partition s0)
					/\ (forall partition : paddr,
								partition <> globalIdPDChild ->
								isPDT partition s0 ->
								 getAccessibleMappedPaddr partition s = getAccessibleMappedPaddr partition s0)

				)
		)

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
/\ consistency1 s10
/\ isPDT globalIdPDChild s10
/\ isSCE sceaddr s10
/\ isSHE sh1eaddr s10
/\ isBE newBlockEntryAddr s10
/\ lookup sh1eaddr (memory s10) beqAddr = lookup sh1eaddr (memory s0) beqAddr
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
				by (unfold consistency in * ; unfold consistency1 in * ; intuition).
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
					by (unfold consistency in * ; unfold consistency1 in * ; intuition).
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
				by (unfold consistency in * ; unfold consistency1 in * ; intuition).
			unfold wellFormedFstShadowIfBlockEntry in *.
			assert(HwellFormedSCnewBs0 : wellFormedShadowCutIfBlockEntry s0)
				by (unfold consistency in * ; unfold consistency1 in * ; intuition).
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
						by (unfold consistency in * ; unfold consistency1 in * ; intuition).
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
						by (unfold consistency in * ; unfold consistency1 in * ; intuition).
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

			assert(HPDTpartEq : forall partition, partition <> globalIdPDChild ->
															isPDT partition s0 ->
															isPDT partition s' = isPDT partition s0).
			{
				(* DUP *)
				intros partition HPDTparts0 HidpdpartNotEq.
				unfold isPDT. unfold s'. rewrite Hs.
				simpl.
				repeat rewrite beqAddrTrue.
				destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + sh1offset)) partition) eqn:beqsh1part; try(exfalso ; congruence).
				-- (* sh1eaddr = partition) *)
						rewrite <- DependentTypeLemmas.beqAddrTrue in beqsh1part.
						rewrite beqsh1part in *.
						unfold isPDT in *.
						rewrite HSHEbtss in *.
						trivial.
				-- (* sh1eaddr <> partition) *)
						rewrite beqAddrSym in beqsh1sce.
						rewrite beqsh1sce.
						simpl.
						destruct (beqAddr sceaddr partition) eqn:beqscepart; try(exfalso ; congruence).
						--- (* sceaddr = partition) *)
								rewrite <- DependentTypeLemmas.beqAddrTrue in beqscepart.
								rewrite beqscepart in *.
								unfold isPDT in *. unfold isSCE in *.
								destruct (lookup partition (memory s0) beqAddr) ; try(exfalso ; congruence).
								destruct v ; try(exfalso ; congruence).
						--- (* sceaddr <> partition) *)
								simpl.
								rewrite <- beqAddrFalse in *.
								repeat rewrite removeDupIdentity; intuition.
								destruct (beqAddr newBlockEntryAddr sceaddr) eqn:beqnewBsce; try(exfalso ; congruence).
								---- (* newBlockEntryAddr = sceaddr) *)
										rewrite <- DependentTypeLemmas.beqAddrTrue in beqnewBsce.
										rewrite beqnewBsce in *.
										unfold isSCE in *.
										destruct (lookup sceaddr (memory s0) beqAddr) ; try(exfalso ; congruence).
								---- (* sceaddr <> partition) *)
										simpl.
										destruct (beqAddr newBlockEntryAddr partition) eqn:beqnewBpart; try(exfalso ; congruence).
										----- (* newBlockEntryAddr = partition) *)
													rewrite <- DependentTypeLemmas.beqAddrTrue in beqnewBpart.
													rewrite beqnewBpart in *.
													unfold isPDT in *.
													destruct (lookup partition (memory s0) beqAddr) ; try(exfalso ; congruence).
													destruct v ; try(exfalso ; congruence).
										----- (* newBlockEntryAddr <> partition) *)
													simpl.
													rewrite <- beqAddrFalse in *.
													repeat rewrite removeDupIdentity; intuition.
													destruct (beqAddr globalIdPDChild newBlockEntryAddr) eqn:Hf; try(exfalso ; congruence).
													rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
													simpl.
													destruct (beqAddr globalIdPDChild partition) eqn:Hff; try(exfalso ; congruence).
													rewrite <- DependentTypeLemmas.beqAddrTrue in Hff. congruence.
													simpl.
													rewrite <- beqAddrFalse in *.
													repeat rewrite removeDupIdentity; intuition.
			}

			destruct H80 as [s1 (s2 & (s3 & (s4 & (s5 & (s6 & (s7 & (s8 & (s9 & (s10 & Hstates)))))))))].
			assert(HsEq : s = s10).
			{ intuition. subst s10. subst s9. subst s8. subst s7. subst s6. subst s5. subst s4.
				subst s3. subst s2. subst s1. simpl. subst s.
				f_equal.
			}
			assert(HPDTIfPDFlags : PDTIfPDFlag s).
			{ (*PDTIfPDFlag *)
				(* COPY of PDTIfPDFlag proved later *)
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
				destruct (lookup sh1entryaddr (memory s) beqAddr) eqn:Hlookupsh1 ; try(exfalso ; congruence).
				destruct v0  ; try(exfalso ; congruence).

					assert(HidPDs0 : isBE idpdchild s10).
					{ rewrite HsEq in Hlookup.
						unfold isBE. rewrite Hlookup. trivial.
					}
					assert(HlookupidpdchildEq : lookup idpdchild (memory s) beqAddr = lookup idpdchild (memory s10) beqAddr).
					{
						rewrite HsEq. trivial.
					}

					(* pull hypotheses to s10 *)
					assert(Hchilds10 : true = StateLib.checkChild idpdchild s10 sh1entryaddr /\
								sh1entryAddr idpdchild sh1entryaddr s10).
					{
						assert(HwellformedFstShadows10 : wellFormedFstShadowIfBlockEntry s10)
							by (rewrite HsEq in * ; unfold consistency1 in * ; intuition).
						specialize(HwellformedFstShadows10 idpdchild HidPDs0).
						apply isSHELookupEq in HwellformedFstShadows10 as [sh1pdchild Hlookupsh1pdchilds10].
						unfold checkChild.
						rewrite HsEq in Hlookup. rewrite Hlookup.
						subst sh1entryaddr.
						rewrite Hlookupsh1pdchilds10 in *.
						assert(Hlookupidpdchilds10  : isBE idpdchild s10)
							by (unfold isBE ; rewrite Hlookup ; intuition).
						apply isBELookupEq in Hlookupidpdchilds10. destruct Hlookupidpdchilds10 as [idpdchilds10 Hlookupidpdchilds10].
						unfold sh1entryAddr.
						rewrite Hlookupidpdchilds10 in *.
						assert(s11 = sh1pdchild).
						{
							rewrite HsEq in Hlookupsh1.
							rewrite Hlookupsh1pdchilds10 in Hlookupsh1.
							inversion Hlookupsh1. trivial.
						}
						subst s11.
						intuition.
					}
					assert(Hcons10 : PDTIfPDFlag s10)
						by (rewrite HsEq in * ; unfold consistency1 in * ; intuition).
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
						rewrite HsEq. trivial.
					}
					rewrite HlookupstartaddrEq.

					destruct (lookup startaddr (memory s10) beqAddr) eqn:Hlookupstart ; try(exfalso ; congruence).
					destruct v0 ; try (exfalso ; congruence).
					reflexivity.
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
			+ destruct H78 as [optionfreeslotslist (s2' & (n0 & (n1 & (n2 & (nbleft & Hoptionfreeslotslist)))))].
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
				++	destruct H113 as [optionentrieslist (Hoptionentrieslists & (Hoptionentrieslists' & Hoptionentrieslists0))].
						exists optionentrieslist.
						unfold s'. intuition.
						remember ((CPaddr (blockToShareInCurrPartAddr + sh1offset))) as sh1eaddr.
						rewrite <- Hoptionentrieslists'.
						eapply getKSEntriesEqSHE.
						+++ assert(Hlookupglobals : lookup globalIdPDChild (memory s) beqAddr = Some (PDT pdentry1)) by trivial.
								rewrite Hlookupglobals. trivial.
						+++ unfold isSHE. rewrite Hlookupsh1btseq. rewrite Hsh1entry. trivial.
				++ 	apply isPDTMultiplexerEqSHE with sh1entry; intuition.
						rewrite Hlookupsh1btseq. assumption.
				++ 	assert(Heq1 : getPartitions multiplexer s = getPartitions multiplexer s2') by intuition.
						assert(Heq2 : getPartitions multiplexer s2' = getPartitions multiplexer s0) by intuition.
						rewrite Heq1. rewrite Heq2. trivial.
				++ eapply getPartitionsEqSHE with sh1entry; intuition.
						+++ rewrite Hlookupsh1btseq. assumption.
						+++ rewrite Hsh1entryEq. simpl. trivial.
				++ 	assert(Heq1 : getChildren globalIdPDChild s = getChildren globalIdPDChild s2') by intuition.
						assert(Heq2 : getChildren globalIdPDChild s2' = getChildren globalIdPDChild s0) by intuition.
						rewrite Heq1. rewrite Heq2. trivial.
				++ 	eapply getChildrenEqSHE with sh1entry ; intuition.
						+++ rewrite Hs.
								cbn. rewrite beqAddrTrue.
								rewrite beqAddrSym in beqsh1sce. rewrite beqsh1sce.
								destruct (beqAddr newBlockEntryAddr sceaddr) eqn:Hf ; try(exfalso ; congruence).
								rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
								cbn.
								rewrite beqAddrSym in beqsh1newB. rewrite beqsh1newB.
								cbn.
								rewrite <- beqAddrFalse in *.
								repeat rewrite removeDupIdentity ; intuition.
								destruct (beqAddr globalIdPDChild newBlockEntryAddr) eqn:Hff ; try(exfalso ; congruence).
								rewrite <- DependentTypeLemmas.beqAddrTrue in Hff. congruence.
								cbn.
								destruct (beqAddr globalIdPDChild (CPaddr (blockToShareInCurrPartAddr + sh1offset))) eqn:Hfff ; try(exfalso ; congruence).
								rewrite <- DependentTypeLemmas.beqAddrTrue in Hfff. congruence.
								cbn.
								rewrite beqAddrTrue.
								rewrite <- beqAddrFalse in *.
								repeat rewrite removeDupIdentity ; intuition.
						+++ cbn. subst sh1entrybts. trivial.
				++	assert(Heq1 : getConfigBlocks globalIdPDChild s = getConfigBlocks globalIdPDChild s2') by intuition.
						assert(Heq2 : getConfigBlocks globalIdPDChild s2' = getConfigBlocks globalIdPDChild s0) by intuition.
						rewrite Heq1. rewrite Heq2. trivial.
				++	eapply getConfigBlocksEqSHE with pdentry1 ; intuition.
				++	assert(Heq1 : getConfigPaddr globalIdPDChild s = getConfigPaddr globalIdPDChild s2') by intuition.
						assert(Heq2 : getConfigPaddr globalIdPDChild s2' = getConfigPaddr globalIdPDChild s0) by intuition.
						rewrite Heq1. rewrite Heq2. trivial.
				++	eapply getConfigPaddrEqSHE ; intuition.
				++ assert(HMappedEq : (getMappedBlocks globalIdPDChild s') = (getMappedBlocks globalIdPDChild s)).
						{ unfold s'. eapply getMappedBlocksEqSHE ; intuition. }
						assert(HMapped :   forall block : paddr,
								In block (getMappedBlocks globalIdPDChild s) <->
								newBlockEntryAddr = block \/ In block (getMappedBlocks globalIdPDChild s0))
								by intuition.
						rewrite HMappedEq in *.
						specialize (HMapped block). intuition.
				++ assert(HMappedEq : (getMappedBlocks globalIdPDChild s') = (getMappedBlocks globalIdPDChild s)).
						{ unfold s'. eapply getMappedBlocksEqSHE ; intuition. }
						assert(HMapped :   forall block : paddr,
								In block (getMappedBlocks globalIdPDChild s) <->
								newBlockEntryAddr = block \/ In block (getMappedBlocks globalIdPDChild s0))
								by intuition.
						rewrite HMappedEq in *.
						specialize (HMapped block). intuition.
				++ assert(HMappedEq : (getMappedBlocks globalIdPDChild s') = (getMappedBlocks globalIdPDChild s)).
						{ unfold s'. eapply getMappedBlocksEqSHE ; intuition. }
						assert(HMapped :   forall block : paddr,
								In block (getMappedBlocks globalIdPDChild s) <->
								newBlockEntryAddr = block \/ In block (getMappedBlocks globalIdPDChild s0))
								by intuition.
						rewrite HMappedEq in *.
						specialize (HMapped block). intuition.
				++ assert(HMappedPaddrEq : (getMappedPaddr globalIdPDChild s') =
																		(getMappedPaddr globalIdPDChild s)).
						{ unfold s'. eapply getMappedPaddrEqSHE ; intuition. }
						assert(HMapped :   forall addr : paddr,
													 In addr (getMappedPaddr globalIdPDChild s) <->
													 In addr
														 (getAllPaddrBlock (startAddr (blockrange bentry6))
																(endAddr (blockrange bentry6)) ++ getMappedPaddr globalIdPDChild s0))
								by intuition.
						rewrite HMappedPaddrEq in *.
						specialize (HMapped addr). intuition.
					++ assert(HMappedPaddrEq : (getMappedPaddr globalIdPDChild s') =
																		(getMappedPaddr globalIdPDChild s)).
						{ unfold s'. eapply getMappedPaddrEqSHE ; intuition. }
						assert(HMapped :   forall addr : paddr,
													 In addr (getMappedPaddr globalIdPDChild s) <->
													 In addr
														 (getAllPaddrBlock (startAddr (blockrange bentry6))
																(endAddr (blockrange bentry6)) ++ getMappedPaddr globalIdPDChild s0))
								by intuition.
						rewrite HMappedPaddrEq in *.
						specialize (HMapped addr). intuition.
					++ (* Length equality *)
							(* DUP *)
							assert(HMappedPaddrEq : (getMappedPaddr globalIdPDChild s') =
																		(getMappedPaddr globalIdPDChild s)).
							{ unfold s'. eapply getMappedPaddrEqSHE ; intuition. }
							rewrite HMappedPaddrEq in *.
							intuition.
					++ (* DUP *)
							assert(HMappedBlocksEq : (getAccessibleMappedBlocks globalIdPDChild s') =
																		(getAccessibleMappedBlocks globalIdPDChild s)).
							{ unfold s'. eapply getAccessibleMappedBlocksEqSHE ; intuition. }
							assert(HMapped :   forall block : paddr,
											In block (getAccessibleMappedBlocks globalIdPDChild s) <->
											newBlockEntryAddr = block \/
											In block (getAccessibleMappedBlocks globalIdPDChild s0))
									by intuition.
							rewrite HMappedBlocksEq in *.
							specialize (HMapped block). intuition.
					++ (* DUP *)
							assert(HMappedBlocksEq : (getAccessibleMappedBlocks globalIdPDChild s') =
																		(getAccessibleMappedBlocks globalIdPDChild s)).
							{ unfold s'. eapply getAccessibleMappedBlocksEqSHE ; intuition. }
							assert(HMapped :   forall block : paddr,
											In block (getAccessibleMappedBlocks globalIdPDChild s) <->
											newBlockEntryAddr = block \/
											In block (getAccessibleMappedBlocks globalIdPDChild s0))
									by intuition.
							rewrite HMappedBlocksEq in *.
							specialize (HMapped block). intuition.
					++ (* DUP *)
							assert(HMappedBlocksEq : (getAccessibleMappedBlocks globalIdPDChild s') =
																		(getAccessibleMappedBlocks globalIdPDChild s)).
							{ unfold s'. eapply getAccessibleMappedBlocksEqSHE ; intuition. }
							assert(HMapped :   forall block : paddr,
											In block (getAccessibleMappedBlocks globalIdPDChild s) <->
											newBlockEntryAddr = block \/
											In block (getAccessibleMappedBlocks globalIdPDChild s0))
									by intuition.
							rewrite HMappedBlocksEq in *.
							specialize (HMapped block). intuition.
					++ (* DUP *)
							assert(HMappedPaddrEq : (getAccessibleMappedPaddr globalIdPDChild s') =
																		(getAccessibleMappedPaddr globalIdPDChild s)).
							{ unfold s'. eapply getAccessibleMappedPaddrEqSHE ; intuition. }
							assert(HMapped :   forall addr : paddr,
									In addr (getAccessibleMappedPaddr globalIdPDChild s) <->
									In addr
										(getAllPaddrBlock (startAddr (blockrange bentry6))
											 (endAddr (blockrange bentry6)) ++ getAccessibleMappedPaddr globalIdPDChild s0))
									by intuition.
							rewrite HMappedPaddrEq in *.
							specialize (HMapped addr). intuition.
					++ (* DUP *)
							assert(HMappedPaddrEq : (getAccessibleMappedPaddr globalIdPDChild s') =
																		(getAccessibleMappedPaddr globalIdPDChild s)).
							{ unfold s'. eapply getAccessibleMappedPaddrEqSHE ; intuition. }
							assert(HMapped :   forall addr : paddr,
									In addr (getAccessibleMappedPaddr globalIdPDChild s) <->
									In addr
										(getAllPaddrBlock (startAddr (blockrange bentry6))
											 (endAddr (blockrange bentry6)) ++ getAccessibleMappedPaddr globalIdPDChild s0))
									by intuition.
							rewrite HMappedPaddrEq in *.
							specialize (HMapped addr). intuition.
					++ assert(HEq : getKSEntries partition s = getKSEntries partition s0)
								by intuition.
							rewrite <- HEq.

							assert(HPDTpartEq' : isPDT partition s' = isPDT partition s).
							{
								(* DUP *)
								unfold isPDT. unfold s'.
								simpl.
								repeat rewrite beqAddrTrue.
								destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + sh1offset)) partition) eqn:beqsh1part; try(exfalso ; congruence).
								-- (* sh1eaddr = partition) *)
										rewrite <- DependentTypeLemmas.beqAddrTrue in beqsh1part.
										rewrite beqsh1part in *.
										unfold isPDT in *.
										rewrite HSHEbtss in *.
										exfalso ; congruence.
								-- (* sh1eaddr <> partition) *)
										simpl.
										rewrite <- beqAddrFalse in *.
										repeat rewrite removeDupIdentity; intuition.
							}
							assert(HidpdpartNotEq : partition <> globalIdPDChild) by intuition.
							assert(HPDTparts0 : isPDT partition s0) by trivial.
							specialize (HPDTpartEq partition HidpdpartNotEq HPDTparts0).
							rewrite <- HPDTpartEq in *. rewrite HPDTpartEq' in *.
							assert(HPDTparts : isPDT partition s) by trivial.
							apply isPDTLookupEq in HPDTparts. destruct HPDTparts as [pdentry' Hlookupparts'].
							eapply getKSEntriesEqSHE with pdentry'; intuition.
					++ assert(HEq : getMappedPaddr partition s = getMappedPaddr partition s0)
								by intuition.
							rewrite <- HEq.

							assert(HPDTpartEq' : isPDT partition s' = isPDT partition s).
							{
								(* DUP *)
								unfold isPDT. unfold s'.
								simpl.
								repeat rewrite beqAddrTrue.
								destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + sh1offset)) partition) eqn:beqsh1part; try(exfalso ; congruence).
								-- (* sh1eaddr = partition) *)
										rewrite <- DependentTypeLemmas.beqAddrTrue in beqsh1part.
										rewrite beqsh1part in *.
										unfold isPDT in *.
										rewrite HSHEbtss in *.
										exfalso ; congruence.
								-- (* sh1eaddr <> partition) *)
										simpl.
										rewrite <- beqAddrFalse in *.
										repeat rewrite removeDupIdentity; intuition.
							}
							assert(HidpdpartNotEq : partition <> globalIdPDChild) by intuition.
							assert(HPDTparts0 : isPDT partition s0) by trivial.
							specialize (HPDTpartEq partition HidpdpartNotEq HPDTparts0).
							rewrite <- HPDTpartEq in *. rewrite HPDTpartEq' in *.
							assert(HPDTparts : isPDT partition s) by trivial.
							apply isPDTLookupEq in HPDTparts. destruct HPDTparts as [pdentry' Hlookupparts'].
							eapply getMappedPaddrEqSHE ; intuition.
					++ assert(HEq : getConfigPaddr partition s = getConfigPaddr partition s0)
								by intuition.
							rewrite <- HEq.

							assert(HPDTpartEq' : isPDT partition s' = isPDT partition s).
							{
								(* DUP *)
								unfold isPDT. unfold s'.
								simpl.
								repeat rewrite beqAddrTrue.
								destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + sh1offset)) partition) eqn:beqsh1part; try(exfalso ; congruence).
								-- (* sh1eaddr = partition) *)
										rewrite <- DependentTypeLemmas.beqAddrTrue in beqsh1part.
										rewrite beqsh1part in *.
										unfold isPDT in *.
										rewrite HSHEbtss in *.
										exfalso ; congruence.
								-- (* sh1eaddr <> partition) *)
										simpl.
										rewrite <- beqAddrFalse in *.
										repeat rewrite removeDupIdentity; intuition.
							}
							assert(HidpdpartNotEq : partition <> globalIdPDChild) by intuition.
							assert(HPDTparts0 : isPDT partition s0) by trivial.
							specialize (HPDTpartEq partition HidpdpartNotEq HPDTparts0).
							rewrite <- HPDTpartEq in *. rewrite HPDTpartEq' in *.
							assert(HPDTparts : isPDT partition s) by trivial.
							apply isPDTLookupEq in HPDTparts. destruct HPDTparts as [pdentry' Hlookupparts'].
							eapply getConfigPaddrEqSHE ; intuition.
					++ assert(HEq : getPartitions partition s = getPartitions partition s0)
								by intuition.
							rewrite <- HEq.

							assert(HPDTpartEq' : isPDT partition s' = isPDT partition s).
							{
								(* DUP *)
								unfold isPDT. unfold s'.
								simpl.
								repeat rewrite beqAddrTrue.
								destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + sh1offset)) partition) eqn:beqsh1part; try(exfalso ; congruence).
								-- (* sh1eaddr = partition) *)
										rewrite <- DependentTypeLemmas.beqAddrTrue in beqsh1part.
										rewrite beqsh1part in *.
										unfold isPDT in *.
										rewrite HSHEbtss in *.
										exfalso ; congruence.
								-- (* sh1eaddr <> partition) *)
										simpl.
										rewrite <- beqAddrFalse in *.
										repeat rewrite removeDupIdentity; intuition.
							}
							assert(HidpdpartNotEq : partition <> globalIdPDChild) by intuition.
							assert(HPDTparts0 : isPDT partition s0) by trivial.
							specialize (HPDTpartEq partition HidpdpartNotEq HPDTparts0).
							assert(HpartitionsEq :   forall partition : paddr,
												(partition = globalIdPDChild -> False) ->
												isPDT partition s0 -> getPartitions partition s = getPartitions partition s0)
									by intuition.
							specialize (HpartitionsEq partition HidpdpartNotEq HPDTparts0).
							rewrite <- HpartitionsEq in *.
							rewrite <- HPDTpartEq in *. rewrite HPDTpartEq' in *.
							assert(HPDTparts : isPDT partition s) by trivial.
							apply isPDTLookupEq in HPDTparts. destruct HPDTparts as [pdentry' Hlookupparts'].
							subst sh1entrybts.
							eapply getPartitionsEqSHE with sh1entry; intuition.
							rewrite Hlookupsh1btseq. intuition.
					++ assert(HEq : getChildren partition s = getChildren partition s0)
								by intuition.
							rewrite <- HEq.

							assert(HPDTpartEq' : isPDT partition s' = isPDT partition s).
							{
								(* DUP *)
								unfold isPDT. unfold s'.
								simpl.
								repeat rewrite beqAddrTrue.
								destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + sh1offset)) partition) eqn:beqsh1part; try(exfalso ; congruence).
								-- (* sh1eaddr = partition) *)
										rewrite <- DependentTypeLemmas.beqAddrTrue in beqsh1part.
										rewrite beqsh1part in *.
										unfold isPDT in *.
										rewrite HSHEbtss in *.
										exfalso ; congruence.
								-- (* sh1eaddr <> partition) *)
										simpl.
										rewrite <- beqAddrFalse in *.
										repeat rewrite removeDupIdentity; intuition.
							}
							assert(HidpdpartNotEq : partition <> globalIdPDChild) by intuition.
							assert(HPDTparts0 : isPDT partition s0) by trivial.
							specialize (HPDTpartEq partition HidpdpartNotEq HPDTparts0).
							rewrite <- HPDTpartEq in *. rewrite HPDTpartEq' in *.
							assert(HPDTparts : isPDT partition s) by trivial.
							apply isPDTLookupEq in HPDTparts. destruct HPDTparts as [pdentry' Hlookupparts'].
							subst sh1entrybts.
							eapply getChildrenEqSHE with sh1entry; intuition.
							rewrite Hlookupsh1btseq. intuition.
					++ assert(HEq : getMappedBlocks partition s = getMappedBlocks partition s0)
								by intuition.
							rewrite <- HEq.

							assert(HPDTpartEq' : isPDT partition s' = isPDT partition s).
							{
								(* DUP *)
								unfold isPDT. unfold s'.
								simpl.
								repeat rewrite beqAddrTrue.
								destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + sh1offset)) partition) eqn:beqsh1part; try(exfalso ; congruence).
								-- (* sh1eaddr = partition) *)
										rewrite <- DependentTypeLemmas.beqAddrTrue in beqsh1part.
										rewrite beqsh1part in *.
										unfold isPDT in *.
										rewrite HSHEbtss in *.
										exfalso ; congruence.
								-- (* sh1eaddr <> partition) *)
										simpl.
										rewrite <- beqAddrFalse in *.
										repeat rewrite removeDupIdentity; intuition.
							}
							assert(HidpdpartNotEq : partition <> globalIdPDChild) by intuition.
							assert(HPDTparts0 : isPDT partition s0) by trivial.
							specialize (HPDTpartEq partition HidpdpartNotEq HPDTparts0).
							rewrite <- HPDTpartEq in *. rewrite HPDTpartEq' in *.
							assert(HPDTparts : isPDT partition s) by trivial.
							apply isPDTLookupEq in HPDTparts. destruct HPDTparts as [pdentry' Hlookupparts'].
							eapply getMappedBlocksEqSHE ; intuition.
					++ assert(HEq : getAccessibleMappedPaddr partition s = getAccessibleMappedPaddr partition s0)
								by intuition.
							rewrite <- HEq.

							assert(HPDTpartEq' : isPDT partition s' = isPDT partition s).
							{
								(* DUP *)
								unfold isPDT. unfold s'.
								simpl.
								repeat rewrite beqAddrTrue.
								destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + sh1offset)) partition) eqn:beqsh1part; try(exfalso ; congruence).
								-- (* sh1eaddr = partition) *)
										rewrite <- DependentTypeLemmas.beqAddrTrue in beqsh1part.
										rewrite beqsh1part in *.
										unfold isPDT in *.
										rewrite HSHEbtss in *.
										exfalso ; congruence.
								-- (* sh1eaddr <> partition) *)
										simpl.
										rewrite <- beqAddrFalse in *.
										repeat rewrite removeDupIdentity; intuition.
							}
							assert(HidpdpartNotEq : partition <> globalIdPDChild) by intuition.
							assert(HPDTparts0 : isPDT partition s0) by trivial.
							specialize (HPDTpartEq partition HidpdpartNotEq HPDTparts0).
							rewrite <- HPDTpartEq in *. rewrite HPDTpartEq' in *.
							assert(HPDTparts : isPDT partition s) by trivial.
							apply isPDTLookupEq in HPDTparts. destruct HPDTparts as [pdentry' Hlookupparts'].
							eapply getAccessibleMappedPaddrEqSHE ; intuition.
			+	destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + sh1offset)) blockToShareInCurrPartAddr) eqn:btssh1bts ; try(exfalso ; congruence).
				rewrite <- beqAddrFalse in *.
				repeat rewrite removeDupIdentity ; intuition.
			+	exists s1. exists s2. exists s3. exists s4. exists s5. exists s6.
				exists s7. exists s8. exists s9. exists s10. eexists.
				rewrite <- HsEq. intuition.
				++ 	subst s9. subst s8. subst s7. subst s6. subst s5. subst s4.
						subst s3. subst s2. subst s1. simpl. subst s.
						f_equal.
} intros. simpl.
eapply bindRev.
{ (** MAL.writeSh1InChildLocationFromBlockEntryAddr **)
	eapply weaken. apply writeSh1InChildLocationFromBlockEntryAddr.
	intros. simpl.
	destruct H7 as [s0 Hprops].
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
                             blockToShareInCurrPartAddr = idBlockToShare /\
        										bentryPFlag blockToShareInCurrPartAddr true s0)) /\
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
						 (exists (sh1entry : Sh1Entry) (sh1entryaddr : paddr),
												  lookup sh1entryaddr (memory s0) beqAddr = Some (SHE sh1entry) /\
												  sh1entryPDchild sh1entryaddr PDChildAddr s0 /\
													sh1entryAddr blockToShareInCurrPartAddr sh1entryaddr s0) /\
								beqAddr nullAddr PDChildAddr = pdchildIsNull /\
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
/\ (
		(lookup sh1eaddr (memory s0) beqAddr = Some (SHE sh1entry)
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
bentry3 = (CBlockEntry (read bentry2) (write bentry2) (exec bentry2)
                       (present bentry2) true (blockindex bentry2) (blockrange bentry2))
/\
bentry2 = (CBlockEntry (read bentry1) (write bentry1) (exec bentry1) true
                       (accessible bentry1) (blockindex bentry1) (blockrange bentry1))
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
	/\ sceaddr <> blockToShareInCurrPartAddr )
	(* globalIdPDChild's new free slots list and relation with list at s0 *)
	/\ ( exists (optionfreeslotslist : list optionPaddr) (s2 : state)
				(n0 n1 n2 : nat) (nbleft : index),
      ( nbleft = CIndex (nbfreeslots - 1) /\
      	nbleft < maxIdx
			) /\
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
				     optionentrieslist = getKSEntries globalIdPDChild s2 /\
				     getKSEntries globalIdPDChild s = optionentrieslist /\
				     optionentrieslist = getKSEntries globalIdPDChild s0 /\
							(* newB in free slots list at s0, so in optionentrieslist *)
							In newBlockEntryAddr (filterOptionPaddr optionentrieslist) )
				)


			/\ (	isPDT multiplexer s
					/\ getPartitions multiplexer s2 = getPartitions multiplexer s0
					/\ getPartitions multiplexer s = getPartitions multiplexer s2
					/\ getChildren globalIdPDChild s2 = getChildren globalIdPDChild s0
					/\ getChildren globalIdPDChild s = getChildren globalIdPDChild s2
					/\ getConfigBlocks globalIdPDChild s2 = getConfigBlocks globalIdPDChild s0
					/\ getConfigBlocks globalIdPDChild s = getConfigBlocks globalIdPDChild s2
					/\ getConfigPaddr globalIdPDChild s2 = getConfigPaddr globalIdPDChild s0
					/\ getConfigPaddr globalIdPDChild s = getConfigPaddr globalIdPDChild s2
					/\ (forall block, In block (getMappedBlocks globalIdPDChild s2) <->
										In block (newBlockEntryAddr:: (getMappedBlocks globalIdPDChild s0)))
					/\ (forall block, In block (getMappedBlocks globalIdPDChild s) <->
										In block (newBlockEntryAddr:: (getMappedBlocks globalIdPDChild s0)))
					/\ (forall addr, In addr (getMappedPaddr globalIdPDChild s2) <->
								In addr (getAllPaddrBlock (startAddr (blockrange bentry6)) (endAddr (blockrange bentry6))
									 ++ getMappedPaddr globalIdPDChild s0))
					/\ ((forall addr, In addr (getMappedPaddr globalIdPDChild s) <->
								In addr (getAllPaddrBlock (startAddr (blockrange bentry6)) (endAddr (blockrange bentry6))
									 ++ getMappedPaddr globalIdPDChild s0)) /\
								length (getMappedPaddr globalIdPDChild s) =
								length (getAllPaddrBlock (startAddr (blockrange bentry6))
     									(endAddr (blockrange bentry6)) ++ getMappedPaddr globalIdPDChild s0))
					/\ (forall block, In block (getAccessibleMappedBlocks globalIdPDChild s) <->
										In block (newBlockEntryAddr:: (getAccessibleMappedBlocks globalIdPDChild s0)))
					/\ (forall addr, In addr (getAccessibleMappedPaddr globalIdPDChild s) <->
								In addr (getAllPaddrBlock (startAddr (blockrange bentry6)) (endAddr (blockrange bentry6))
									 ++ getAccessibleMappedPaddr globalIdPDChild s0))

					/\ (* if not concerned *)
						(forall partition : paddr,
								partition <> globalIdPDChild ->
								isPDT partition s0 ->
								getKSEntries partition s = getKSEntries partition s0)
					/\ (forall partition : paddr,
								partition <> globalIdPDChild ->
								isPDT partition s0 ->
								 getMappedPaddr partition s = getMappedPaddr partition s0)
					/\ (forall partition : paddr,
								partition <> globalIdPDChild ->
								isPDT partition s0 ->
								getConfigPaddr partition s = getConfigPaddr partition s0)
					/\ (forall partition : paddr,
															partition <> globalIdPDChild ->
															isPDT partition s0 ->
															getPartitions partition s = getPartitions partition s0)
					/\ (forall partition : paddr,
															partition <> globalIdPDChild ->
															isPDT partition s0 ->
															getChildren partition s = getChildren partition s0)
					/\ (forall partition : paddr,
															partition <> globalIdPDChild ->
															isPDT partition s0 ->
															getMappedBlocks partition s = getMappedBlocks partition s0)
					/\ (forall partition : paddr,
								partition <> globalIdPDChild ->
								isPDT partition s0 ->
								 getAccessibleMappedPaddr partition s = getAccessibleMappedPaddr partition s0)

				)
		)

	/\ lookup blockToShareInCurrPartAddr (memory s) beqAddr =
						lookup blockToShareInCurrPartAddr (memory s0) beqAddr

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
/\ consistency1 s10
/\ isPDT globalIdPDChild s10
/\ isSCE sceaddr s10
/\ isSHE sh1eaddr s10
/\ isBE newBlockEntryAddr s10
/\ lookup sh1eaddr (memory s10) beqAddr = lookup sh1eaddr (memory s0) beqAddr
)))).
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

			assert(HPDTIfPDFlags : PDTIfPDFlag s).
			{ (*PDTIfPDFlag *)
				intuition.
				destruct H90 as [s1 (s2' & (s3 & (s4 & (s5 & (s6 & (s7 & (s8 & (s9 & (s10 & (s11 & Hstates))))))))))].

				assert(HsEq : s = s11).
				{ intuition. subst s11. subst s10. subst s9. subst s8. subst s7.
					subst s6. subst s5. subst s4.
					subst s3. subst s2'. subst s1. simpl. subst s.
					f_equal.
				}
				destruct Hstates as [Hs1 (Hs2 & (Hs3 & (Hs4 & (Hs5 & (Hs6 & (Hs7 & (Hs8 & (Hs9 & (Hs10 & (Hs11 & Hstates))))))))))].
				(* DUP PDTIfPDFlag proved above *)
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
				destruct (lookup sh1entryaddr (memory s) beqAddr) eqn:Hlookupsh1 ; try(exfalso ; congruence).
				destruct v0  ; try(exfalso ; congruence).

					assert(HidPDs0 : isBE idpdchild s10).
					{ rewrite HsEq in Hlookup.
						rewrite Hs11 in Hlookup.
						cbn in Hlookup.
						destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + sh1offset)) idpdchild) eqn:beqsh1idpd ; try(exfalso ; congruence).
						rewrite <- beqAddrFalse in *.
						rewrite removeDupIdentity in Hlookup; intuition.
						unfold isBE. rewrite Hlookup. trivial.
					}
					assert(HlookupidpdchildEq : lookup idpdchild (memory s) beqAddr = lookup idpdchild (memory s11) beqAddr).
					{
						rewrite HsEq. trivial.
					}

					(* pull hypotheses to s11 *)
					assert(Hchilds11 : true = StateLib.checkChild idpdchild s11 sh1entryaddr /\
								sh1entryAddr idpdchild sh1entryaddr s11).
					{
						assert(HwellformedFstShadows10 : wellFormedFstShadowIfBlockEntry s10)
							by (rewrite HsEq in * ; unfold consistency1 in * ; intuition).
						specialize(HwellformedFstShadows10 idpdchild HidPDs0).
						apply isSHELookupEq in HwellformedFstShadows10 as [sh1pdchild Hlookupsh1pdchilds10].
						unfold checkChild.
						rewrite HsEq in Hlookup. rewrite Hlookup.
						subst sh1entryaddr.
						rewrite HsEq in Hlookupsh1.
						rewrite Hlookupsh1 in *.
						assert(Hlookupidpdchilds10  : isBE idpdchild s11)
							by (unfold isBE ; rewrite Hlookup ; intuition).
						apply isBELookupEq in Hlookupidpdchilds10. destruct Hlookupidpdchilds10 as [idpdchilds10 Hlookupidpdchilds10].
						unfold sh1entryAddr.
						rewrite Hlookupidpdchilds10 in *.
						intuition.
					}
					assert(Hchilds10 : true = StateLib.checkChild idpdchild s10 sh1entryaddr /\
								sh1entryAddr idpdchild sh1entryaddr s10).
					{
						rewrite Hs11 in Hchilds11.
						unfold checkChild in Hchilds11. unfold sh1entryAddr in Hchilds11.
						cbn in Hchilds11.
						destruct Hchilds11 as [Hchilds11 Hsh1entryaddrss11].
						destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + sh1offset)) idpdchild) eqn:beqsh1idpd ; try(exfalso ; congruence).
						rewrite <- beqAddrFalse in *.
						rewrite removeDupIdentity in Hchilds11; intuition.
						unfold checkChild.
						destruct(lookup idpdchild (memory s10) beqAddr) eqn:Hlookups10 ; try(exfalso ; congruence).
						destruct v0 ; try(exfalso ; congruence).
						subst sh1entryaddr.
						assert(HwellformedFstShadows10 : wellFormedFstShadowIfBlockEntry s10)
							by (rewrite HsEq in * ; unfold consistency1 in * ; intuition).
						specialize(HwellformedFstShadows10 idpdchild HidPDs0).
						apply isSHELookupEq in HwellformedFstShadows10 as [sh1pdchild Hlookupsh1pdchilds10].
						rewrite Hlookupsh1pdchilds10 in *.
						destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + sh1offset))
															(CPaddr (idpdchild + sh1offset))) eqn:beqbtsidpd ; try(exfalso ; congruence).
						- (* idpd = bts *)
							rewrite <- DependentTypeLemmas.beqAddrTrue in beqbtsidpd.
							rewrite <- beqbtsidpd in *.
							assert(Hsh1eaddr : lookup (CPaddr (blockToShareInCurrPartAddr + sh1offset)) (memory s0) beqAddr = Some (SHE sh1entry))
								by intuition.
							rewrite Hsh1eaddr in *.
							assert(Hsh1eaddr' : lookup (CPaddr (blockToShareInCurrPartAddr + sh1offset)) (memory s10) beqAddr = Some (SHE sh1entry))
								by intuition.
							rewrite Hsh1eaddr' in *.
							inversion Hlookupsh1pdchilds10 as [Hsh1eaddrEq].
							rewrite <- Hsh1eaddrEq in *.
							cbn in Hchilds11.
							assumption.
						- (* idpd <> bts *)
							rewrite <- beqAddrFalse in *.
							rewrite removeDupIdentity in Hchilds11 ; intuition.
							rewrite Hlookupsh1pdchilds10 in *.
							assumption.
						- unfold sh1entryAddr.
							destruct (lookup idpdchild (memory s10) beqAddr) eqn:Htrue ; try(exfalso ; congruence).
							destruct v0 ; try(exfalso ; congruence).
							rewrite removeDupIdentity in Hsh1entryaddrss11 ; intuition.
					}
					assert(Hcons10 : PDTIfPDFlag s10)
						by (rewrite HsEq in * ; unfold consistency1 in * ; intuition).
					unfold PDTIfPDFlag in *.
					specialize(Hcons10 idpdchild sh1entryaddr Hchilds10).

					(* A & P flags *)
					unfold bentryAFlag in *.
					unfold bentryPFlag in *.
					rewrite HlookupidpdchildEq.
					destruct (lookup idpdchild (memory s11) beqAddr) eqn:Hlookups10 ; try(exfalso ; congruence).
					destruct v0 ; try(exfalso ; congruence).
					destruct Hcons10 as [HAflag (HPflag & (startaddr & Hcons10))].
					unfold isBE in HidPDs0.
					assert(HlookupEq : lookup idpdchild (memory s11) beqAddr = lookup idpdchild (memory s10) beqAddr).
					{
						rewrite Hs11. cbn.
						rewrite <- beqAddrFalse in *.
						destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + sh1offset)) idpdchild) eqn:Hf ; try(exfalso ; congruence).
						rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
						rewrite <- beqAddrFalse in *.
						rewrite removeDupIdentity ; intuition.
					}
					rewrite HsEq.
					rewrite <- HlookupEq in *.
					rewrite Hlookups10 in *.
					split. assumption.
					split. assumption.

					(* PDflag *)
					eexists. intuition.
					unfold bentryStartAddr in *. unfold entryPDT in *.
					rewrite <- HlookupEq in *.
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
						rewrite Hs11. cbn.
						destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + sh1offset)) startaddr) eqn:Hf ; try(exfalso ; congruence).
						- (* = *)
							rewrite <- DependentTypeLemmas.beqAddrTrue in Hf.
							rewrite <- Hf in *.
							destruct (lookup (CPaddr (blockToShareInCurrPartAddr + sh1offset)) (memory s10) beqAddr) eqn:Hff ; try(exfalso ; congruence).
							destruct v0 ; try(exfalso  ; congruence).
						- (* <> *)
							rewrite <- beqAddrFalse in *.
							rewrite removeDupIdentity ; intuition.
					}
					rewrite <- HsEq. rewrite HlookupstartaddrEq.

					destruct (lookup startaddr (memory s10) beqAddr) eqn:Hlookupstart ; try(exfalso ; congruence).
					destruct v0 ; try (exfalso ; congruence).
					reflexivity.
			}

			assert(HPDTpartEq : forall partition, partition <> globalIdPDChild ->
															isPDT partition s0 ->
															isPDT partition s' = isPDT partition s0).
			{
				(* DUP *)
				intros partition HPDTparts0 HidpdpartNotEq.
				unfold isPDT. unfold s'. rewrite Hs.
				simpl.
				repeat rewrite beqAddrTrue.
				destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + sh1offset)) partition) eqn:beqsh1part; try(exfalso ; congruence).
				-- (* sh1eaddr = partition) *)
						rewrite <- DependentTypeLemmas.beqAddrTrue in beqsh1part.
						rewrite beqsh1part in *.
						unfold isPDT in *. unfold isSHE in *.
						destruct (lookup partition (memory s0) beqAddr) ; try(exfalso ; congruence).
						destruct v ; try(intuition ; exfalso ; congruence).
				-- (* sh1eaddr <> partition) *)
						rewrite beqAddrSym in beqsh1sce.
						rewrite beqsh1sce.
						simpl.
						rewrite beqsh1sce.
						simpl.
						destruct (beqAddr sceaddr partition) eqn:beqscepart; try(exfalso ; congruence).
						--- (* sceaddr = partition) *)
								rewrite <- DependentTypeLemmas.beqAddrTrue in beqscepart.
								rewrite beqscepart in *.
								unfold isPDT in *. unfold isSCE in *.
								destruct (lookup partition (memory s0) beqAddr) ; try(exfalso ; congruence).
								destruct v ; try(intuition ; exfalso ; congruence).
						--- (* sceaddr <> partition) *)
								simpl.
								rewrite <- beqAddrFalse in *.
								repeat rewrite removeDupIdentity; intuition.
								destruct (beqAddr newBlockEntryAddr sceaddr) eqn:beqnewBsce; try(exfalso ; congruence).
								---- (* newBlockEntryAddr = sceaddr) *)
										rewrite <- DependentTypeLemmas.beqAddrTrue in beqnewBsce.
										rewrite beqnewBsce in *.
										unfold isSCE in *.
										destruct (lookup sceaddr (memory s0) beqAddr) ; try(exfalso ; congruence).
								---- (* sceaddr <> partition) *)
										simpl.
										destruct (beqAddr newBlockEntryAddr partition) eqn:beqnewBpart; try(exfalso ; congruence).
										----- (* newBlockEntryAddr = partition) *)
													rewrite <- DependentTypeLemmas.beqAddrTrue in beqnewBpart.
													rewrite beqnewBpart in *.
													unfold isPDT in *.
													destruct (lookup partition (memory s0) beqAddr) ; try(exfalso ; congruence).
													destruct v ; try(exfalso ; congruence).
										----- (* newBlockEntryAddr <> partition) *)
													simpl.
													rewrite <- beqAddrFalse in *.
													repeat rewrite removeDupIdentity; intuition.
													destruct (beqAddr globalIdPDChild newBlockEntryAddr) eqn:Hf; try(exfalso ; congruence).
													rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
													simpl.
													destruct (beqAddr globalIdPDChild partition) eqn:Hff; try(exfalso ; congruence).
													rewrite <- DependentTypeLemmas.beqAddrTrue in Hff. congruence.
													simpl.
													rewrite <- beqAddrFalse in *.
													repeat rewrite removeDupIdentity; intuition.
			}

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
			+ destruct H87 as [optionfreeslotslist (s2 & (n0 & (n1 & (n2 & (nbleft & Hoptionfreeslotslist)))))].
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
				++	destruct H115 as [optionentrieslist (Hoptionentrieslists & (Hoptionentrieslists' & Hoptionentrieslists0))].
						exists optionentrieslist.
						unfold s'. intuition.
						remember ((CPaddr (blockToShareInCurrPartAddr + sh1offset))) as sh1eaddr.
						rewrite <- Hoptionentrieslists'.
						eapply getKSEntriesEqSHE.
						+++ assert(Hlookupglobals : lookup globalIdPDChild (memory s) beqAddr = Some (PDT pdentry1)) by trivial.
								rewrite Hlookupglobals. trivial.
						+++ unfold isSHE. rewrite HSHEs. trivial.
				++ apply isPDTMultiplexerEqSHE with sh1entry0; intuition.
				++ assert(Hmultiss2 : getPartitions multiplexer s = getPartitions multiplexer s2)
							by assumption.
						assert(Hmultis2s0 : getPartitions multiplexer s2 = getPartitions multiplexer s0)
							by assumption.
						rewrite Hmultiss2. rewrite Hmultis2s0. trivial.
				++ eapply getPartitionsEqSHE with sh1entry0; intuition.
						+++ subst sh1entrybts. cbn. trivial.
				++ 	assert(Heq1 : getChildren globalIdPDChild s = getChildren globalIdPDChild s2) by intuition.
						assert(Heq2 : getChildren globalIdPDChild s2 = getChildren globalIdPDChild s0) by intuition.
						rewrite Heq1. rewrite Heq2. trivial.
				++ 	eapply getChildrenEqSHE with sh1entry0 ; intuition.
						subst sh1entrybts. cbn. trivial.
				++	assert(Heq1 : getConfigBlocks globalIdPDChild s = getConfigBlocks globalIdPDChild s2) by intuition.
						assert(Heq2 : getConfigBlocks globalIdPDChild s2 = getConfigBlocks globalIdPDChild s0) by intuition.
						rewrite Heq1. rewrite Heq2. trivial.
				++	eapply getConfigBlocksEqSHE with pdentry1 ; intuition.
				++	assert(Heq1 : getConfigPaddr globalIdPDChild s = getConfigPaddr globalIdPDChild s2) by intuition.
						assert(Heq2 : getConfigPaddr globalIdPDChild s2 = getConfigPaddr globalIdPDChild s0) by intuition.
						rewrite Heq1. rewrite Heq2. trivial.
				++	eapply getConfigPaddrEqSHE ; intuition.
				++ assert(HMappedEq : (getMappedBlocks globalIdPDChild s') = (getMappedBlocks globalIdPDChild s)).
						{ unfold s'. eapply getMappedBlocksEqSHE ; intuition. }
						assert(HMapped :   forall block : paddr,
								In block (getMappedBlocks globalIdPDChild s) <->
								newBlockEntryAddr = block \/ In block (getMappedBlocks globalIdPDChild s0))
								by intuition.
						rewrite HMappedEq in *.
						specialize (HMapped block). intuition.
				++ assert(HMappedEq : (getMappedBlocks globalIdPDChild s') = (getMappedBlocks globalIdPDChild s)).
						{ unfold s'. eapply getMappedBlocksEqSHE ; intuition. }
						assert(HMapped :   forall block : paddr,
								In block (getMappedBlocks globalIdPDChild s) <->
								newBlockEntryAddr = block \/ In block (getMappedBlocks globalIdPDChild s0))
								by intuition.
						rewrite HMappedEq in *.
						specialize (HMapped block). intuition.
				++ assert(HMappedEq : (getMappedBlocks globalIdPDChild s') = (getMappedBlocks globalIdPDChild s)).
						{ unfold s'. eapply getMappedBlocksEqSHE ; intuition. }
						assert(HMapped :   forall block : paddr,
								In block (getMappedBlocks globalIdPDChild s) <->
								newBlockEntryAddr = block \/ In block (getMappedBlocks globalIdPDChild s0))
								by intuition.
						rewrite HMappedEq in *.
						specialize (HMapped block). intuition.
				++ assert(HMappedPaddrEq : (getMappedPaddr globalIdPDChild s') =
																		(getMappedPaddr globalIdPDChild s)).
						{ unfold s'. eapply getMappedPaddrEqSHE ; intuition. }
						assert(HMapped :   forall addr : paddr,
													 In addr (getMappedPaddr globalIdPDChild s) <->
													 In addr
														 (getAllPaddrBlock (startAddr (blockrange bentry6))
																(endAddr (blockrange bentry6)) ++ getMappedPaddr globalIdPDChild s0))
								by intuition.
						rewrite HMappedPaddrEq in *.
						specialize (HMapped addr). intuition.
					++ assert(HMappedPaddrEq : (getMappedPaddr globalIdPDChild s') =
																		(getMappedPaddr globalIdPDChild s)).
						{ unfold s'. eapply getMappedPaddrEqSHE ; intuition. }
						assert(HMapped :   forall addr : paddr,
													 In addr (getMappedPaddr globalIdPDChild s) <->
													 In addr
														 (getAllPaddrBlock (startAddr (blockrange bentry6))
																(endAddr (blockrange bentry6)) ++ getMappedPaddr globalIdPDChild s0))
								by intuition.
						rewrite HMappedPaddrEq in *.
						specialize (HMapped addr). intuition.
					++ (* Length equality *)
							(* DUP *)
							assert(HMappedPaddrEq : (getMappedPaddr globalIdPDChild s') =
																		(getMappedPaddr globalIdPDChild s)).
							{ unfold s'. eapply getMappedPaddrEqSHE ; intuition. }
							rewrite HMappedPaddrEq in *.
							intuition.
					++ (* DUP *)
							assert(HMappedBlocksEq : (getAccessibleMappedBlocks globalIdPDChild s') =
																		(getAccessibleMappedBlocks globalIdPDChild s)).
							{ unfold s'. eapply getAccessibleMappedBlocksEqSHE ; intuition. }
							assert(HMapped :   forall block : paddr,
											In block (getAccessibleMappedBlocks globalIdPDChild s) <->
											newBlockEntryAddr = block \/
											In block (getAccessibleMappedBlocks globalIdPDChild s0))
									by intuition.
							rewrite HMappedBlocksEq in *.
							specialize (HMapped block). intuition.
					++ (* DUP *)
							assert(HMappedBlocksEq : (getAccessibleMappedBlocks globalIdPDChild s') =
																		(getAccessibleMappedBlocks globalIdPDChild s)).
							{ unfold s'. eapply getAccessibleMappedBlocksEqSHE ; intuition. }
							assert(HMapped :   forall block : paddr,
											In block (getAccessibleMappedBlocks globalIdPDChild s) <->
											newBlockEntryAddr = block \/
											In block (getAccessibleMappedBlocks globalIdPDChild s0))
									by intuition.
							rewrite HMappedBlocksEq in *.
							specialize (HMapped block). intuition.
					++ (* DUP *)
							assert(HMappedBlocksEq : (getAccessibleMappedBlocks globalIdPDChild s') =
																		(getAccessibleMappedBlocks globalIdPDChild s)).
							{ unfold s'. eapply getAccessibleMappedBlocksEqSHE ; intuition. }
							assert(HMapped :   forall block : paddr,
											In block (getAccessibleMappedBlocks globalIdPDChild s) <->
											newBlockEntryAddr = block \/
											In block (getAccessibleMappedBlocks globalIdPDChild s0))
									by intuition.
							rewrite HMappedBlocksEq in *.
							specialize (HMapped block). intuition.
					++ (* DUP *)
							assert(HMappedPaddrEq : (getAccessibleMappedPaddr globalIdPDChild s') =
																		(getAccessibleMappedPaddr globalIdPDChild s)).
							{ unfold s'. eapply getAccessibleMappedPaddrEqSHE ; intuition. }
							assert(HMapped :   forall addr : paddr,
									In addr (getAccessibleMappedPaddr globalIdPDChild s) <->
									In addr
										(getAllPaddrBlock (startAddr (blockrange bentry6))
											 (endAddr (blockrange bentry6)) ++ getAccessibleMappedPaddr globalIdPDChild s0))
									by intuition.
							rewrite HMappedPaddrEq in *.
							specialize (HMapped addr). intuition.
					++ (* DUP *)
							assert(HMappedPaddrEq : (getAccessibleMappedPaddr globalIdPDChild s') =
																		(getAccessibleMappedPaddr globalIdPDChild s)).
							{ unfold s'. eapply getAccessibleMappedPaddrEqSHE ; intuition. }
							assert(HMapped :   forall addr : paddr,
									In addr (getAccessibleMappedPaddr globalIdPDChild s) <->
									In addr
										(getAllPaddrBlock (startAddr (blockrange bentry6))
											 (endAddr (blockrange bentry6)) ++ getAccessibleMappedPaddr globalIdPDChild s0))
									by intuition.
							rewrite HMappedPaddrEq in *.
							specialize (HMapped addr). intuition.
					++ assert(HEq : getKSEntries partition s = getKSEntries partition s0)
								by intuition.
							rewrite <- HEq.

							assert(HPDTpartEq' : isPDT partition s' = isPDT partition s).
							{
								(* DUP *)
								unfold isPDT. unfold s'.
								simpl.
								repeat rewrite beqAddrTrue.
								destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + sh1offset)) partition) eqn:beqsh1part; try(exfalso ; congruence).
								-- (* sh1eaddr = partition) *)
										rewrite <- DependentTypeLemmas.beqAddrTrue in beqsh1part.
										rewrite beqsh1part in *.
										unfold isPDT in *. unfold isSHE in *.
										destruct (lookup partition (memory s0) beqAddr) ; try(exfalso ; congruence).
										destruct v ; (intuition ; exfalso ; congruence).
								-- (* sh1eaddr <> partition) *)
										simpl.
										rewrite <- beqAddrFalse in *.
										repeat rewrite removeDupIdentity; intuition.
							}
							assert(HidpdpartNotEq : partition <> globalIdPDChild) by intuition.
							assert(HPDTparts0 : isPDT partition s0) by trivial.
							specialize (HPDTpartEq partition HidpdpartNotEq HPDTparts0).
							rewrite <- HPDTpartEq in *. rewrite HPDTpartEq' in *.
							assert(HPDTparts : isPDT partition s) by trivial.
							apply isPDTLookupEq in HPDTparts. destruct HPDTparts as [pdentry' Hlookupparts'].
							eapply getKSEntriesEqSHE with pdentry'; intuition.
					++ assert(HEq : getMappedPaddr partition s = getMappedPaddr partition s0)
								by intuition.
							rewrite <- HEq.

							assert(HPDTpartEq' : isPDT partition s' = isPDT partition s).
							{
								(* DUP *)
								unfold isPDT. unfold s'.
								simpl.
								repeat rewrite beqAddrTrue.
								destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + sh1offset)) partition) eqn:beqsh1part; try(exfalso ; congruence).
								-- (* sh1eaddr = partition) *)
										rewrite <- DependentTypeLemmas.beqAddrTrue in beqsh1part.
										rewrite beqsh1part in *.
										unfold isPDT in *. unfold isSHE in *.
										destruct (lookup partition (memory s0) beqAddr) ; try(exfalso ; congruence).
										destruct v ; (intuition ; exfalso ; congruence).
								-- (* sh1eaddr <> partition) *)
										simpl.
										rewrite <- beqAddrFalse in *.
										repeat rewrite removeDupIdentity; intuition.
							}
							assert(HidpdpartNotEq : partition <> globalIdPDChild) by intuition.
							assert(HPDTparts0 : isPDT partition s0) by trivial.
							specialize (HPDTpartEq partition HidpdpartNotEq HPDTparts0).
							rewrite <- HPDTpartEq in *. rewrite HPDTpartEq' in *.
							assert(HPDTparts : isPDT partition s) by trivial.
							apply isPDTLookupEq in HPDTparts. destruct HPDTparts as [pdentry' Hlookupparts'].
							eapply getMappedPaddrEqSHE ; intuition.
					++ assert(HEq : getConfigPaddr partition s = getConfigPaddr partition s0)
								by intuition.
							rewrite <- HEq.

							assert(HPDTpartEq' : isPDT partition s' = isPDT partition s).
							{
								(* DUP *)
								unfold isPDT. unfold s'.
								simpl.
								repeat rewrite beqAddrTrue.
								destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + sh1offset)) partition) eqn:beqsh1part; try(exfalso ; congruence).
								-- (* sh1eaddr = partition) *)
										rewrite <- DependentTypeLemmas.beqAddrTrue in beqsh1part.
										rewrite beqsh1part in *.
										unfold isPDT in *. unfold isSHE in *.
										destruct (lookup partition (memory s0) beqAddr) ; try(exfalso ; congruence).
										destruct v ; (intuition ; exfalso ; congruence).
								-- (* sh1eaddr <> partition) *)
										simpl.
										rewrite <- beqAddrFalse in *.
										repeat rewrite removeDupIdentity; intuition.
							}
							assert(HidpdpartNotEq : partition <> globalIdPDChild) by intuition.
							assert(HPDTparts0 : isPDT partition s0) by trivial.
							specialize (HPDTpartEq partition HidpdpartNotEq HPDTparts0).
							rewrite <- HPDTpartEq in *. rewrite HPDTpartEq' in *.
							assert(HPDTparts : isPDT partition s) by trivial.
							apply isPDTLookupEq in HPDTparts. destruct HPDTparts as [pdentry' Hlookupparts'].
							eapply getConfigPaddrEqSHE ; intuition.
					++ assert(HEq : getPartitions partition s = getPartitions partition s0)
								by intuition.
							rewrite <- HEq.

							assert(HPDTpartEq' : isPDT partition s' = isPDT partition s).
							{
								(* DUP *)
								unfold isPDT. unfold s'.
								simpl.
								repeat rewrite beqAddrTrue.
								destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + sh1offset)) partition) eqn:beqsh1part; try(exfalso ; congruence).
								-- (* sh1eaddr = partition) *)
										rewrite <- DependentTypeLemmas.beqAddrTrue in beqsh1part.
										rewrite beqsh1part in *.
										unfold isPDT in *. unfold isSHE in *.
										destruct (lookup partition (memory s0) beqAddr) ; try(exfalso ; congruence).
										destruct v ; (intuition ; exfalso ; congruence).
								-- (* sh1eaddr <> partition) *)
										simpl.
										rewrite <- beqAddrFalse in *.
										repeat rewrite removeDupIdentity; intuition.
							}
							assert(HidpdpartNotEq : partition <> globalIdPDChild) by intuition.
							assert(HPDTparts0 : isPDT partition s0) by trivial.
							specialize (HPDTpartEq partition HidpdpartNotEq HPDTparts0).
							assert(HpartitionsEq :   forall partition : paddr,
												(partition = globalIdPDChild -> False) ->
												isPDT partition s0 -> getPartitions partition s = getPartitions partition s0)
									by intuition.
							specialize (HpartitionsEq partition HidpdpartNotEq HPDTparts0).
							rewrite <- HpartitionsEq in *.
							rewrite <- HPDTpartEq in *. rewrite HPDTpartEq' in *.
							assert(HPDTparts : isPDT partition s) by trivial.
							apply isPDTLookupEq in HPDTparts. destruct HPDTparts as [pdentry' Hlookupparts'].
							subst sh1entrybts.
							eapply getPartitionsEqSHE with sh1entry0; intuition.
					++ assert(HEq : getChildren partition s = getChildren partition s0)
								by intuition.
							rewrite <- HEq.

							assert(HPDTpartEq' : isPDT partition s' = isPDT partition s).
							{
								(* DUP *)
								unfold isPDT. unfold s'.
								simpl.
								repeat rewrite beqAddrTrue.
								destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + sh1offset)) partition) eqn:beqsh1part; try(exfalso ; congruence).
								-- (* sh1eaddr = partition) *)
										rewrite <- DependentTypeLemmas.beqAddrTrue in beqsh1part.
										rewrite beqsh1part in *.
										unfold isPDT in *. unfold isSHE in *.
										destruct (lookup partition (memory s0) beqAddr) ; try(exfalso ; congruence).
										destruct v ; (intuition ; exfalso ; congruence).
								-- (* sh1eaddr <> partition) *)
										simpl.
										rewrite <- beqAddrFalse in *.
										repeat rewrite removeDupIdentity; intuition.
							}
							assert(HidpdpartNotEq : partition <> globalIdPDChild) by intuition.
							assert(HPDTparts0 : isPDT partition s0) by trivial.
							specialize (HPDTpartEq partition HidpdpartNotEq HPDTparts0).
							rewrite <- HPDTpartEq in *. rewrite HPDTpartEq' in *.
							assert(HPDTparts : isPDT partition s) by trivial.
							apply isPDTLookupEq in HPDTparts. destruct HPDTparts as [pdentry' Hlookupparts'].
							subst sh1entrybts.
							eapply getChildrenEqSHE with sh1entry0; intuition.
					++ assert(HEq : getMappedBlocks partition s = getMappedBlocks partition s0)
								by intuition.
							rewrite <- HEq.

							assert(HPDTpartEq' : isPDT partition s' = isPDT partition s).
							{
								(* DUP *)
								unfold isPDT. unfold s'.
								simpl.
								repeat rewrite beqAddrTrue.
								destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + sh1offset)) partition) eqn:beqsh1part; try(exfalso ; congruence).
								-- (* sh1eaddr = partition) *)
										rewrite <- DependentTypeLemmas.beqAddrTrue in beqsh1part.
										rewrite beqsh1part in *.
										unfold isPDT in *. unfold isSHE in *.
										destruct (lookup partition (memory s0) beqAddr) ; try(exfalso ; congruence).
										destruct v ; (intuition ; exfalso ; congruence).
								-- (* sh1eaddr <> partition) *)
										simpl.
										rewrite <- beqAddrFalse in *.
										repeat rewrite removeDupIdentity; intuition.
							}
							assert(HidpdpartNotEq : partition <> globalIdPDChild) by intuition.
							assert(HPDTparts0 : isPDT partition s0) by trivial.
							specialize (HPDTpartEq partition HidpdpartNotEq HPDTparts0).
							rewrite <- HPDTpartEq in *. rewrite HPDTpartEq' in *.
							assert(HPDTparts : isPDT partition s) by trivial.
							apply isPDTLookupEq in HPDTparts. destruct HPDTparts as [pdentry' Hlookupparts'].
							eapply getMappedBlocksEqSHE ; intuition.
					++ assert(HEq : getAccessibleMappedPaddr partition s = getAccessibleMappedPaddr partition s0)
								by intuition.
							rewrite <- HEq.

							assert(HPDTpartEq' : isPDT partition s' = isPDT partition s).
							{
								(* DUP *)
								unfold isPDT. unfold s'.
								simpl.
								repeat rewrite beqAddrTrue.
								destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + sh1offset)) partition) eqn:beqsh1part; try(exfalso ; congruence).
								-- (* sh1eaddr = partition) *)
										rewrite <- DependentTypeLemmas.beqAddrTrue in beqsh1part.
										rewrite beqsh1part in *.
										unfold isPDT in *. unfold isSHE in *.
										destruct (lookup partition (memory s0) beqAddr) ; try(exfalso ; congruence).
										destruct v ; (intuition ; exfalso ; congruence).
								-- (* sh1eaddr <> partition) *)
										simpl.
										rewrite <- beqAddrFalse in *.
										repeat rewrite removeDupIdentity; intuition.
							}
							assert(HidpdpartNotEq : partition <> globalIdPDChild) by intuition.
							assert(HPDTparts0 : isPDT partition s0) by trivial.
							specialize (HPDTpartEq partition HidpdpartNotEq HPDTparts0).
							rewrite <- HPDTpartEq in *. rewrite HPDTpartEq' in *.
							assert(HPDTparts : isPDT partition s) by trivial.
							apply isPDTLookupEq in HPDTparts. destruct HPDTparts as [pdentry' Hlookupparts'].
							eapply getAccessibleMappedPaddrEqSHE ; intuition.
			+	destruct (beqAddr (CPaddr (blockToShareInCurrPartAddr + sh1offset)) blockToShareInCurrPartAddr) eqn:btssh1bts ; try(exfalso ; congruence).
				rewrite <- beqAddrFalse in *.
				repeat rewrite removeDupIdentity ; intuition.
			+ destruct H90 as [s1 (s2 & (s3 & (s4 & (s5 & (s6 & (s7 & (s8 & (s9 & (s10 & (s11 & Hstates))))))))))].
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
																			by (unfold consistency in * ; unfold consistency1 in *; intuition).
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
																						by (unfold consistency in * ; unfold consistency1 in *; intuition).
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
																												by (unfold consistency in * ; unfold consistency1 in *; intuition).
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
														by (unfold consistency in * ; unfold consistency1 in *; intuition).
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
														by (unfold consistency in * ; unfold consistency1 in *; intuition).
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

						assert(Hcons0 : KernelStructureStartFromBlockEntryAddrIsKS s0) by (unfold consistency in * ; unfold consistency1 in * ; intuition).
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
												** (* globalIdPDChild <> (CPaddr (newBlockEntryAddr - blockidx)) *)
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
		destruct H7 as [s0 Hprops].
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
			assert(Hcons0 : nullAddrExists s0) by (unfold consistency in * ; unfold consistency1 in * ; intuition).
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
		destruct Hstates as [Hlists (Hblockcurrpart & Hstates)].
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
		assert(HSHEs10Eq : lookup sh1eaddr (memory s10) beqAddr =
								lookup sh1eaddr (memory s0) beqAddr) by intuition.

		assert(HlookupbtscurrpartEq : lookup blockToShareInCurrPartAddr (memory s) beqAddr = lookup blockToShareInCurrPartAddr (memory s10) beqAddr).
		{
			rewrite HsEq.
			cbn.
			rewrite beqAddrTrue.
			rewrite beqsh1bts.
			rewrite <- beqAddrFalse in *.
			repeat rewrite removeDupIdentity; intuition.
		}


		destruct Hlists as [Hoptionlists (olds & (n0 & (n1 & (n2 & (nbleft & Hfreeslotss)))))].

		assert(HparentEq : getPartitions multiplexer s = getPartitions multiplexer s0).
		{
			assert(HmultiEqs0 : getPartitions multiplexer olds = getPartitions multiplexer s0)
					by intuition.
		  assert(HmultiEqs : getPartitions multiplexer s = getPartitions multiplexer olds)
					by intuition.
			rewrite HmultiEqs. rewrite HmultiEqs0. trivial.
		} (* constructed along the way *)

		assert(HpdchildrenEq : getChildren globalIdPDChild s = getChildren globalIdPDChild s0).
		{
			assert(HchildrenEqs0 : getChildren globalIdPDChild olds = getChildren globalIdPDChild s0)
					by intuition.
		  assert(HchildrenEqs : getChildren globalIdPDChild s = getChildren globalIdPDChild olds)
					by intuition.
			rewrite HchildrenEqs. rewrite HchildrenEqs0. trivial.
		} (* constructed along the way *)

		assert(HpdchildMappedBlocks : forall addr, In addr (getMappedBlocks globalIdPDChild s) <->
																		In addr (newBlockEntryAddr:: (getMappedBlocks globalIdPDChild s0)))
						by intuition. (* constructed along the way *)

		assert(Hidpdchildmapped :
						         (forall addr : paddr,
						          In addr (getMappedPaddr globalIdPDChild s) <->
						          In addr
						            (getAllPaddrBlock (startAddr (blockrange bentry6))
						               (endAddr (blockrange bentry6)) ++
						             getMappedPaddr globalIdPDChild s0))) by intuition. (* constructed along the way *)

		assert(Hidpdchildconfig : getConfigBlocks globalIdPDChild s = getConfigBlocks globalIdPDChild s0).
		{
			assert(HconfigEqs0 : getConfigBlocks globalIdPDChild olds = getConfigBlocks globalIdPDChild s0)
					by intuition.
		  assert(HconfigEqs : getConfigBlocks globalIdPDChild s = getConfigBlocks globalIdPDChild olds)
					by intuition.
			rewrite HconfigEqs. rewrite HconfigEqs0. trivial.
		} (* constructed along the way *)

		assert(Hidpdchildconfigaddr : getConfigPaddr globalIdPDChild s = getConfigPaddr globalIdPDChild s0).
		{
			assert(HconfigEqs0 : getConfigPaddr globalIdPDChild olds = getConfigPaddr globalIdPDChild s0)
					by intuition.
		  assert(HconfigEqs : getConfigPaddr globalIdPDChild s = getConfigPaddr globalIdPDChild olds)
					by intuition.
			rewrite HconfigEqs. rewrite HconfigEqs0. trivial.
		} (* constructed along the way *)

		assert(HstatesFreeSlotsList : exists s11 s12,
			s11 = {|
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
					          {|
					            PDchild := PDchild sh1entry0;
					            PDflag := PDflag sh1entry0;
					            inChildLocation := blockToShareChildEntryAddr
					          |}) (memory s11) beqAddr |}
								).
		{	eexists ?[s11]. eexists ?[s12]. intuition. }

		destruct HstatesFreeSlotsList as [s11 (s12 & (Hs11 & Hs12))].

		assert(Hs12Eq : s = s12).
		{ subst s12. rewrite HsEq. subst s11. intuition. }

		assert(Hsh1PDchildbtsNulls0 : sh1entryPDchild sh1eaddr nullAddr s0).
		{
			 assert(HSHEpdchilds0 : (exists (sh1entry : Sh1Entry) (sh1entryaddr : paddr),
             lookup sh1entryaddr (memory s0) beqAddr = Some (SHE sh1entry) /\
             sh1entryPDchild sh1entryaddr PDChildAddr s0 /\
						sh1entryAddr blockToShareInCurrPartAddr sh1entryaddr s0)) by intuition.
			assert(Hpdchilds0IsNull : beqAddr nullAddr PDChildAddr = pdchildIsNull)
				by intuition.
			destruct HSHEpdchilds0 as [sh1entry' (sh1entryaddr' & (Hlookupsh1 & (Hpdchilds0 & Hsh1s0)))].
			assert(Hsh1enetryaddrEq : sh1entryaddr' = sh1eaddr).
			{ unfold sh1entryAddr in *. unfold isBE in *.
				destruct (lookup blockToShareInCurrPartAddr (memory s0) beqAddr) ; try(exfalso ; congruence).
				destruct v ; try(exfalso ; congruence).
				subst sh1entryaddr'. subst sh1eaddr. trivial.
			}
			assert(pdchildIsNull = true).
			{ assert(Hpdchild : negb pdchildIsNull = false) by intuition.
				apply negb_false_iff. trivial.
			}
			subst pdchildIsNull.
			rewrite <- DependentTypeLemmas.beqAddrTrue in *. subst PDChildAddr.
			rewrite Hsh1enetryaddrEq in *. assumption.
		}
		assert(Hsh1PDflagbtsNulls0 : sh1entryPDflag sh1eaddr false s0).
		{
			assert(HAFlag : bentryAFlag blockToShareInCurrPartAddr addrIsAccessible s0)
				by intuition.
			assert(HAccessibleNoPDFlag : AccessibleNoPDFlag s0)
				by (unfold consistency in * ; unfold consistency1 in * ; unfold consistency1 in *; intuition).
			eapply HAccessibleNoPDFlag with blockToShareInCurrPartAddr; intuition.
			unfold sh1entryAddr. unfold isBE in *.
			destruct (lookup blockToShareInCurrPartAddr (memory s0) beqAddr) ; try(exfalso ; congruence).
			destruct v ; try(exfalso ; congruence).
			subst sh1eaddr. trivial.
			assert(addrIsAccessible = true).
			{ assert(HAflag : negb addrIsAccessible = false) by intuition.
				apply negb_false_iff. trivial.
			}
			subst addrIsAccessible. assumption.
		} (* use AccessibleNoPDFlag consistency prop *)

		assert(HidpdInMapped : In idPDchild (getMappedBlocks currentPart s0))
			by admit. (*from found block : present in structure *)

		assert(HidpdIsChild : In globalIdPDChild (getChildren currentPart s0)).
		{
				unfold getChildren.
				assert(HPDTcurrParts0 : isPDT currentPart s0 ) by intuition.
				apply isPDTLookupEq in HPDTcurrParts0. destruct HPDTcurrParts0 as [pdentrycurs0 Hlookupcurrs0].
				rewrite Hlookupcurrs0.
				assert(HNDupMappedBlocks : noDupMappedBlocksList s0)
					by (unfold consistency in * ; unfold consistency1 in * ; intuition).
				unfold noDupMappedBlocksList in *.
				assert(HPDTcurrParts0 : isPDT currentPart s0) by intuition.
				specialize (HNDupMappedBlocks currentPart HPDTcurrParts0).
				unfold getPDs.
				induction (getMappedBlocks currentPart s0).
				- intuition.
				- simpl in *.
					intuition.
					-- (* a = idPDchild *)
							subst a1.
							unfold childFilter. simpl.
							assert(isChildCurrPart = true).
							{ assert(Hchild : negb isChildCurrPart = false) by intuition.
								apply negb_false_iff. trivial.
							}
							subst isChildCurrPart.
							destruct H50 ; trivial. (* isChildCurrPart *)
							assert(Hidpd : true = checkChild idPDchild s0 x /\
								(exists entry : BlockEntry,
									 lookup idPDchild (memory s0) beqAddr = Some (BE entry) /\
									 (exists sh1entry : Sh1Entry,
											sh1entryAddr idPDchild x s0 /\
											lookup x (memory s0) beqAddr = Some (SHE sh1entry)))) by intuition.
							destruct Hidpd as [Hcheckchild (idpdentry & (Hidpd & Hsh1idpd))].
							assert(HPDTIfPDFlag : PDTIfPDFlag s0)
									by (unfold consistency in * ; unfold consistency1 in * ; intuition).
							unfold PDTIfPDFlag in *.
							destruct (Hsh1idpd) as [sh1entryidpd (Hsh1entryAddridpd & Hlookupsh1idpd)].
							pose (Hconj := conj Hcheckchild Hsh1entryAddridpd).
							specialize (HPDTIfPDFlag idPDchild x Hconj).
							destruct HPDTIfPDFlag as [HAflag (HPflag & HbentryStartPD)].
							destruct HbentryStartPD as [startaddr (HbentryStart & HentryPDT)].

							unfold sh1entryAddr in *. rewrite Hidpd in *.
							unfold CPaddr in *. unfold Paddr.addPaddrIdx.
							destruct (Compare_dec.le_dec (idPDchild + sh1offset) maxAddr) ; try(exfalso ; congruence).
							simpl in *.
							assert(HoffsetEq : {|
						       p := idPDchild + sh1offset;
						       Hp := StateLib.Paddr.addPaddrIdx_obligation_1 idPDchild sh1offset l0
						     |} = {|
										p := idPDchild + sh1offset;
										Hp := ADT.CPaddr_obligation_1 (idPDchild + sh1offset) l0
									|}).
							{
								f_equal.
							}
							rewrite HoffsetEq in *.
							rewrite <- Hsh1entryAddridpd in *. (* x=...*) rewrite Hlookupsh1idpd in *.
							unfold checkChild in *. rewrite Hidpd in *. rewrite Hlookupsh1idpd in *.
							destruct (PDflag sh1entryidpd) ; intuition.
							simpl. left. rewrite Hidpd in *.
							unfold bentryStartAddr in *. rewrite Hidpd in *.
							apply eq_sym. assumption.
							assert(nullAddrExists s0)
									by (unfold consistency in * ; unfold consistency1 in * ; intuition).
							unfold nullAddrExists in *. unfold isPADDR in *. unfold nullAddr in *.
							unfold CPaddr in *.
							destruct (le_dec 0 maxAddr) ; intuition.
							assert(HnullEq : {| p := 0; Hp := ADT.CPaddr_obligation_1 0 l0 |} =
											{| p := 0; Hp := ADT.CPaddr_obligation_2 |}).
							{ f_equal. apply proof_irrelevance. }
							rewrite HnullEq in *. rewrite <- Hsh1entryAddridpd in *. (* x = *)
							rewrite Hlookupsh1idpd in *. exfalso ; congruence.
					-- (* a1 <> idPDchild*)
							apply NoDup_cons_iff in HNDupMappedBlocks.
							destruct (childFilter s0 a1) ; intuition.
							simpl. right. intuition.
			} (* from checkIsChild *)

			assert(HglobalInPartTree : In globalIdPDChild (getPartitions multiplexer s0))
				by admit. (* lemma isChild of currPart that belongs to tree
											then also belongs to partition tree *)

		assert(HstartendEq : (endAddr (blockrange bentry6) = blockend) /\ (startAddr (blockrange bentry6) = blockstart)).
		{
		apply isBELookupEq in HBEbtss0. destruct HBEbtss0 as [btsentrys0 Hlookupbtss0].
		assert(HaddrStart : bentryStartAddr blockToShareInCurrPartAddr blockstart s0)
			by intuition.
		assert(HaddrEnd : bentryEndAddr blockToShareInCurrPartAddr blockend s0)
			by intuition.
		unfold bentryStartAddr in HaddrStart. unfold bentryEndAddr in HaddrEnd.
		rewrite Hlookupbtss0 in *.
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
						CBlockEntry (read bentry2) (write bentry2) (exec bentry2)
							(present bentry2) true (blockindex bentry2) (blockrange bentry2)) by intuition.
				assert(Hbentry2 : bentry2 =
						CBlockEntry (read bentry1) (write bentry1) (exec bentry1) true
							(accessible bentry1) (blockindex bentry1) (blockrange bentry1)) by intuition.
				assert(Hbentry1 : bentry1 =
					 CBlockEntry (read bentry0) (write bentry0) (exec bentry0)
						 (present bentry0) (accessible bentry0) (blockindex bentry0)
						 (CBlock (startAddr (blockrange bentry0)) blockend)) by intuition.
				assert(Hbentry0 : bentry0 =
					 CBlockEntry (read bentry) (write bentry) (exec bentry)
						 (present bentry) (accessible bentry) (blockindex bentry)
						 (CBlock blockstart (endAddr (blockrange bentry)))) by intuition.
				assert(Hranges6Eq : blockrange bentry6 = blockrange bentry5).
				{
						subst bentry6. unfold CBlockEntry.
						destruct (lt_dec (blockindex bentry5) kernelStructureEntriesNb) ; intuition.
						destruct blockentry_d. destruct bentry5.
						intuition.
				}
				assert(Hranges5Eq : blockrange bentry5 = blockrange bentry4).
				{
						rewrite Hbentry5. unfold CBlockEntry.
						destruct (lt_dec (blockindex bentry4) kernelStructureEntriesNb) ; intuition.
						destruct blockentry_d. destruct bentry4.
						intuition.
				}
				assert(Hranges4Eq : blockrange bentry4 = blockrange bentry3).
				{
						rewrite Hbentry4. unfold CBlockEntry.
						destruct (lt_dec (blockindex bentry3) kernelStructureEntriesNb) ; intuition.
						destruct blockentry_d. destruct bentry3.
						intuition.
				}

				assert(Hranges3Eq : blockrange bentry3 = blockrange bentry2).
				{
						rewrite Hbentry3. unfold CBlockEntry.
						destruct (lt_dec (blockindex bentry2) kernelStructureEntriesNb) ; intuition.
						destruct blockentry_d. destruct bentry2.
						intuition.
				}
				assert(Hranges2Eq : blockrange bentry2 = blockrange bentry1).
				{		rewrite Hbentry2. simpl.
						unfold CBlockEntry.
						destruct (lt_dec (blockindex bentry1) kernelStructureEntriesNb) ; intuition.
						destruct blockentry_d. destruct bentry1.
						intuition.
				}
		rewrite Hranges6Eq. rewrite Hranges5Eq. rewrite Hranges4Eq. rewrite Hranges3Eq.
		rewrite Hranges2Eq.

		assert(Hstart1Eq : startAddr (blockrange bentry1) = startAddr (blockrange bentry0)). 
		{
			subst bentry1.
			unfold CBlockEntry.
			admit.
		}
		admit.

		(*assert(HendEq : (endAddr (blockrange bentry6)) = blockend).
		{
				assert(HendEq : endAddr (blockrange bentry6) = endAddr (blockrange bentry2)).
				{ assert(HendEq1 : endAddr (blockrange bentry6) = endAddr (blockrange bentry5)).
					{
						(* DUP*)
						subst bentry6.
						unfold CBlockEntry.
						destruct (lt_dec (blockindex bentry5) kernelStructureEntriesNb) ; intuition.
						destruct blockentry_d. destruct bentry5.
						intuition.
					}
					assert(HendEq2 : endAddr (blockrange bentry5) = endAddr (blockrange bentry4)).
					{
						(* DUP*)
						subst bentry5.
						unfold CBlockEntry.
						destruct (lt_dec (blockindex bentry4) kernelStructureEntriesNb) ; intuition.
						destruct blockentry_d. destruct bentry4.
						intuition.
					}
					assert(HendEq3 : endAddr (blockrange bentry4) = endAddr (blockrange bentry3)).
					{
						(* DUP*)
						subst bentry4.
						unfold CBlockEntry.
						destruct (lt_dec (blockindex bentry3) kernelStructureEntriesNb) ; intuition.
						destruct blockentry_d. destruct bentry3.
						intuition.
					}
					assert(HendEq4 : endAddr (blockrange bentry3) = endAddr (blockrange bentry2)).
					{
						(* DUP*)
						subst bentry3.
						unfold CBlockEntry.
						destruct (lt_dec (blockindex bentry2) kernelStructureEntriesNb) ; intuition.
						destruct blockentry_d. destruct bentry2.
						intuition.
					}
					rewrite HendEq1. rewrite HendEq2. rewrite HendEq3. rewrite HendEq4.
					trivial.
				}
				rewrite HstartEq in *. rewrite HendEq in *.
				rewrite Hranges6Eq. rewrite Hranges5Eq. rewrite Hranges4Eq. rewrite Hranges3Eq.
				rewrite Hranges2Eq.
				assert(Hends1Eq : (endAddr (blockrange bentry1)) = blockend).
				{		rewrite Hbentry1. simpl.
						unfold CBlockEntry. unfold CBlock.
						destruct (lt_dec (blockindex bentry0) kernelStructureEntriesNb) ; intuition.
						destruct (lt_dec (startAddr (blockrange bentry0)) blockend) ; intuition.
						destruct (lt_dec (blockend - startAddr (blockrange bentry0)) maxIdx) ; intuition.
						simpl.
						admit. admit. admit. (* false cases *)
				}
				rewrite Hends1Eq. trivial.
		}
		split. assumption. assumption.*)
		}

		assert(HaddrInBTSIfInnewB : (forall addr : paddr,
									In addr
									  (getAllPaddrBlock (startAddr (blockrange bentry6))
									     (endAddr (blockrange bentry6))) <->
									In addr (getAllPaddrAux [blockToShareInCurrPartAddr] s0))).
		{
		intro addr.
		unfold getAllPaddrAux. rewrite <- Hlookupbtss in *.
		assert(HstartEq : (startAddr (blockrange bentry6)) = blockstart) by intuition.
		assert(HendEq : (endAddr (blockrange bentry6) = blockend)) by intuition.
		apply isBELookupEq in HBEbtss0. destruct HBEbtss0 as [btsentrys0 Hlookupbtss0].
		assert(HaddrStart : bentryStartAddr blockToShareInCurrPartAddr blockstart s0)
			by intuition.
		assert(HaddrEnd : bentryEndAddr blockToShareInCurrPartAddr blockend s0)
			by intuition.
		unfold bentryStartAddr in HaddrStart. unfold bentryEndAddr in HaddrEnd.
		rewrite Hlookupbtss0 in *.
		rewrite Hlookupbtss. rewrite <- HaddrStart. rewrite <- HaddrEnd.
		rewrite <- HstartEq. rewrite <- HendEq.
		rewrite app_nil_r. intuition.
		}

	(* Prove ret *)

	(* Prove all consistency properties outside *)


	assert(HwellFormedFstShadowIfBlockEntry : wellFormedFstShadowIfBlockEntry s).
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
																by (unfold consistency in * ; unfold consistency1 in *; intuition).
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
															by (unfold consistency in * ; unfold consistency1 in *; intuition).
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
																				by (unfold consistency in * ; unfold consistency1 in *; intuition).
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
																by (unfold consistency in * ; unfold consistency1 in *; intuition).
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
																by (unfold consistency in * ; unfold consistency1 in *; intuition).
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

	assert(HPDTIfPDFlags : PDTIfPDFlag s).
	{ (* PDTIfPDFlag s *)
		assert(Hcons0 : PDTIfPDFlag s0) by (unfold consistency in * ; unfold consistency1 in * ; intuition).
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
							by (unfold consistency in * ; unfold consistency1 in *; intuition).
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
								destruct (lookup nullAddr (memory s) beqAddr) ; try(exfalso ; congruence).
								destruct v0 ; try(exfalso ; congruence).
					-- assert(Heq : CPaddr(blockToShareInCurrPartAddr + sh1offset) = nullAddr).
						{ rewrite nullAddrIs0.
							unfold CPaddr. rewrite Hj.
							destruct (le_dec 0 maxAddr) ; intuition.
							f_equal. apply proof_irrelevance.
						}
						rewrite Heq in *.
						unfold isSHE in *.
						destruct (lookup nullAddr (memory s) beqAddr) ; try(exfalso ; congruence).
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
					by (unfold consistency in * ; unfold consistency1 in * ; intuition).
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
			assert(Hcons10 : PDTIfPDFlag s10) by (unfold consistency in * ; unfold consistency1 in * ; intuition).
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

	assert(HAccessibleNoPDFlags : AccessibleNoPDFlag s).
	{ (* AccessibleNoPDFlag s *)
		unfold AccessibleNoPDFlag.
		intros block sh1entryaddr HBEblocks Hsh1entryAddr HAflag.
		unfold sh1entryPDflag.
		unfold sh1entryAddr in Hsh1entryAddr.
		unfold isBE in HBEblocks.

		(* Force BE type for block*)
		destruct(lookup block (memory s) beqAddr) eqn:Hlookup ; try(exfalso ; congruence).
		destruct v eqn:Hv ; try(exfalso ; congruence).

		(* check all possible values of block in s -> only newBlock is OK
				1) if block == newBlock then
						- we read the pdflag value of newBlock which is not modified in s so equal to s0
						- at s0 newBlock was a freeSlot so the flag was default to false
				2) if block <> any modified address then
						- lookup block s == lookup block s0
						- we didn't change the pdflag
						- explore all possible values of sh1entryaddr which didn't change
								- AccessibleNoPDFlag at s0 prevales depends on the A flag
									-- we never modified the A flag, so what holds at s0 holds at s *)
		destruct (beqAddr sh1eaddr block) eqn:beqsh1block; try(exfalso ; congruence).
		*	(* sh1eaddr = block *)
			rewrite <- DependentTypeLemmas.beqAddrTrue in beqsh1block.
			rewrite <- beqsh1block in *.
			congruence.
		* (* sh1eaddr <> block *)
			assert(HidPDs10 : isBE block s10).
			{ rewrite HsEq in Hlookup. cbn in Hlookup.
				rewrite beqAddrTrue in Hlookup.
				rewrite beqsh1block in Hlookup.
				rewrite <- beqAddrFalse in *.
				do 2 rewrite removeDupIdentity in Hlookup; intuition.
				unfold isBE. rewrite Hlookup. trivial.
			}
			assert(HlookupidpdchildEq : lookup block (memory s) beqAddr = lookup block (memory s10) beqAddr).
			{
				rewrite HsEq.
				cbn.
				rewrite beqAddrTrue.
				rewrite beqsh1block.
				rewrite <- beqAddrFalse in *.
				repeat rewrite removeDupIdentity; intuition.
			}

			(* craft hypotheses at s10 *)
			assert(Hsh1entryAddrs10 : sh1entryAddr block sh1entryaddr s10).
			{
				unfold sh1entryAddr.
				rewrite <- HlookupidpdchildEq.
				rewrite Hlookup in *.
				assumption.
			}
			assert(HbentryAFlags10 : bentryAFlag block true s10).
			{
				unfold bentryAFlag in *.
				rewrite <- HlookupidpdchildEq.
				assumption.
			}

			assert(Hcons10 : AccessibleNoPDFlag s10) by (unfold consistency in * ; unfold consistency1 in * ; intuition).
			unfold AccessibleNoPDFlag in *.
			specialize(Hcons10 block sh1entryaddr HidPDs10 Hsh1entryAddrs10 HbentryAFlags10).

			rewrite HsEq.
			cbn. rewrite beqAddrTrue.
			destruct (beqAddr sh1eaddr sh1entryaddr) eqn:beqsh1sh1entryaddr ; try(exfalso ; congruence).
			- (* sh1eaddr = sh1entryaddr *)
				rewrite <- DependentTypeLemmas.beqAddrTrue in beqsh1sh1entryaddr.
				rewrite <- beqsh1sh1entryaddr in *.
				cbn.
				assert(HpdflagEq : PDflag sh1entry0 = PDflag sh1entry).
				{
					intuition. subst sh1entry0. cbn. trivial.
				}
				rewrite HpdflagEq.
				unfold sh1entryPDflag in Hcons10. unfold isSHE in *.
				rewrite HSHEs10Eq in *.
				assert(Hlookupsh1s10 : lookup sh1eaddr (memory s0) beqAddr = Some (SHE sh1entry))
					by intuition.
				rewrite Hlookupsh1s10 in *.
				assumption.
			- (* sh1eaddr <> sh1entryaddr *)
				rewrite <- beqAddrFalse in *.
				repeat rewrite removeDupIdentity ; intuition.
	} (* end of AccessibleNoPDFlag *)

	(* Prove outside in order to use the proven properties to prove other ones *)
	assert(HFirstFreeIsBEAndFreeSlots : FirstFreeSlotPointerIsBEAndFreeSlot s).
	{ (* FirstFreeSlotPointerIsBEAndFreeSlot s *)
		assert(Hcons10 : FirstFreeSlotPointerIsBEAndFreeSlot s10) by (unfold consistency in * ; unfold consistency1 in * ; intuition).
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
									by (unfold consistency in * ; unfold consistency1 in * ; intuition).
								assert(HwellFormedShadowCutFirsts : wellFormedShadowCutIfBlockEntry s10)
									by (unfold consistency in * ; unfold consistency1 in * ; intuition).
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
												by (unfold consistency in * ; unfold consistency1 in *; intuition).
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
								- (* sh1eaddr <> (CPaddr (firstfreeslot entrypd + scoffset)) *)
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

	assert(HcurrentPartitionInPartitionsLists : currentPartitionInPartitionsList s).
	{ (* currentPartitionInPartitionsList s *)
		assert(Hcons0 : currentPartitionInPartitionsList s0)
			by (unfold consistency in * ; unfold consistency1 in * ; intuition).
		unfold currentPartitionInPartitionsList in Hcons0.

		unfold currentPartitionInPartitionsList. rewrite HparentEq.
		assert(HcurrPartEq : currentPartition s = currentPartition s0).
		{
			rewrite Hs. simpl. trivial.
		}
		rewrite HcurrPartEq in *. assumption.
	} (* end of currentPartitionInPartitionsList *)

	assert(HwellFormedShadowCutIfBlockEntrys : wellFormedShadowCutIfBlockEntry s).
	{ (* wellFormedShadowCutIfBlockEntry s*)
	intros pa HBEaddrs.

	assert(Hcons10 : wellFormedShadowCutIfBlockEntry s10) by (unfold consistency in * ; unfold consistency1 in * ; intuition).
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

	assert(HBlocksRangeFromKernelStartIsBE : BlocksRangeFromKernelStartIsBE s).
	{ (* BlocksRangeFromKernelStartIsBE s*)
		unfold BlocksRangeFromKernelStartIsBE.
		intros kernelentryaddr blockidx HKSs Hblockidx.

		assert(Hcons10 : BlocksRangeFromKernelStartIsBE s10) by (unfold consistency in * ; unfold consistency1 in * ; intuition).
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

	assert(HKernelStructureStartFromBlockEntryAddrIsKSs : KernelStructureStartFromBlockEntryAddrIsKS s).
	{ (* KernelStructureStartFromBlockEntryAddrIsKS s *)
		unfold KernelStructureStartFromBlockEntryAddrIsKS.
		intros bentryaddr blockidx Hlookup Hblockidx.

		assert(Hcons10 : KernelStructureStartFromBlockEntryAddrIsKS s10) by (unfold consistency in * ; unfold consistency1 in * ; intuition).
		unfold KernelStructureStartFromBlockEntryAddrIsKS in Hcons10.

		(* check all possible values for bentryaddr in the modified state s
				-> no entry matches -> leads to s10 -> OK

			same for the kernel start, no entry matches -> leads to s10 -> OK
		*)

		destruct (beqAddr sh1eaddr bentryaddr) eqn:beqsh1bentry; try(exfalso ; congruence).
		*	(* sh1eaddr = bentryaddr *)
			rewrite <- DependentTypeLemmas.beqAddrTrue in beqsh1bentry.
			rewrite <- beqsh1bentry in *.
			unfold isSHE in *. unfold isBE in *.
			destruct (lookup sh1eaddr (memory s) beqAddr) eqn:Hlookupscefirst ; try(exfalso ; congruence).
			destruct v ; try(exfalso ; congruence).
		* (* sh1eaddr <> bentryaddr *)
			assert(HlookupbentryEq : lookup bentryaddr (memory s) beqAddr = lookup bentryaddr (memory s10) beqAddr).
			{
				rewrite HsEq.
				cbn.
				rewrite beqAddrTrue.
				rewrite beqsh1bentry.
				rewrite <- beqAddrFalse in *.
				repeat rewrite removeDupIdentity; intuition.
			}
			assert(HBEbentrys10Eq : isBE bentryaddr s = isBE bentryaddr s10)
				by (unfold isBE ; rewrite <- HlookupbentryEq ; intuition).
			assert(HBEbentrys10 : isBE bentryaddr s10) by (rewrite <- HBEbentrys10Eq ; intuition).
			assert(Hblockidxs10Eq : bentryBlockIndex bentryaddr blockidx s = bentryBlockIndex bentryaddr blockidx s10)
				by (unfold bentryBlockIndex ; rewrite <- HlookupbentryEq ; intuition).
			assert(Hblockidxbentrys10 : bentryBlockIndex bentryaddr blockidx s10)
						by (rewrite <- Hblockidxs10Eq ; intuition).
			specialize (Hcons10 bentryaddr blockidx HBEbentrys10 Hblockidxbentrys10).

			(* check all values for bentryaddr - blockidx *)
			destruct (beqAddr sh1eaddr (CPaddr (bentryaddr - blockidx))) eqn:beqsh1ks; try(exfalso ; congruence).
			**	(* sh1eaddr = (CPaddr (bentryaddr - blockidx)) *)
					rewrite <- DependentTypeLemmas.beqAddrTrue in beqsh1ks.
					rewrite <- beqsh1ks in *.
					unfold isSHE in *. unfold isKS in *.
					destruct (lookup sh1eaddr (memory s10) beqAddr) eqn:Hsh1 ; try(exfalso ; congruence).
					destruct v ; try(exfalso ; congruence).
			** (* sh1eaddr <> (CPaddr (bentryaddr - blockidx)) *)
					unfold isKS in *.
					rewrite HsEq.
					cbn.
					rewrite beqAddrTrue.
					rewrite beqsh1ks.
					rewrite <- beqAddrFalse in *.
					repeat rewrite removeDupIdentity; intuition.
	} (* end of KernelStructureStartFromBlockEntryAddrIsKS *)

	assert(Hsh1InChildLocationIsBEs : sh1InChildLocationIsBE s).
	{ (* sh1InChildLocationIsBE s *)
		unfold sh1InChildLocationIsBE.
		intros sh1entryaddr newsh1entry Hlookup Hsh1entryNotNull.

		assert(Hcons10 : sh1InChildLocationIsBE s10) by (unfold consistency in * ; unfold consistency1 in * ; intuition).
		unfold sh1InChildLocationIsBE in Hcons10.

		(* check all possible values for sh1entryaddr in the modified state s
				-> sh1eaddr corresponds
				1) if sh1entryaddr = sh1eaddr:
						then inChildLocation is newBlockEntryAddr:
							-> it's a BE at s -> OK
				2) if sh1entryaddr <> sh1eaddr:
						- check values for inChildLocation:
							-> no modifications of type BE from s to s10 -> leads to s10 -> OK
		*)
		destruct (beqAddr sh1eaddr sh1entryaddr) eqn:beqsh1newsh1; try(exfalso ; congruence).
		*	(* sh1eaddr = sh1entryaddr *)
			rewrite <- DependentTypeLemmas.beqAddrTrue in beqsh1newsh1.
			rewrite <- beqsh1newsh1 in *.
			assert(Hlookupsh1s : lookup sh1eaddr (memory s) beqAddr = Some (SHE sh1entry1))
				by intuition.
			assert(Hsh1entryEq : sh1entry1 = newsh1entry).
			{ rewrite Hlookup in *. inversion Hlookupsh1s ; intuition. }
			rewrite <- Hsh1entryEq.
			intuition. subst sh1entry1. subst newsh1entry. simpl.
			subst blockToShareChildEntryAddr.
			assert(isBE newBlockEntryAddr s) by intuition.
			intuition.
		* (* sh1eaddr <> sh1entryaddr *)
			assert(Hlookupsh1entryEq : lookup sh1entryaddr (memory s) beqAddr = lookup sh1entryaddr (memory s10) beqAddr).
			{
				rewrite HsEq.
				cbn.
				rewrite beqAddrTrue.
				rewrite beqsh1newsh1.
				rewrite <- beqAddrFalse in *.
				repeat rewrite removeDupIdentity; intuition.
			}
			assert(Hlookupsh1entrys10 : lookup sh1entryaddr (memory s10) beqAddr = Some (SHE newsh1entry))
				by (rewrite <- Hlookupsh1entryEq ; intuition).

			specialize(Hcons10 sh1entryaddr newsh1entry Hlookupsh1entrys10 Hsh1entryNotNull).

			(* check all values for inchildlocation *)
			destruct (beqAddr sh1eaddr (inChildLocation newsh1entry)) eqn:beqsh1loc; try(exfalso ; congruence).
			**	(* sh1eaddr = (inChildLocation newsh1entry) *)
					rewrite <- DependentTypeLemmas.beqAddrTrue in beqsh1loc.
					rewrite <- beqsh1loc in *.
					unfold isSHE in *. unfold isBE in *.
					destruct (lookup sh1eaddr (memory s10) beqAddr) eqn:Hsh1 ; try(exfalso ; congruence).
					destruct v ; try(exfalso ; congruence).
			** (* sh1eaddr <> (inChildLocation newsh1entry) *)
					unfold isBE in *.
					rewrite HsEq.
					cbn.
					rewrite beqAddrTrue.
					rewrite beqsh1loc.
					rewrite <- beqAddrFalse in *.
					repeat rewrite removeDupIdentity; intuition.
	} (* end of sh1InChildLocationIsBE *)

	assert(HStructurePointerIsKSs : StructurePointerIsKS s).
	{ (* StructurePointerIsKS s *)
		unfold StructurePointerIsKS.
		intros pdentryaddr pdentry' Hlookup.

		assert(Hcons10 : StructurePointerIsKS s10) by (unfold consistency in * ; unfold consistency1 in * ; intuition).
		unfold StructurePointerIsKS in Hcons10.

		(* check all possible values for pdentryaddr in the modified state s
				-> no entry matches -> leads to s10 -> OK

			same for the kernel start, no entry matches -> leads to s10 -> OK
		*)

		(* Check all values *)
		destruct (beqAddr sh1eaddr pdentryaddr) eqn:beqsh1pd; try(exfalso ; congruence).
		*	(* sh1eaddr = pdentryaddr *)
			rewrite <- DependentTypeLemmas.beqAddrTrue in beqsh1pd.
			rewrite <- beqsh1pd in *.
			unfold isPDT in *. unfold isSHE in *.
			destruct (lookup sh1eaddr (memory s10) beqAddr) eqn:Hlookupscefirst ; try(exfalso ; congruence).
		* (* sh1eaddr <> pdentryaddr *)
			assert(HlookuppdEq : lookup pdentryaddr (memory s) beqAddr = lookup pdentryaddr (memory s10) beqAddr).
			{
				rewrite HsEq.
				cbn.
				rewrite beqAddrTrue.
				rewrite beqsh1pd.
				rewrite <- beqAddrFalse in *.
				repeat rewrite removeDupIdentity; intuition.
			}
			assert(Hlookuppds10 : lookup pdentryaddr (memory s10) beqAddr = Some (PDT pdentry'))
				by (rewrite <- HlookuppdEq ; intuition).
			specialize (Hcons10 pdentryaddr pdentry' Hlookuppds10).

			(* check all values for KS *)
			destruct (beqAddr sh1eaddr (structure pdentry')) eqn:beqsh1ks; try(exfalso ; congruence).
			**	(* sh1eaddr = (structure pdentry')) *)
					rewrite <- DependentTypeLemmas.beqAddrTrue in beqsh1ks.
					rewrite <- beqsh1ks in *.
					unfold isSHE in *. unfold isKS in *.
					destruct (lookup sh1eaddr (memory s10) beqAddr) eqn:Hsh1 ; try(exfalso ; congruence).
					destruct v ; try(exfalso ; congruence).
			** (* sh1eaddr <> (structure pdentry') *)
					unfold isKS in *.
					rewrite HsEq.
					cbn.
					rewrite beqAddrTrue.
					rewrite beqsh1ks.
					rewrite <- beqAddrFalse in *.
					repeat rewrite removeDupIdentity; intuition.
	} (* end of StructurePointerIsKS *)

	assert(HNextKSIsKSs : NextKSIsKS s).
	{ (* NextKSIsKS s *)
		unfold NextKSIsKS.
		intros ksaddr nextksaddr next HKS Hnextksaddr Hnext HnextNotNull.

		assert(Hcons10 : NextKSIsKS s10) by (unfold consistency in * ; unfold consistency1 in * ; intuition).
		unfold NextKSIsKS in Hcons10.

		(* check all possible values for ksaddr in the modified state s
				-> no entry matches -> leads to s10 -> OK

			same for the kernel start and the next KS, no entry matches -> leads to s10 -> OK
		*)

		(* Check all values *)
		destruct (beqAddr sh1eaddr ksaddr) eqn:beqsh1ks; try(exfalso ; congruence).
		*	(* sh1eaddr = ksaddr *)
			rewrite <- DependentTypeLemmas.beqAddrTrue in beqsh1ks.
			rewrite <- beqsh1ks in *.
			unfold isKS in *. unfold isSHE in *.
			destruct (lookup sh1eaddr (memory s) beqAddr) eqn:Hlookupscefirst ; try(exfalso ; congruence).
			destruct v ; try(exfalso ; congruence).
		* (* sh1eaddr <> ksaddr *)
			assert(HlookupksEq : lookup ksaddr (memory s) beqAddr = lookup ksaddr (memory s10) beqAddr).
			{
				rewrite HsEq.
				cbn.
				rewrite beqAddrTrue.
				rewrite beqsh1ks.
				rewrite <- beqAddrFalse in *.
				repeat rewrite removeDupIdentity; intuition.
			}
			assert(Hkss10Eq : isKS ksaddr s = isKS ksaddr s10)
				by (unfold isKS ; rewrite <- HlookupksEq ; intuition).
			assert(HKSs10 : isKS ksaddr s10) by (rewrite <- Hkss10Eq ; intuition).
			assert(HnextKSaddrs10Eq : nextKSAddr ksaddr nextksaddr s = nextKSAddr ksaddr nextksaddr s10)
				by (unfold nextKSAddr ; rewrite <- HlookupksEq ; intuition).
			assert(HnextKSaddrs10 : nextKSAddr ksaddr nextksaddr s10)
						by (rewrite <- HnextKSaddrs10Eq ; intuition).
			assert(HnextKSentrys10Eq : nextKSentry nextksaddr next s = nextKSentry nextksaddr next s10).
			{	unfold nextKSentry.
				unfold nextKSAddr in *. rewrite <- HlookupksEq in *.
				destruct (lookup ksaddr (memory s) beqAddr) eqn:Hlookupksaddr ; try(exfalso ; congruence).
				destruct v eqn:Hv ; try(exfalso ; congruence).
				rewrite HsEq.
				cbn.
				rewrite beqAddrTrue.
				destruct (beqAddr sh1eaddr nextksaddr) eqn:beqsh1nextks ; try(exfalso ; congruence).
				- (* sh1eaddr = nextksaddr *)
					rewrite <- DependentTypeLemmas.beqAddrTrue in beqsh1nextks.
					rewrite <- beqsh1nextks in *.
					unfold isSHE in *. unfold nextKSentry in *.
					destruct (lookup sh1eaddr (memory s) beqAddr) eqn:Hlookupscefirst ; try(exfalso ; congruence).
					destruct v0 ; try(exfalso ; congruence).
				- (* sh1eaddr <> nextksaddr *)
					rewrite <- beqAddrFalse in *.
					repeat rewrite removeDupIdentity; intuition.
			}
			assert(HnextKSentrys10 : nextKSentry nextksaddr next s10)
						by (rewrite <- HnextKSentrys10Eq ; intuition).
			specialize (Hcons10 ksaddr nextksaddr next HKSs10 HnextKSaddrs10 HnextKSentrys10 HnextNotNull).

			(* check all values for next -> no entry matches -> leads to s10 *)
			destruct (beqAddr sh1eaddr next) eqn:beqsh1nextks; try(exfalso ; congruence).
			**	(* sh1eaddr = next *)
					rewrite <- DependentTypeLemmas.beqAddrTrue in beqsh1nextks.
					rewrite <- beqsh1nextks in *.
					unfold isSHE in *. unfold isKS in *.
					destruct (lookup sh1eaddr (memory s10) beqAddr) eqn:Hsh1 ; try(exfalso ; congruence).
					destruct v ; try(exfalso ; congruence).
			** (* sh1eaddr <> next *)
					unfold isKS in *.
					rewrite HsEq.
					cbn.
					rewrite beqAddrTrue.
					rewrite beqsh1nextks.
					rewrite <- beqAddrFalse in *.
					repeat rewrite removeDupIdentity; intuition.
	} (* end of NextKSIsKS *)

	assert(HNextKSOffsetIsPADDRs : NextKSOffsetIsPADDR s).
	{ (* NextKSOffsetIsPADDR s *)
		unfold NextKSOffsetIsPADDR.
		intros ksaddr nextksaddr HKS Hnextksaddr.

		assert(Hcons10 : NextKSOffsetIsPADDR s10) by (unfold consistency in * ; unfold consistency1 in * ; intuition).
		unfold NextKSOffsetIsPADDR in Hcons10.

		(* check all possible values for ksaddr in the modified state s
				-> no entry matches -> leads to s10 -> OK

			same for the next KS offset, no entry matches type PADDR -> leads to s10 -> OK
		*)

		(* Check all values *)
		destruct (beqAddr sh1eaddr ksaddr) eqn:beqsh1ks; try(exfalso ; congruence).
		*	(* sh1eaddr = ksaddr *)
			rewrite <- DependentTypeLemmas.beqAddrTrue in beqsh1ks.
			rewrite <- beqsh1ks in *.
			unfold isKS in *. unfold isSHE in *.
			destruct (lookup sh1eaddr (memory s) beqAddr) eqn:Hlookupscefirst ; try(exfalso ; congruence).
			destruct v ; try(exfalso ; congruence).
		* (* sh1eaddr <> ksaddr *)
			assert(HlookupksEq : lookup ksaddr (memory s) beqAddr = lookup ksaddr (memory s10) beqAddr).
			{
				rewrite HsEq.
				cbn.
				rewrite beqAddrTrue.
				rewrite beqsh1ks.
				rewrite <- beqAddrFalse in *.
				repeat rewrite removeDupIdentity; intuition.
			}
			assert(Hkss10Eq : isKS ksaddr s = isKS ksaddr s10)
				by (unfold isKS ; rewrite <- HlookupksEq ; intuition).
			assert(HKSs10 : isKS ksaddr s10) by (rewrite <- Hkss10Eq ; intuition).
			assert(HnextKSaddrs10Eq : nextKSAddr ksaddr nextksaddr s = nextKSAddr ksaddr nextksaddr s10)
				by (unfold nextKSAddr ; rewrite <- HlookupksEq ; intuition).
			assert(HnextKSaddrs10 : nextKSAddr ksaddr nextksaddr s10)
						by (rewrite <- HnextKSaddrs10Eq ; intuition).
			specialize (Hcons10 ksaddr nextksaddr HKSs10 HnextKSaddrs10).

			(* check all values for next -> no entry matches -> leads to s10 *)
			destruct (beqAddr sh1eaddr nextksaddr) eqn:beqsh1nextks; try(exfalso ; congruence).
			**	(* sh1eaddr = nextksaddr *)
					rewrite <- DependentTypeLemmas.beqAddrTrue in beqsh1nextks.
					rewrite <- beqsh1nextks in *.
					unfold isSHE in *. unfold isPADDR in *.
					destruct (lookup sh1eaddr (memory s10) beqAddr) eqn:Hsh1 ; try(exfalso ; congruence).
					destruct v ; try(exfalso ; congruence).
			** (* sh1eaddr <> nextksaddr *)
					unfold isPADDR in *.
					rewrite HsEq.
					cbn.
					rewrite beqAddrTrue.
					rewrite beqsh1nextks.
					rewrite <- beqAddrFalse in *.
					repeat rewrite removeDupIdentity; intuition.
	} (* end of NextKSOffsetIsPADDR *)

	assert(HNoDupInFreeSlotsLists : NoDupInFreeSlotsList s).
	{ (* NoDupInFreeSlotsList s *)
		unfold NoDupInFreeSlotsList.
		intros pd entrypd Hlookuppd.

		assert(Hcons10 : NoDupInFreeSlotsList s10) by (unfold consistency in * ; unfold consistency1 in * ; intuition).
		unfold NoDupInFreeSlotsList in Hcons10.

		(* check all possible values for pd in the modified state s
				-> no entry matches
				-> it is an unknown pd, we must prove there are still noDup in that list
						by showing this list was never modified
				-> compute the list at each modified state and check not changed from s10 -> OK
	*)

	(* Check all values *)
	destruct (beqAddr sh1eaddr pd) eqn:beqsh1pd; try(exfalso ; congruence).
	*	(* sh1eaddr = pd *)
		rewrite <- DependentTypeLemmas.beqAddrTrue in beqsh1pd.
		rewrite <- beqsh1pd in *.
		unfold isPDT in *. unfold isSHE in *.
		destruct (lookup sh1eaddr (memory s) beqAddr) eqn:Hlookupscefirst ; try(exfalso ; congruence).
	* (* sh1eaddr <> pd *)
		assert(HlookuppdEq : lookup pd (memory s) beqAddr = lookup pd (memory s10) beqAddr).
		{
			rewrite HsEq.
			cbn.
			rewrite beqAddrTrue.
			rewrite beqsh1pd.
			rewrite <- beqAddrFalse in *.
			repeat rewrite removeDupIdentity; intuition.
		}
		assert(Hlookuppds10 : lookup pd (memory s10) beqAddr = Some (PDT entrypd))
			by (rewrite <- HlookuppdEq ; intuition).
		specialize (Hcons10 pd entrypd Hlookuppds10).

		(* we must prove the list has not changed by recomputing each
				intermediate steps and check at that time *)

		unfold getFreeSlotsList.
		unfold getFreeSlotsList in *.
		rewrite HlookuppdEq. rewrite Hlookuppds10 in *.
		destruct (beqAddr (firstfreeslot entrypd) nullAddr) ; try(exfalso ; congruence).
		---- (* optionfreeslotslist = NIL *)
					destruct Hcons10 as [optionfreeslotslist (Hnil & HwellFormed & HNoDup)].
					exists optionfreeslotslist. intuition.
		---- 	(* optionfreeslotslist <> NIL *)
					(* show list equality between s10 and s*)
					assert(HstatesFreeSlotsList : exists (*s11 s12*) n1 nbleft,
	nbleft = (ADT.nbfreeslots entrypd) /\
	(*s11 = {|
		   currentPartition := currentPartition s10;
		   memory := add sh1eaddr
                (SHE
                   {|
                     PDchild := globalIdPDChild;
                     PDflag := PDflag sh1entry;
                     inChildLocation := inChildLocation sh1entry
                   |}) (memory s10) beqAddr |} /\*)
	getFreeSlotsListRec n1 (firstfreeslot entrypd) s11 nbleft =
	getFreeSlotsListRec (maxIdx+1) (firstfreeslot entrypd) s10 nbleft
				 /\
		n1 <= maxIdx+1 /\ nbleft < n1 /\
	(*/\ s12 = {|
		   currentPartition := currentPartition s11;
		   memory := add sh1eaddr
             (SHE
                {|
                  PDchild := PDchild sh1entry0;
                  PDflag := PDflag sh1entry0;
                  inChildLocation := blockToShareChildEntryAddr
                |}) (memory s11) beqAddr |} /\*)
	getFreeSlotsListRec n1 (firstfreeslot entrypd) s12 nbleft =
				getFreeSlotsListRec n1 (firstfreeslot entrypd) s11 nbleft
					).
					{	(*eexists ?[s11]. eexists ?[s12].*) eexists ?[n1]. eexists.
						(*split. intuition.*)
						split. intuition.
						(*set (s11 := {| currentPartition := _ |}).*)
						(* prove outside *)
						assert(Hfreeslotss1 : getFreeSlotsListRec ?n1 (firstfreeslot entrypd) s11 (ADT.nbfreeslots entrypd) =
							getFreeSlotsListRec (maxIdx + 1) (firstfreeslot entrypd) s10 (ADT.nbfreeslots entrypd)).
						{	rewrite Hs11.
							apply getFreeSlotsListRecEqSHE.
							-- 	intro Hfirstpdeq.
									assert(HFirstFreeSlotPointerIsBEAndFreeSlots10 : FirstFreeSlotPointerIsBEAndFreeSlot s10)
										by (unfold consistency in * ; unfold consistency1 in * ; intuition).
									unfold FirstFreeSlotPointerIsBEAndFreeSlot in *.
									specialize (HFirstFreeSlotPointerIsBEAndFreeSlots10 pd entrypd Hlookuppds10).
									destruct HFirstFreeSlotPointerIsBEAndFreeSlots10.
									--- intro HfirstfreeNull.
											assert(HnullAddrExistss0 : nullAddrExists s10)
												by (unfold consistency in * ; unfold consistency1 in * ; intuition).
											unfold nullAddrExists in *.
											unfold isPADDR in *.
											rewrite HfirstfreeNull in *. rewrite <- Hfirstpdeq in *.
											unfold isSHE in *.
											destruct (lookup nullAddr (memory s10) beqAddr) ; try(exfalso ; congruence).
											destruct v ; try(exfalso ; congruence).
									--- rewrite Hfirstpdeq in *.
											unfold isBE in *. unfold isSHE in *.
											destruct (lookup sh1eaddr (memory s10) beqAddr) ; try (exfalso ; congruence).
											destruct v ; try(exfalso ; congruence).
							-- 	unfold isBE. unfold isSHE in *.
									destruct (lookup sh1eaddr (memory s10) beqAddr) ; try (exfalso ; congruence).
									destruct v ; try(exfalso ; congruence).
									easy.
							-- 	unfold isPADDR. unfold isSHE in *.
									destruct (lookup sh1eaddr (memory s10) beqAddr) ; try (exfalso ; congruence).
									destruct v ; try(exfalso ; congruence).
									easy.
						}
						(*set (s12 := {| currentPartition := _ |}).*)
						assert(Hfreeslotss2 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot entrypd) s12 (ADT.nbfreeslots entrypd) =
							getFreeSlotsListRec (maxIdx + 1) (firstfreeslot entrypd) s11 (ADT.nbfreeslots entrypd)).
						{
							(* COPY of previous *)
							rewrite Hs12.
							apply getFreeSlotsListRecEqSHE.
							-- 	intro Hfirstpdeq.
									assert(HFirstFreeSlotPointerIsBEAndFreeSlots10 : FirstFreeSlotPointerIsBEAndFreeSlot s10)
										by (unfold consistency in * ; unfold consistency1 in * ; intuition).
									unfold FirstFreeSlotPointerIsBEAndFreeSlot in *.
									specialize (HFirstFreeSlotPointerIsBEAndFreeSlots10 pd entrypd Hlookuppds10).
									destruct HFirstFreeSlotPointerIsBEAndFreeSlots10.
									--- intro HfirstfreeNull.
											assert(HnullAddrExistss0 : nullAddrExists s10)
												by (unfold consistency in * ; unfold consistency1 in * ; intuition).
											unfold nullAddrExists in *.
											unfold isPADDR in *.
											rewrite HfirstfreeNull in *. rewrite <- Hfirstpdeq in *.
											unfold isSHE in *.
											destruct (lookup nullAddr (memory s10) beqAddr) ; try(exfalso ; congruence).
											destruct v ; try(exfalso ; congruence).
									--- rewrite Hfirstpdeq in *.
											unfold isBE in *. unfold isSHE in *.
											destruct (lookup sh1eaddr (memory s10) beqAddr) ; try (exfalso ; congruence).
											destruct v ; try(exfalso ; congruence).
							-- 	unfold isBE.
									subst s11. simpl. rewrite beqAddrTrue.
									easy.
							-- 	unfold isPADDR.
									subst s11. simpl. rewrite beqAddrTrue.
									easy.
						}
						(*fold s11. fold s12.*)
						intuition.
						assert(HcurrLtmaxIdx : ADT.nbfreeslots entrypd <= maxIdx).
						{ intuition. apply IdxLtMaxIdx. }
						lia.
					}
					destruct HstatesFreeSlotsList as [(*s11 (s12 &*)
														n1' (nbleft' & (Hnbleft & Hnewstates))].
					(*assert(Hs12Eq : s12 = s).
					{ intuition. subst s1. subst s2. subst s3. subst s4. subst s5. subst s6.
						subst s7. subst s8. subst s9. subst s10. subst s11. subst s12.
						rewrite Hs. f_equal.
					}*)
					rewrite <- Hs12Eq in *.
					assert(HfreeslotsEq : getFreeSlotsListRec n1' (firstfreeslot entrypd) s (ADT.nbfreeslots entrypd) =
																getFreeSlotsListRec (maxIdx+1) (firstfreeslot entrypd) s10 (ADT.nbfreeslots entrypd)).
					{
						intuition.
						subst nbleft'.
						(* rewrite all previous getFreeSlotsListRec equalities *)
						assert(FreeSlotsEq1 :  getFreeSlotsListRec n1' (firstfreeslot entrypd) s (ADT.nbfreeslots entrypd) =
  											getFreeSlotsListRec n1' (firstfreeslot entrypd) s11 (ADT.nbfreeslots entrypd)) by intuition.
						assert(FreeSlotsEq2 :   getFreeSlotsListRec n1' (firstfreeslot entrypd) s11 (ADT.nbfreeslots entrypd) =
  											getFreeSlotsListRec (maxIdx + 1) (firstfreeslot entrypd) s10 (ADT.nbfreeslots entrypd))
							by intuition.
						rewrite FreeSlotsEq1. rewrite FreeSlotsEq2.
						reflexivity.
					}
					assert (HfreeslotsEqn1 : getFreeSlotsListRec n1' (firstfreeslot entrypd) s (ADT.nbfreeslots entrypd)
																		= getFreeSlotsListRec (maxIdx + 1) (firstfreeslot entrypd) s (ADT.nbfreeslots entrypd)).
					{ eapply getFreeSlotsListRecEqN ; intuition.
						subst nbleft'. lia.
						assert (HnbLtmaxIdx : ADT.nbfreeslots entrypd <= maxIdx) by apply IdxLtMaxIdx.
						lia.
					}
					rewrite <- HfreeslotsEqn1. rewrite HfreeslotsEq. intuition.
	} (* end of NoDupInFreeSlotsList *)

	assert(HfreeSlotsListIsFreeSlots : freeSlotsListIsFreeSlot s).
	{ (* freeSlotsListIsFreeSlot s*)
		unfold freeSlotsListIsFreeSlot.
		intros pd freeslotaddr optionfreeslotslist freeslotslist HPDTpds.
		intros (HoptionfreeSlotsList&HwellFormedFreeSlots) (HfreeSlotsList & HfreeSlotInList).
		intro HfreeSlotNotNull.

		assert(Hcons10 : freeSlotsListIsFreeSlot s10) by (unfold consistency in * ; unfold consistency1 in * ; intuition).
		unfold freeSlotsListIsFreeSlot in Hcons10.

		(* check all possible values for pd in the modified state s
				-> no entry matches
				-> it is an unknown pd, we must prove an element of that pd's free slots list
						is still a free slot
						by showing this list was never modified
							-> compute the list at each modified state and check not changed from s10 -> OK
			check all possible values for freeslotaddr in the modified state s
				-> no entry matches -> element has not changed and the list didn't change
				-> relates to another free slot than what is modified in the state
						(from another pd only)
					-> leads to s10 -> OK
		*)


		(* Check all values *)
		destruct (beqAddr sh1eaddr pd) eqn:beqsh1pd; try(exfalso ; congruence).
		*	(* sh1eaddr = pd *)
			rewrite <- DependentTypeLemmas.beqAddrTrue in beqsh1pd.
			rewrite <- beqsh1pd in *.
			unfold isPDT in *. unfold isSHE in *.
			destruct (lookup sh1eaddr (memory s) beqAddr) eqn:Hlookupscefirst ; try(exfalso ; congruence).
			destruct v ; try(exfalso ; congruence).
		* (* sh1eaddr <> pd *)
			assert(HlookuppdEq : lookup pd (memory s) beqAddr = lookup pd (memory s10) beqAddr).
			{
				rewrite HsEq.
				cbn.
				rewrite beqAddrTrue.
				rewrite beqsh1pd.
				rewrite <- beqAddrFalse in *.
				repeat rewrite removeDupIdentity; intuition.
			}
			apply isPDTLookupEq in HPDTpds. destruct HPDTpds as [pdentry' Hlookuppds].
			assert(HPDTpds10 : isPDT pd s10)
				by (unfold isPDT ; rewrite <- HlookuppdEq ; rewrite Hlookuppds ; intuition).
			specialize (Hcons10 pd freeslotaddr).

			(* DUP of NoDupInFreeSlotsList *)
			(* we must prove the list has not changed by recomputing each
					intermediate steps and check at that time *)

			assert(HfreeSlotsListEq : optionfreeslotslist = getFreeSlotsList pd s10 /\
		 						wellFormedFreeSlotsList optionfreeslotslist <> False).
			{
				unfold getFreeSlotsList.
				unfold getFreeSlotsList in *.
				apply isPDTLookupEq in HPDTpds10. destruct HPDTpds10 as [entrypd Hlookuppds10].
				rewrite HlookuppdEq in *.
				rewrite Hlookuppds10 in *.
				destruct (beqAddr (firstfreeslot entrypd) nullAddr) ; try(exfalso ; congruence).
				---- (* optionfreeslotslist = NIL *)
							intuition.
				---- 	(* optionfreeslotslist <> NIL *)
							(* show list equality between s10 and s*)
							assert(HstatesFreeSlotsList : exists (*s11 s12*) n1 nbleft,
		nbleft = (ADT.nbfreeslots entrypd) /\
		(*s11 = {|
				 currentPartition := currentPartition s10;
				 memory := add sh1eaddr
		              (SHE
		                 {|
		                   PDchild := globalIdPDChild;
		                   PDflag := PDflag sh1entry;
		                   inChildLocation := inChildLocation sh1entry
		                 |}) (memory s10) beqAddr |} /\*)
		getFreeSlotsListRec n1 (firstfreeslot entrypd) s11 nbleft =
		getFreeSlotsListRec (maxIdx+1) (firstfreeslot entrypd) s10 nbleft
					 /\
			n1 <= maxIdx+1 /\ nbleft < n1 /\
		(*/\ s12 = {|
				 currentPartition := currentPartition s11;
				 memory := add sh1eaddr
		           (SHE
		              {|
		                PDchild := PDchild sh1entry0;
		                PDflag := PDflag sh1entry0;
		                inChildLocation := blockToShareChildEntryAddr
		              |}) (memory s11) beqAddr |} /\*)
		getFreeSlotsListRec n1 (firstfreeslot entrypd) s12 nbleft =
					getFreeSlotsListRec n1 (firstfreeslot entrypd) s11 nbleft
						).
						{	(*eexists ?[s11]. eexists ?[s12].*) eexists ?[n1]. eexists.
							(*split. intuition.*)
							split. intuition.
							(*set (s11 := {| currentPartition := _ |}).*)
							(* prove outside *)
							assert(Hfreeslotss1 : getFreeSlotsListRec ?n1 (firstfreeslot entrypd) s11 (ADT.nbfreeslots entrypd) =
								getFreeSlotsListRec (maxIdx + 1) (firstfreeslot entrypd) s10 (ADT.nbfreeslots entrypd)).
							{	rewrite Hs11.
								apply getFreeSlotsListRecEqSHE.
								-- 	intro Hfirstpdeq.
										assert(HFirstFreeSlotPointerIsBEAndFreeSlots10 : FirstFreeSlotPointerIsBEAndFreeSlot s10)
											by (unfold consistency in * ; unfold consistency1 in * ; intuition).
										unfold FirstFreeSlotPointerIsBEAndFreeSlot in *.
										specialize (HFirstFreeSlotPointerIsBEAndFreeSlots10 pd entrypd Hlookuppds10).
										destruct HFirstFreeSlotPointerIsBEAndFreeSlots10.
										--- intro HfirstfreeNull.
												assert(HnullAddrExistss0 : nullAddrExists s10)
													by (unfold consistency in * ; unfold consistency1 in * ; intuition).
												unfold nullAddrExists in *.
												unfold isPADDR in *.
												rewrite HfirstfreeNull in *. rewrite <- Hfirstpdeq in *.
												unfold isSHE in *.
												destruct (lookup nullAddr (memory s10) beqAddr) ; try(exfalso ; congruence).
												destruct v ; try(exfalso ; congruence).
										--- rewrite Hfirstpdeq in *.
												unfold isBE in *. unfold isSHE in *.
												destruct (lookup sh1eaddr (memory s10) beqAddr) ; try (exfalso ; congruence).
												destruct v ; try(exfalso ; congruence).
								-- 	unfold isBE. unfold isSHE in *.
										destruct (lookup sh1eaddr (memory s10) beqAddr) ; try (exfalso ; congruence).
										destruct v ; try(exfalso ; congruence).
										easy.
								-- 	unfold isPADDR. unfold isSHE in *.
										destruct (lookup sh1eaddr (memory s10) beqAddr) ; try (exfalso ; congruence).
										destruct v ; try(exfalso ; congruence).
										easy.
							}
							(*set (s12 := {| currentPartition := _ |}).*)
							assert(Hfreeslotss2 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot entrypd) s12 (ADT.nbfreeslots entrypd) =
								getFreeSlotsListRec (maxIdx + 1) (firstfreeslot entrypd) s11 (ADT.nbfreeslots entrypd)).
							{
								(* COPY of previous *)
								rewrite Hs12.
								apply getFreeSlotsListRecEqSHE.
								-- 	intro Hfirstpdeq.
										assert(HFirstFreeSlotPointerIsBEAndFreeSlots10 : FirstFreeSlotPointerIsBEAndFreeSlot s10)
											by (unfold consistency in * ; unfold consistency1 in * ; intuition).
										unfold FirstFreeSlotPointerIsBEAndFreeSlot in *.
										specialize (HFirstFreeSlotPointerIsBEAndFreeSlots10 pd entrypd Hlookuppds10).
										destruct HFirstFreeSlotPointerIsBEAndFreeSlots10.
										--- intro HfirstfreeNull.
												assert(HnullAddrExistss0 : nullAddrExists s10)
													by (unfold consistency in * ; unfold consistency1 in * ; intuition).
												unfold nullAddrExists in *.
												unfold isPADDR in *.
												rewrite HfirstfreeNull in *. rewrite <- Hfirstpdeq in *.
												unfold isSHE in *.
												destruct (lookup nullAddr (memory s10) beqAddr) ; try(exfalso ; congruence).
												destruct v ; try(exfalso ; congruence).
										--- rewrite Hfirstpdeq in *.
												unfold isBE in *. unfold isSHE in *.
												destruct (lookup sh1eaddr (memory s10) beqAddr) ; try (exfalso ; congruence).
												destruct v ; try(exfalso ; congruence).
								-- 	unfold isBE.
										subst s11. simpl. rewrite beqAddrTrue.
										easy.
								-- 	unfold isPADDR.
										subst s11. simpl. rewrite beqAddrTrue.
										easy.
							}
							(*fold s11. fold s12.*)
							intuition.
							assert(HcurrLtmaxIdx : ADT.nbfreeslots entrypd <= maxIdx).
							{ intuition. apply IdxLtMaxIdx. }
							lia.
						}
						destruct HstatesFreeSlotsList as [(*s11 (s12 &*)
															n1'  (nbleft' & (Hnbleft & Hnewstates))].
						(*assert(Hs12Eq : s12 = s).
						{ intuition. subst s1. subst s2. subst s3. subst s4. subst s5. subst s6.
							subst s7. subst s8. subst s9. subst s10. subst s11. subst s12.
							rewrite Hs. f_equal.
						}*)
						rewrite <- Hs12Eq in *.
						assert(HfreeslotsEq : getFreeSlotsListRec n1' (firstfreeslot entrypd) s (ADT.nbfreeslots entrypd) =
																	getFreeSlotsListRec (maxIdx+1) (firstfreeslot entrypd) s10 (ADT.nbfreeslots entrypd)).
						{
							intuition.
							subst nbleft'.
							(* rewrite all previous getFreeSlotsListRec equalities *)
							assert(HFreeSlotsEq1 :   getFreeSlotsListRec n1' (firstfreeslot entrypd) s (ADT.nbfreeslots entrypd) =
  										getFreeSlotsListRec n1' (firstfreeslot entrypd) s11 (ADT.nbfreeslots entrypd))
									by intuition.
							assert(HFreeSlotsEq2 :  getFreeSlotsListRec n1' (firstfreeslot entrypd) s11 (ADT.nbfreeslots entrypd) =
												getFreeSlotsListRec (maxIdx + 1) (firstfreeslot entrypd) s10
													(ADT.nbfreeslots entrypd))
									by intuition.
							rewrite HFreeSlotsEq1. rewrite <- HFreeSlotsEq2.
							reflexivity.
						}
						assert (HfreeslotsEqn1 : getFreeSlotsListRec n1' (firstfreeslot entrypd) s (ADT.nbfreeslots entrypd)
																			= getFreeSlotsListRec (maxIdx + 1) (firstfreeslot entrypd) s (ADT.nbfreeslots entrypd)).
						{ eapply getFreeSlotsListRecEqN ; intuition.
							subst nbleft'. lia.
							assert (HnbLtmaxIdx : ADT.nbfreeslots entrypd <= maxIdx) by apply IdxLtMaxIdx.
							lia.
						}
						rewrite <- HfreeslotsEq. rewrite HfreeslotsEqn1. intuition.
			}

			specialize (Hcons10 optionfreeslotslist freeslotslist HPDTpds10 HfreeSlotsListEq).
			assert(HInfreeSlot : freeslotslist = filterOptionPaddr optionfreeslotslist /\
						   In freeslotaddr freeslotslist) by intuition.
			specialize (Hcons10 HInfreeSlot HfreeSlotNotNull).

			(* dismiss all impossible values for freeslotaddr *)
			destruct (beqAddr sh1eaddr freeslotaddr) eqn:beqfsh1free; try(exfalso ; congruence).
			---- (* sh1eaddr = freeslotaddr *)
						rewrite <- DependentTypeLemmas.beqAddrTrue in beqfsh1free.
						rewrite <- beqfsh1free in *.
						unfold isSHE in *.
						unfold isFreeSlot in *.
						destruct (lookup sh1eaddr (memory s10) beqAddr) ; try(exfalso ; congruence).
						destruct v ; try(exfalso ; congruence).
			---- (* sh1eaddr <> freeslotaddr *)
						(* DUP of FirstFreeSlotPointerIsBEAndFreeSlot *)
						destruct (beqAddr blockToShareInCurrPartAddr freeslotaddr) eqn:beqbtfirst ; try(exfalso ; congruence).
							**** (* 2) treat special case where blockToShareInCurrPartAddr = freeslotaddr *)
									(* blockToShare is not a free slot (present) at s10,
											while freeslotaddr is not present as it is a free slot,
											so can't be possible *)
									rewrite <- DependentTypeLemmas.beqAddrTrue in beqbtfirst.
									rewrite <- beqbtfirst in *.
									assert(HwellFormedFstShadowFirsts : wellFormedFstShadowIfBlockEntry s10)
										by (unfold consistency in * ; unfold consistency1 in * ; intuition).
									assert(HwellFormedShadowCutFirsts : wellFormedShadowCutIfBlockEntry s10)
										by (unfold consistency in * ; unfold consistency1 in * ; intuition).
									assert(HisBEEq : isBE blockToShareInCurrPartAddr s = isBE blockToShareInCurrPartAddr s10).
									{
										unfold isBE. rewrite HsEq.
										cbn.
										rewrite beqAddrTrue.
										rewrite beqsh1bts.
										rewrite <- beqAddrFalse in *.
										repeat rewrite removeDupIdentity; intuition.
									}
									assert(HisBEs10 : isBE blockToShareInCurrPartAddr s10)
										by (rewrite <- HisBEEq ; intuition).
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
									unfold isFreeSlot in Hcons10.
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
							**** (* blockToShareInCurrPartAddr <> freeslotaddr *)
									unfold isFreeSlot.
									assert(HlookupfirstEq : lookup freeslotaddr(memory s) beqAddr = lookup freeslotaddr (memory s10) beqAddr ).
									{
					 					rewrite HsEq.
										simpl. rewrite beqAddrTrue.
										rewrite beqfsh1free.
										rewrite <- beqAddrFalse in *.
										repeat rewrite removeDupIdentity; intuition.
									}
									rewrite HlookupfirstEq.

									unfold isFreeSlot in Hcons10.

									destruct (lookup freeslotaddr (memory s10) beqAddr) eqn:Hlookupfirst ; try(exfalso ; congruence).
									destruct v ; try(exfalso ; congruence).

									assert(Hlookupfirstsh1Eq : lookup (CPaddr (freeslotaddr + sh1offset)) (memory s) beqAddr = lookup (CPaddr (freeslotaddr + sh1offset)) (memory s10) beqAddr).
									{
										destruct (beqAddr sh1eaddr (CPaddr (freeslotaddr + sh1offset))) eqn:beqssh1newsh1 ; try(exfalso ; congruence).
										- (* 1) sh1eaddr = (CPaddr (freeslotaddr + sh1offset)) *)
											(* can't discriminate by type, must do by showing blockToShareInCurrPartAddr
													must be equal to (freeslotaddr) -> contradiction since we are not in this case *)
											subst sh1eaddr.
											rewrite <- DependentTypeLemmas.beqAddrTrue in beqssh1newsh1.
											rewrite <- beqssh1newsh1 in *.
											assert(HnullAddrExistss10 : nullAddrExists s10)
													by (unfold consistency in * ; unfold consistency1 in *; intuition).
											unfold nullAddrExists in *. unfold isPADDR in *.
											unfold CPaddr in beqssh1newsh1.
											destruct (le_dec (blockToShareInCurrPartAddr + sh1offset) maxAddr) eqn:Hj.
											-- destruct (le_dec (freeslotaddr + sh1offset) maxAddr) eqn:Hk.
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

									destruct (lookup (CPaddr (freeslotaddr + sh1offset)) (memory s10) beqAddr) eqn:Hlookupsh1first ; try(exfalso ; congruence).
									destruct v ; try(exfalso ; congruence).

									assert(HlookupfirstsceEq : lookup (CPaddr (freeslotaddr + scoffset)) (memory s) beqAddr = lookup (CPaddr (freeslotaddr + scoffset)) (memory s10) beqAddr).
									{
										destruct (beqAddr sh1eaddr (CPaddr (freeslotaddr + scoffset))) eqn:beqssh1newsce ; try(exfalso ; congruence).
										- (* sh1eaddr = (CPaddr (freeslotaddr + scoffset)) *)
											rewrite <- DependentTypeLemmas.beqAddrTrue in beqssh1newsce.
											rewrite <- beqssh1newsce in *.
											unfold isSHE in *.
											destruct (lookup sh1eaddr (memory s10) beqAddr) ; try(exfalso ; congruence).
											destruct v ; try(exfalso ; congruence).
										- (* sh1eaddr <> (CPaddr (freeslotaddr + scoffset)) *)
											rewrite HsEq.
											simpl. rewrite beqAddrTrue.
											rewrite beqssh1newsce.
											rewrite <- beqAddrFalse in *.
											repeat rewrite removeDupIdentity; intuition.
									}
									rewrite HlookupfirstsceEq.

									destruct (lookup (CPaddr (freeslotaddr + scoffset)) (memory s10) beqAddr) eqn:Hlookupscefirst ; try(exfalso ; congruence).
									destruct v ; try(exfalso ; congruence).

									intuition.
	} (* end of freeSlotsListIsFreeSlot *)

	assert(HDisjointFreeSlotsListss : DisjointFreeSlotsLists s).
	{ (* DisjointFreeSlotsLists s *)
		unfold DisjointFreeSlotsLists.
		intros pd1 pd2 HPDTpd1 HPDTpd2 Hpd1pd2NotEq.

		assert(Hcons10 : DisjointFreeSlotsLists s10) by (unfold consistency in * ; unfold consistency1 in * ; intuition).
		unfold DisjointFreeSlotsLists in Hcons10.

	(* we must show all free slots list are disjoint
		check all possible values for pd1 AND pd2 in the modified state s
			-> no entry matches -> pd1's free slots list and pd2's free slot list
						have NOT changed in the modified state, so they are still disjoint
							-> compute the lists at each modified state and check not changed from s10 -> OK
				1) show listoption1 equality between s and s10
				2) show listoption2 equality between s and s10
						-> if they were disjoint at s10, they are still disjoint at s -> OK
	*)
	(* Check all values for pd1 and pd2 *)
	destruct (beqAddr sh1eaddr pd1) eqn:beqsh1pd1; try(exfalso ; congruence).
	*	(* sh1eaddr = pd1 *)
		rewrite <- DependentTypeLemmas.beqAddrTrue in beqsh1pd1.
		rewrite <- beqsh1pd1 in *.
		unfold isPDT in *. unfold isSHE in *.
		destruct (lookup sh1eaddr (memory s) beqAddr) eqn:Hlookupscefirst ; try(exfalso ; congruence).
		destruct v ; try(exfalso ; congruence).
	* (* sh1eaddr <> pd1 *)
			destruct (beqAddr sh1eaddr pd2) eqn:beqsh1pd2; try(exfalso ; congruence).
			**	(* sh1eaddr = pd2 *)
					rewrite <- DependentTypeLemmas.beqAddrTrue in beqsh1pd2.
					rewrite <- beqsh1pd2 in *.
					unfold isPDT in *. unfold isSHE in *.
					destruct (lookup sh1eaddr (memory s) beqAddr) eqn:Hlookupscefirst ; try(exfalso ; congruence).
					destruct v ; try(exfalso ; congruence).
			** (* sh1eaddr <> pd2 *)
					(* show strict equality of listoption1 at s and s10
						and listoption2 at s and s10 because no list changed *)
					(* DUP *)
					(* we must prove optionfreeslotslist1 and optionfreeslotslist2 are strictly
							the same at s than at s10 by recomputing each
							intermediate steps and check at that time *)
					assert(Hlookuppd1Eq : lookup pd1 (memory s) beqAddr = lookup pd1 (memory s10) beqAddr).
					{
						rewrite HsEq.
						cbn.
						rewrite beqAddrTrue.
						rewrite beqsh1pd1.
						rewrite <- beqAddrFalse in *.
						repeat rewrite removeDupIdentity; intuition.
					}
					assert(HPDTpd1Eq : isPDT pd1 s = isPDT pd1 s10).
					{ unfold isPDT. rewrite Hlookuppd1Eq. intuition. }
					assert(HPDTpd1s10 : isPDT pd1 s10) by (rewrite HPDTpd1Eq in * ; assumption).
					assert(Hlookuppd2Eq : lookup pd2 (memory s) beqAddr = lookup pd2 (memory s10) beqAddr).
					{
						rewrite HsEq.
						cbn.
						rewrite beqAddrTrue.
						rewrite beqsh1pd2.
						rewrite <- beqAddrFalse in *.
						repeat rewrite removeDupIdentity; intuition.
					}

					assert(HPDTpd2Eq : isPDT pd2 s = isPDT pd2 s10).
					{ unfold isPDT. rewrite Hlookuppd2Eq. intuition. }
					assert(HPDTpd2s10 : isPDT pd2 s10) by (rewrite HPDTpd2Eq in * ; assumption).
						(* DUP of previous steps to show strict equality of listoption2
							at s and s10 *)
					specialize (Hcons10 pd1 pd2 HPDTpd1s10 HPDTpd2s10 Hpd1pd2NotEq).
					destruct Hcons10 as [listoption1 (listoption2 & (Hoptionlist1s10 & (Hwellformed1s01 & (Hoptionlist2s10 & (Hwellformed2s10 & HDisjoints10)))))].

					(* specialize disjoint for pd1 and pd2 at s10 *)
					assert(HDisjointpd1pd2s10 : DisjointFreeSlotsLists s10)
						by (unfold consistency in * ; unfold consistency1 in * ; intuition).
					unfold DisjointFreeSlotsLists in *.
					specialize (HDisjointpd1pd2s10 pd1 pd2 HPDTpd1s10 HPDTpd2s10 Hpd1pd2NotEq).

					(* 1) compute listoption1 at s and show equality with listoption1 at s10 *)
					unfold getFreeSlotsList in Hoptionlist1s10.
					apply isPDTLookupEq in HPDTpd1s10. destruct HPDTpd1s10 as [pd1entry Hlookuppd1s10].
					rewrite Hlookuppd1s10 in *.
					destruct (beqAddr (firstfreeslot pd1entry) nullAddr) eqn:Hpd1Null ; try(exfalso ; congruence).
					- (* listoption1 = NIL *)
						exists listoption1. exists listoption2.
						assert(Hlistoption1s : getFreeSlotsList pd1 s = nil).
						{
							unfold getFreeSlotsList.
							rewrite Hlookuppd1Eq. rewrite Hpd1Null. reflexivity.
						}
						rewrite Hlistoption1s in *. intuition.
						unfold getFreeSlotsList in *. rewrite Hlookuppd2Eq in *.
						apply isPDTLookupEq in HPDTpd2s10. destruct HPDTpd2s10 as [pd2entry Hlookuppd2s10].
						rewrite Hlookuppd2s10 in *.
						destruct (beqAddr (firstfreeslot pd2entry) nullAddr) eqn:beqfirstnull; try(exfalso ; congruence).
						-- (* (firstfreeslot pd2entry) = nullAddr *)
								intuition.
						-- (* (firstfreeslot pd2entry) <> nullAddr *)
								(* show equality between listoption2 at s and s10
										-> if listoption2 has NOT changed, they are
										still disjoint at s because lisoption1 is NIL *)
								assert(HstatesFreeSlotsList : exists (*s11 s12*) n1 nbleft,
	nbleft = (ADT.nbfreeslots pd2entry) /\
	(*s11 = {|
		   currentPartition := currentPartition s10;
		   memory := add sh1eaddr
                (SHE
                   {|
                     PDchild := globalIdPDChild;
                     PDflag := PDflag sh1entry;
                     inChildLocation := inChildLocation sh1entry
                   |}) (memory s10) beqAddr |} /\*)
	getFreeSlotsListRec n1 (firstfreeslot pd2entry) s11 nbleft =
	getFreeSlotsListRec (maxIdx+1) (firstfreeslot pd2entry) s10 nbleft
				 /\
		n1 <= maxIdx+1 /\ nbleft < n1 /\
	(*\ s12 = {|
		   currentPartition := currentPartition s11;
		   memory := add sh1eaddr
             (SHE
                {|
                  PDchild := PDchild sh1entry0;
                  PDflag := PDflag sh1entry0;
                  inChildLocation := blockToShareChildEntryAddr
                |}) (memory s11) beqAddr |} /\*)
	getFreeSlotsListRec n1 (firstfreeslot pd2entry) s12 nbleft =
				getFreeSlotsListRec n1 (firstfreeslot pd2entry) s11 nbleft
								).
								{	(*eexists ?[s11]. eexists ?[s12].*) eexists ?[n1]. eexists.
									(*split. intuition.*)
									split. intuition.
									(*set (s11 := {| currentPartition := _ |}).*)
									(* prove outside *)
									assert(Hfreeslotss1 : getFreeSlotsListRec ?n1 (firstfreeslot pd2entry) s11 (ADT.nbfreeslots pd2entry) =
										getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s10 (ADT.nbfreeslots pd2entry)).
									{	rewrite Hs11.
										apply getFreeSlotsListRecEqSHE.
										-- 	intro Hfirstpdeq.
												assert(HFirstFreeSlotPointerIsBEAndFreeSlots10 : FirstFreeSlotPointerIsBEAndFreeSlot s10)
													by (unfold consistency in * ; unfold consistency1 in * ; intuition).
												unfold FirstFreeSlotPointerIsBEAndFreeSlot in *.
												specialize (HFirstFreeSlotPointerIsBEAndFreeSlots10 pd2 pd2entry Hlookuppd2s10).
												destruct HFirstFreeSlotPointerIsBEAndFreeSlots10.
												--- intro HfirstfreeNull.
														assert(HnullAddrExistss0 : nullAddrExists s10)
															by (unfold consistency in * ; unfold consistency1 in * ; intuition).
														unfold nullAddrExists in *.
														unfold isPADDR in *.
														rewrite HfirstfreeNull in *. rewrite <- Hfirstpdeq in *.
														unfold isSHE in *.
														destruct (lookup nullAddr (memory s10) beqAddr) ; try(exfalso ; congruence).
														destruct v ; try(exfalso ; congruence).
												--- rewrite Hfirstpdeq in *.
														unfold isBE in *. unfold isSHE in *.
														destruct (lookup sh1eaddr (memory s10) beqAddr) ; try (exfalso ; congruence).
														destruct v ; try(exfalso ; congruence).
										-- 	unfold isBE. unfold isSHE in *.
												destruct (lookup sh1eaddr (memory s10) beqAddr) ; try (exfalso ; congruence).
												destruct v ; try(exfalso ; congruence).
												easy.
										-- 	unfold isPADDR. unfold isSHE in *.
												destruct (lookup sh1eaddr (memory s10) beqAddr) ; try (exfalso ; congruence).
												destruct v ; try(exfalso ; congruence).
												easy.
									}
									(*set (s12 := {| currentPartition := _ |}).*)
									assert(Hfreeslotss2 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s12 (ADT.nbfreeslots pd2entry) =
										getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s11 (ADT.nbfreeslots pd2entry)).
									{
										(* COPY of previous *)
										rewrite Hs12.
										apply getFreeSlotsListRecEqSHE.
										-- 	intro Hfirstpdeq.
												assert(HFirstFreeSlotPointerIsBEAndFreeSlots10 : FirstFreeSlotPointerIsBEAndFreeSlot s10)
													by (unfold consistency in * ; unfold consistency1 in * ; intuition).
												unfold FirstFreeSlotPointerIsBEAndFreeSlot in *.
												specialize (HFirstFreeSlotPointerIsBEAndFreeSlots10 pd2 pd2entry Hlookuppd2s10).
												destruct HFirstFreeSlotPointerIsBEAndFreeSlots10.
												--- intro HfirstfreeNull.
														assert(HnullAddrExistss0 : nullAddrExists s10)
															by (unfold consistency in * ; unfold consistency1 in * ; intuition).
														unfold nullAddrExists in *.
														unfold isPADDR in *.
														rewrite HfirstfreeNull in *. rewrite <- Hfirstpdeq in *.
														unfold isSHE in *.
														destruct (lookup nullAddr (memory s10) beqAddr) ; try(exfalso ; congruence).
														destruct v ; try(exfalso ; congruence).
												--- rewrite Hfirstpdeq in *.
														unfold isBE in *. unfold isSHE in *.
														destruct (lookup sh1eaddr (memory s10) beqAddr) ; try (exfalso ; congruence).
														destruct v ; try(exfalso ; congruence).
										-- 	unfold isBE.
												subst s11. simpl. rewrite beqAddrTrue.
												easy.
										-- 	unfold isPADDR.
												subst s11. simpl. rewrite beqAddrTrue.
												easy.
									}
									(*fold s11. fold s12.*)
									intuition.
									assert(HcurrLtmaxIdx : ADT.nbfreeslots pd2entry <= maxIdx).
									{ intuition. apply IdxLtMaxIdx. }
									lia.
								}
								destruct HstatesFreeSlotsList as [(*s11 (s12 &*)
																	n1' (nbleft' & (Hnbleft & Hnewstates))].
								(*assert(Hs12Eq : s12 = s).
								{ intuition. subst s1. subst s2. subst s3. subst s4. subst s5. subst s6.
									subst s7. subst s8. subst s9. subst s10. subst s11. subst s12.
									rewrite Hs. f_equal.
								}*)
								rewrite <- Hs12Eq in *.
								assert(HfreeslotsEq : getFreeSlotsListRec n1' (firstfreeslot pd2entry) s (ADT.nbfreeslots pd2entry) =
																			getFreeSlotsListRec (maxIdx+1) (firstfreeslot pd2entry) s10 (ADT.nbfreeslots pd2entry)).
								{
									intuition.
									subst nbleft'.
									(* rewrite all previous getFreeSlotsListRec equalities *)
									assert(HFreeSlotsEq1 :     getFreeSlotsListRec n1' (firstfreeslot pd2entry) s (ADT.nbfreeslots pd2entry) =
  												getFreeSlotsListRec n1' (firstfreeslot pd2entry) s11 (ADT.nbfreeslots pd2entry))
										by intuition.
									assert(HfreeSlotsEq2 :    getFreeSlotsListRec n1' (firstfreeslot pd2entry) s11 (ADT.nbfreeslots pd2entry) =
													getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s10
														(ADT.nbfreeslots pd2entry))
										by intuition.
									rewrite HFreeSlotsEq1. rewrite HfreeSlotsEq2.
									reflexivity.
								}
								assert (HfreeslotsEqn1 : getFreeSlotsListRec n1' (firstfreeslot pd2entry) s (ADT.nbfreeslots pd2entry)
																					= getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s (ADT.nbfreeslots pd2entry)).
								{ eapply getFreeSlotsListRecEqN ; intuition.
									subst nbleft'. lia.
									assert (HnbLtmaxIdx : ADT.nbfreeslots pd2entry <= maxIdx) by apply IdxLtMaxIdx.
									lia.
								}
								rewrite <- HfreeslotsEqn1. rewrite HfreeslotsEq. intuition.

					- (* listoption1 <> NIL *)
						(* show equality beween listoption1 at s10 and at s
								-> if equality, then show listoption2 has not changed either
										-> if listoption1 and listoption2 stayed the same
												and they were disjoint at s10, then they
												are still disjoint at s*)
						assert(HstatesFreeSlotsList : exists (*s11 s12*) n1 nbleft,
	nbleft = (ADT.nbfreeslots pd1entry) /\
	(*s11 = {|
		   currentPartition := currentPartition s10;
		   memory := add sh1eaddr
                (SHE
                   {|
                     PDchild := globalIdPDChild;
                     PDflag := PDflag sh1entry;
                     inChildLocation := inChildLocation sh1entry
                   |}) (memory s10) beqAddr |} /\*)
	getFreeSlotsListRec n1 (firstfreeslot pd1entry) s11 nbleft =
	getFreeSlotsListRec (maxIdx+1) (firstfreeslot pd1entry) s10 nbleft
				 /\
		n1 <= maxIdx+1 /\ nbleft < n1 /\
	(*/\ s12 = {|
		   currentPartition := currentPartition s11;
		   memory := add sh1eaddr
             (SHE
                {|
                  PDchild := PDchild sh1entry0;
                  PDflag := PDflag sh1entry0;
                  inChildLocation := blockToShareChildEntryAddr
                |}) (memory s11) beqAddr |} /\*)
	getFreeSlotsListRec n1 (firstfreeslot pd1entry) s12 nbleft =
				getFreeSlotsListRec n1 (firstfreeslot pd1entry) s11 nbleft
						).
						{	(*eexists ?[s11]. eexists ?[s12].*) eexists ?[n1]. eexists.
							(*split. intuition.*)
							split. intuition.
							(*set (s11 := {| currentPartition := _ |}).*)
							(* prove outside *)
							assert(Hfreeslotss1 : getFreeSlotsListRec ?n1 (firstfreeslot pd1entry) s11 (ADT.nbfreeslots pd1entry) =
								getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd1entry) s10 (ADT.nbfreeslots pd1entry)).
							{	rewrite Hs11.
								apply getFreeSlotsListRecEqSHE.
								-- 	intro Hfirstpdeq.
										assert(HFirstFreeSlotPointerIsBEAndFreeSlots10 : FirstFreeSlotPointerIsBEAndFreeSlot s10)
											by (unfold consistency in * ; unfold consistency1 in * ; intuition).
										unfold FirstFreeSlotPointerIsBEAndFreeSlot in *.
										specialize (HFirstFreeSlotPointerIsBEAndFreeSlots10 pd1 pd1entry Hlookuppd1s10).
										destruct HFirstFreeSlotPointerIsBEAndFreeSlots10.
										--- intro HfirstfreeNull.
												assert(HnullAddrExistss0 : nullAddrExists s10)
													by (unfold consistency in * ; unfold consistency1 in * ; intuition).
												unfold nullAddrExists in *.
												unfold isPADDR in *.
												rewrite HfirstfreeNull in *. rewrite <- Hfirstpdeq in *.
												unfold isSHE in *.
												destruct (lookup nullAddr (memory s10) beqAddr) ; try(exfalso ; congruence).
												destruct v ; try(exfalso ; congruence).
										--- rewrite Hfirstpdeq in *.
												unfold isBE in *. unfold isSHE in *.
												destruct (lookup sh1eaddr (memory s10) beqAddr) ; try (exfalso ; congruence).
												destruct v ; try(exfalso ; congruence).
								-- 	unfold isBE. unfold isSHE in *.
										destruct (lookup sh1eaddr (memory s10) beqAddr) ; try (exfalso ; congruence).
										destruct v ; try(exfalso ; congruence).
										easy.
								-- 	unfold isPADDR. unfold isSHE in *.
										destruct (lookup sh1eaddr (memory s10) beqAddr) ; try (exfalso ; congruence).
										destruct v ; try(exfalso ; congruence).
										easy.
							}
							(*set (s12 := {| currentPartition := _ |}).*)
							assert(Hfreeslotss2 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd1entry) s12 (ADT.nbfreeslots pd1entry) =
								getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd1entry) s11 (ADT.nbfreeslots pd1entry)).
							{
								(* COPY of previous *)
								rewrite Hs12.
								apply getFreeSlotsListRecEqSHE.
								-- 	intro Hfirstpdeq.
										assert(HFirstFreeSlotPointerIsBEAndFreeSlots10 : FirstFreeSlotPointerIsBEAndFreeSlot s10)
											by (unfold consistency in * ; unfold consistency1 in * ; intuition).
										unfold FirstFreeSlotPointerIsBEAndFreeSlot in *.
										specialize (HFirstFreeSlotPointerIsBEAndFreeSlots10 pd1 pd1entry Hlookuppd1s10).
										destruct HFirstFreeSlotPointerIsBEAndFreeSlots10.
										--- intro HfirstfreeNull.
												assert(HnullAddrExistss0 : nullAddrExists s10)
													by (unfold consistency in * ; unfold consistency1 in * ; intuition).
												unfold nullAddrExists in *.
												unfold isPADDR in *.
												rewrite HfirstfreeNull in *. rewrite <- Hfirstpdeq in *.
												unfold isSHE in *.
												destruct (lookup nullAddr (memory s10) beqAddr) ; try(exfalso ; congruence).
												destruct v ; try(exfalso ; congruence).
										--- rewrite Hfirstpdeq in *.
												unfold isBE in *. unfold isSHE in *.
												destruct (lookup sh1eaddr (memory s10) beqAddr) ; try (exfalso ; congruence).
												destruct v ; try(exfalso ; congruence).
								-- 	unfold isBE.
										subst s11. simpl. rewrite beqAddrTrue.
										easy.
								-- 	unfold isPADDR.
										subst s11. simpl. rewrite beqAddrTrue.
										easy.
							}
							(*fold s11. fold s12.*)
							intuition.
							assert(HcurrLtmaxIdx : ADT.nbfreeslots pd1entry <= maxIdx).
							{ intuition. apply IdxLtMaxIdx. }
							lia.
						}
						destruct HstatesFreeSlotsList as [(*s11 (s12 &*)
															n1' (nbleft' & (Hnbleft & Hnewstates))].
						(*assert(Hs12Eq : s12 = s).
						{ intuition. subst s1. subst s2. subst s3. subst s4. subst s5. subst s6.
							subst s7. subst s8. subst s9. subst s10. subst s11. subst s12.
							rewrite Hs. f_equal.
						}*)
						rewrite <- Hs12Eq in *.
						assert(HfreeslotsEq : getFreeSlotsListRec n1' (firstfreeslot pd1entry) s (ADT.nbfreeslots pd1entry) =
																	getFreeSlotsListRec (maxIdx+1) (firstfreeslot pd1entry) s10 (ADT.nbfreeslots pd1entry)).
						{
							intuition.
							subst nbleft'.
							(* rewrite all previous getFreeSlotsListRec equalities *)
							assert(HFreeSlotsEq1 :
										getFreeSlotsListRec n1' (firstfreeslot pd1entry) s (ADT.nbfreeslots pd1entry) =
										getFreeSlotsListRec n1' (firstfreeslot pd1entry) s11 (ADT.nbfreeslots pd1entry))
									by intuition.
							assert(HFreeSlotsEq2 :   getFreeSlotsListRec n1' (firstfreeslot pd1entry) s11 (ADT.nbfreeslots pd1entry) =
										getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd1entry) s10
											(ADT.nbfreeslots pd1entry))
									by intuition.
							rewrite HFreeSlotsEq1. rewrite HFreeSlotsEq2.
							reflexivity.
						}
						assert (HfreeslotsEqn1 : getFreeSlotsListRec n1' (firstfreeslot pd1entry) s (ADT.nbfreeslots pd1entry)
																			= getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd1entry) s (ADT.nbfreeslots pd1entry)).
						{ eapply getFreeSlotsListRecEqN ; intuition.
							subst nbleft'. lia.
							assert (HnbLtmaxIdx : ADT.nbfreeslots pd1entry <= maxIdx) by apply IdxLtMaxIdx.
							lia.
						}

						(* 2) compute listoption2 at s and show equality with listoption2 at s10 *)
						apply isPDTLookupEq in HPDTpd2s10. destruct HPDTpd2s10 as [pd2entry Hlookuppd2s10].

						destruct HDisjointpd1pd2s10 as [optionfreeslotslistpd1 (optionfreeslotslistpd2 & (Hoptionfreeslotslistpd1 & (Hwellformedpd1s0 & (Hoptionfreeslotslistpd2 & (Hwellformedpd2s0 & HDisjointpd1pd2s0)))))].
						(* we expect identical lists at s10 and s *)
						exists optionfreeslotslistpd1. exists optionfreeslotslistpd2.
						unfold getFreeSlotsList.
						unfold getFreeSlotsList in Hoptionfreeslotslistpd1.
						unfold getFreeSlotsList in Hoptionfreeslotslistpd2.
						rewrite Hlookuppd1Eq. rewrite Hlookuppd2Eq.
						rewrite Hlookuppd1s10 in *.
						rewrite Hlookuppd2s10 in *.
						destruct (beqAddr (firstfreeslot pd1entry) nullAddr) eqn:HfirstfreeNullpd1 ; try(exfalso ; congruence).
						destruct (beqAddr (firstfreeslot pd2entry) nullAddr) eqn:HfirstfreeNullpd2 ; try(exfalso ; congruence).
						+ (* listoption2 = NIL *)
							(* always disjoint with nil *)
							subst optionfreeslotslistpd1.
							intuition.
							(* we are in the case listoption1 is equal at s and s10 *)
							rewrite <- HfreeslotsEqn1. subst nbleft.
							apply eq_sym. assumption.
						+ (* listoption2 <> NIL *)
							(* show list equality for listoption2 *)
							subst optionfreeslotslistpd1. subst optionfreeslotslistpd2.
							intuition.
							rewrite <- HfreeslotsEqn1. subst nbleft.
							apply eq_sym. assumption.

							(* state already cut into intermediate states *)
							assert(Hfreeslotspd2Eq : exists n1 nbleft,
nbleft = (ADT.nbfreeslots pd2entry) /\
getFreeSlotsListRec n1 (firstfreeslot pd2entry) s11 nbleft =
getFreeSlotsListRec (maxIdx+1) (firstfreeslot pd2entry) s10 nbleft
			 /\
	n1 <= maxIdx+1 /\ nbleft < n1
/\
getFreeSlotsListRec n1 (firstfreeslot pd2entry) s12 nbleft =
			getFreeSlotsListRec n1 (firstfreeslot pd2entry) s11 nbleft
							).
							{
								eexists ?[n1]. eexists.
								split. intuition.
								(* prove outside *)
								assert(Hfreeslotss1 : getFreeSlotsListRec ?n1 (firstfreeslot pd2entry) s11 (ADT.nbfreeslots pd2entry) =
									getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s10 (ADT.nbfreeslots pd2entry)).
								{	subst s11.
									(* COPY *)
									apply getFreeSlotsListRecEqSHE.
									-- 	intro Hfirstpdeq.
											assert(HFirstFreeSlotPointerIsBEAndFreeSlots10 : FirstFreeSlotPointerIsBEAndFreeSlot s10)
												by (unfold consistency in * ; unfold consistency1 in * ; intuition).
											unfold FirstFreeSlotPointerIsBEAndFreeSlot in *.
											specialize (HFirstFreeSlotPointerIsBEAndFreeSlots10 pd2 pd2entry Hlookuppd2s10).
											destruct HFirstFreeSlotPointerIsBEAndFreeSlots10.
											--- intro HfirstfreeNull.
													assert(HnullAddrExistss0 : nullAddrExists s10)
														by (unfold consistency in * ; unfold consistency1 in * ; intuition).
													unfold nullAddrExists in *.
													unfold isPADDR in *.
													rewrite HfirstfreeNull in *. rewrite <- Hfirstpdeq in *.
													unfold isSHE in *.
													destruct (lookup nullAddr (memory s10) beqAddr) ; try(exfalso ; congruence).
													destruct v ; try(exfalso ; congruence).
											--- rewrite Hfirstpdeq in *.
													unfold isBE in *. unfold isSHE in *.
													destruct (lookup sh1eaddr (memory s10) beqAddr) ; try (exfalso ; congruence).
													destruct v ; try(exfalso ; congruence).
									-- 	unfold isBE.
											apply isSHELookupEq in HSHEs10. destruct HSHEs10 as [sh1entry' Hlookupsh1s10].
											rewrite Hlookupsh1s10.
											easy.
									-- 	unfold isPADDR.
											apply isSHELookupEq in HSHEs10. destruct HSHEs10 as [sh1entry' Hlookupsh1s10].
											rewrite Hlookupsh1s10.
											easy.
								}
								assert(Hfreeslotss2 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s12 (ADT.nbfreeslots pd2entry) =
									getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s11 (ADT.nbfreeslots pd2entry)).
								{ subst s12.
									assert(HstatesEqs11 : s =
																					{|
																						currentPartition := currentPartition s11;
																						memory :=
																							add sh1eaddr
																								(SHE
																									 {|
																										 PDchild := PDchild sh1entry0;
																										 PDflag := PDflag sh1entry0;
																										 inChildLocation := blockToShareChildEntryAddr
																									 |}) (memory s11) beqAddr |}) by intuition.
									rewrite HstatesEqs11. (* s = currentPartition s11 ...*)
									assert(HSHEs11 : isSHE sh1eaddr s11).
									{ unfold isSHE. subst s11. cbn. rewrite beqAddrTrue. trivial. }
									(* DUP *)
									apply getFreeSlotsListRecEqSHE.
									-- 	intro Hfirstpdeq.
											assert(HFirstFreeSlotPointerIsBEAndFreeSlots10 : FirstFreeSlotPointerIsBEAndFreeSlot s10)
												by (unfold consistency in * ; unfold consistency1 in * ; intuition).
											unfold FirstFreeSlotPointerIsBEAndFreeSlot in *.
											specialize (HFirstFreeSlotPointerIsBEAndFreeSlots10 pd2 pd2entry Hlookuppd2s10).
											destruct HFirstFreeSlotPointerIsBEAndFreeSlots10.
											--- intro HfirstfreeNull.
													assert(HnullAddrExistss0 : nullAddrExists s10)
														by (unfold consistency in * ; unfold consistency1 in * ; intuition).
													unfold nullAddrExists in *.
													unfold isPADDR in *.
													rewrite HfirstfreeNull in *. rewrite <- Hfirstpdeq in *.
													unfold isSHE in *.
													destruct (lookup nullAddr (memory s10) beqAddr) ; try(exfalso ; congruence).
													destruct v ; try(exfalso ; congruence).
											--- rewrite Hfirstpdeq in *.
													unfold isBE in *. unfold isSHE in *.
													destruct (lookup sh1eaddr (memory s10) beqAddr) ; try (exfalso ; congruence).
													destruct v ; try(exfalso ; congruence).
									-- 	unfold isBE.
											apply isSHELookupEq in HSHEs11. destruct HSHEs11 as [sh1entry' Hlookupsh1s11].
											rewrite Hlookupsh1s11.
											easy.
									-- 	unfold isPADDR.
											apply isSHELookupEq in HSHEs11. destruct HSHEs11 as [sh1entry' Hlookupsh1s11].
											rewrite Hlookupsh1s11.
											easy.
								}
								intuition.
								assert(HcurrLtmaxIdx : ADT.nbfreeslots pd2entry <= maxIdx).
								{ intuition. apply IdxLtMaxIdx. }
								intuition.
								assert(Hmax : maxIdx + 1 = S maxIdx) by (apply MaxIdxNextEq).
								rewrite Hmax. apply Lt.le_lt_n_Sm. intuition.
							}
							destruct Hfreeslotspd2Eq as [n1'' (nbleft'' & Hstates)].
							rewrite <- Hs12Eq in *.
							assert(HfreeslotsEqpd2 : getFreeSlotsListRec n1'' (firstfreeslot pd2entry) s (ADT.nbfreeslots pd2entry) =
																		getFreeSlotsListRec (maxIdx+1) (firstfreeslot pd2entry) s10 (ADT.nbfreeslots pd2entry)).
							{
								intuition.
								subst nbleft''.
								(* rewrite all previous getFreeSlotsListRec equalities *)
								assert(HFreeSlotsEq1 :   getFreeSlotsListRec n1'' (firstfreeslot pd2entry) s (ADT.nbfreeslots pd2entry) =
 												 getFreeSlotsListRec n1'' (firstfreeslot pd2entry) s11 (ADT.nbfreeslots pd2entry))
										by intuition.
								assert(HFreeSlotsEq2 :   getFreeSlotsListRec n1'' (firstfreeslot pd2entry) s11 (ADT.nbfreeslots pd2entry) =
												getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s10
													(ADT.nbfreeslots pd2entry))
										by intuition.
								rewrite HFreeSlotsEq1. rewrite HFreeSlotsEq2.
								reflexivity.
							}
							assert (HfreeslotsEqn1' : getFreeSlotsListRec n1'' (firstfreeslot pd2entry) s (ADT.nbfreeslots pd2entry)
																				= getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s (ADT.nbfreeslots pd2entry)).
							{ eapply getFreeSlotsListRecEqN ; intuition.
								subst nbleft''. lia.
								assert (HnbLtmaxIdx : ADT.nbfreeslots pd2entry <= maxIdx) by apply IdxLtMaxIdx.
								lia.
							}
							rewrite <- HfreeslotsEqn1'. rewrite HfreeslotsEqpd2. intuition.
	} (* end of DisjointFreeSlotsLists *)

	assert(HinclFreeSlotsBlockEntriess : inclFreeSlotsBlockEntries s).
	{ (* inclFreeSlotsBlockEntries s *)
		unfold inclFreeSlotsBlockEntries.
		intros pd HPDT.

		assert(Hcons10 : inclFreeSlotsBlockEntries s10) by (unfold consistency in * ; unfold consistency1 in * ; intuition).
		unfold inclFreeSlotsBlockEntries in Hcons10.

	(* we must show the free slots list is included in the ks entries list of the same pd
		check all possible values for pd in the modified state s
			-> no match
				-> prove pd's free slots list and ksentries list have NOT changed
								in the modified state, so the free slots list is still included
									-> compute the lists at each modified state and check not changed from s0 -> OK
	*)
		(* Check all values for pd  *)
		destruct (beqAddr sh1eaddr pd) eqn:beqsh1pd; try(exfalso ; congruence).
		*	(* sh1eaddr = pd *)
			rewrite <- DependentTypeLemmas.beqAddrTrue in beqsh1pd.
			rewrite <- beqsh1pd in *.
			unfold isPDT in *. unfold isSHE in *.
			destruct (lookup sh1eaddr (memory s) beqAddr) eqn:Hlookupscefirst ; try(exfalso ; congruence).
			destruct v ; try(exfalso ; congruence).
		* (* sh1eaddr <> pd *)
			assert(HlookuppdEq : lookup pd (memory s) beqAddr = lookup pd (memory s10) beqAddr).
			{
				rewrite HsEq.
				cbn.
				rewrite beqAddrTrue.
				rewrite beqsh1pd.
				rewrite <- beqAddrFalse in *.
				repeat rewrite removeDupIdentity; intuition.
			}
			apply isPDTLookupEq in HPDT. destruct HPDT as [pdentrys' Hlookuppds].
			assert(HPDTpds10 : isPDT pd s10)
				by (unfold isPDT ; rewrite <- HlookuppdEq ; rewrite Hlookuppds ; intuition).
			specialize (Hcons10 pd HPDTpds10).

			(* develop getFreeSlotsList *)
			unfold getFreeSlotsList. unfold getFreeSlotsList in Hcons10.
			rewrite HlookuppdEq in *.
			apply isPDTLookupEq in HPDTpds10. destruct HPDTpds10 as [pdentrys10 Hlookuppds10].
			rewrite Hlookuppds10 in *.
			destruct (beqAddr (firstfreeslot pdentrys10) nullAddr) eqn:newFNull.
			---- (* getFreeSlots = nil *)
						apply incl_nil_l.
			---- (* getFreeSlots <> nil *)
						(* show equality between Hoptionlists at s10 and at s
								-> if equality then show ksentries didn't change either
										-> if Hoptionlists was included in ksentries at s10,
												then they still included at s*)
						assert(HstatesFreeSlotsList : exists (*s11 s12*) n1 nbleft,
	nbleft = (ADT.nbfreeslots pdentrys10) /\
	(*s11 = {|
		   currentPartition := currentPartition s10;
		   memory := add sh1eaddr
                (SHE
                   {|
                     PDchild := globalIdPDChild;
                     PDflag := PDflag sh1entry;
                     inChildLocation := inChildLocation sh1entry
                   |}) (memory s10) beqAddr |} /\*)
	getFreeSlotsListRec n1 (firstfreeslot pdentrys10) s11 nbleft =
	getFreeSlotsListRec (maxIdx+1) (firstfreeslot pdentrys10) s10 nbleft
				 /\
		n1 <= maxIdx+1 /\ nbleft < n1 /\
	(*/\ s12 = {|
		   currentPartition := currentPartition s11;
		   memory := add sh1eaddr
             (SHE
                {|
                  PDchild := PDchild sh1entry0;
                  PDflag := PDflag sh1entry0;
                  inChildLocation := blockToShareChildEntryAddr
                |}) (memory s11) beqAddr |} /\*)
	getFreeSlotsListRec n1 (firstfreeslot pdentrys10) s12 nbleft =
				getFreeSlotsListRec n1 (firstfreeslot pdentrys10) s11 nbleft
						).
						{	(*eexists ?[s11]. eexists ?[s12].*) eexists ?[n1]. eexists.
							(*split. intuition.*)
							split. intuition.
							(*set (s11 := {| currentPartition := _ |}).*)
							(* prove outside *)
							assert(Hfreeslotss1 : getFreeSlotsListRec ?n1 (firstfreeslot pdentrys10) s11 (ADT.nbfreeslots pdentrys10) =
								getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pdentrys10) s10 (ADT.nbfreeslots pdentrys10)).
							{	rewrite Hs11.
								apply getFreeSlotsListRecEqSHE.
								-- 	intro Hfirstpdeq.
										assert(HFirstFreeSlotPointerIsBEAndFreeSlots10 : FirstFreeSlotPointerIsBEAndFreeSlot s10)
											by (unfold consistency in * ; unfold consistency1 in * ; intuition).
										unfold FirstFreeSlotPointerIsBEAndFreeSlot in *.
										specialize (HFirstFreeSlotPointerIsBEAndFreeSlots10 pd pdentrys10 Hlookuppds10).
										destruct HFirstFreeSlotPointerIsBEAndFreeSlots10.
										--- intro HfirstfreeNull.
												assert(HnullAddrExistss0 : nullAddrExists s10)
													by (unfold consistency in * ; unfold consistency1 in * ; intuition).
												unfold nullAddrExists in *.
												unfold isPADDR in *.
												rewrite HfirstfreeNull in *. rewrite <- Hfirstpdeq in *.
												unfold isSHE in *.
												destruct (lookup nullAddr (memory s10) beqAddr) ; try(exfalso ; congruence).
												destruct v ; try(exfalso ; congruence).
										--- rewrite Hfirstpdeq in *.
												unfold isBE in *. unfold isSHE in *.
												destruct (lookup sh1eaddr (memory s10) beqAddr) ; try (exfalso ; congruence).
												destruct v ; try(exfalso ; congruence).
								-- 	unfold isBE. unfold isSHE in *.
										destruct (lookup sh1eaddr (memory s10) beqAddr) ; try (exfalso ; congruence).
										destruct v ; try(exfalso ; congruence).
										easy.
								-- 	unfold isPADDR. unfold isSHE in *.
										destruct (lookup sh1eaddr (memory s10) beqAddr) ; try (exfalso ; congruence).
										destruct v ; try(exfalso ; congruence).
										easy.
							}
							(*set (s12 := {| currentPartition := _ |}).*)
							assert(Hfreeslotss2 : getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pdentrys10) s12 (ADT.nbfreeslots pdentrys10) =
								getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pdentrys10) s11 (ADT.nbfreeslots pdentrys10)).
							{
								(* COPY of previous *)
								rewrite Hs12.
								apply getFreeSlotsListRecEqSHE.
								-- 	intro Hfirstpdeq.
										assert(HFirstFreeSlotPointerIsBEAndFreeSlots10 : FirstFreeSlotPointerIsBEAndFreeSlot s10)
											by (unfold consistency in * ; unfold consistency1 in * ; intuition).
										unfold FirstFreeSlotPointerIsBEAndFreeSlot in *.
										specialize (HFirstFreeSlotPointerIsBEAndFreeSlots10 pd pdentrys10 Hlookuppds10).
										destruct HFirstFreeSlotPointerIsBEAndFreeSlots10.
										--- intro HfirstfreeNull.
												assert(HnullAddrExistss0 : nullAddrExists s10)
													by (unfold consistency in * ; unfold consistency1 in * ; intuition).
												unfold nullAddrExists in *.
												unfold isPADDR in *.
												rewrite HfirstfreeNull in *. rewrite <- Hfirstpdeq in *.
												unfold isSHE in *.
												destruct (lookup nullAddr (memory s10) beqAddr) ; try(exfalso ; congruence).
												destruct v ; try(exfalso ; congruence).
										--- rewrite Hfirstpdeq in *.
												unfold isBE in *. unfold isSHE in *.
												destruct (lookup sh1eaddr (memory s10) beqAddr) ; try (exfalso ; congruence).
												destruct v ; try(exfalso ; congruence).
								-- 	unfold isBE.
										subst s11. simpl. rewrite beqAddrTrue.
										easy.
								-- 	unfold isPADDR.
										subst s11. simpl. rewrite beqAddrTrue.
										easy.
							}
							(*fold s11. fold s12.*)
							intuition.
							assert(HcurrLtmaxIdx : ADT.nbfreeslots pdentrys10 <= maxIdx).
							{ intuition. apply IdxLtMaxIdx. }
							lia.
						}
						destruct HstatesFreeSlotsList as [(*s11 (s12 &*)
															n1' (nbleft' & (Hnbleft & Hnewstates))].
						(*assert(Hs12Eq : s12 = s).
						{ intuition. subst s1. subst s2. subst s3. subst s4. subst s5. subst s6.
							subst s7. subst s8. subst s9. subst s10. subst s11. subst s12.
							rewrite Hs. f_equal.
						}*)
						rewrite <- Hs12Eq in *.
						assert(HfreeslotsEq : getFreeSlotsListRec n1' (firstfreeslot pdentrys10) s (ADT.nbfreeslots pdentrys10) =
																	getFreeSlotsListRec (maxIdx+1) (firstfreeslot pdentrys10) s10 (ADT.nbfreeslots pdentrys10)).
						{
							intuition.
							subst nbleft'.
							(* rewrite all previous getFreeSlotsListRec equalities *)
							assert(HFreeSlotsEq1 :   getFreeSlotsListRec n1' (firstfreeslot pdentrys10) s (ADT.nbfreeslots pdentrys10) =
 												 getFreeSlotsListRec n1' (firstfreeslot pdentrys10) s11 (ADT.nbfreeslots pdentrys10))
								by intuition.
							assert(HFreeSlotsEq2 :   getFreeSlotsListRec n1' (firstfreeslot pdentrys10) s11 (ADT.nbfreeslots pdentrys10) =
												getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pdentrys10) s10
													(ADT.nbfreeslots pdentrys10))
									by intuition.
							rewrite HFreeSlotsEq1. rewrite HFreeSlotsEq2.
							reflexivity.
						}

						assert (HfreeslotsEqn1 : getFreeSlotsListRec n1' (firstfreeslot pdentrys10) s (ADT.nbfreeslots pdentrys10)
																			= getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pdentrys10) s (ADT.nbfreeslots pdentrys10)).
						{ eapply getFreeSlotsListRecEqN ; intuition.
							subst nbleft'. lia.
							assert (HnbLtmaxIdx : ADT.nbfreeslots pdentrys10 <= maxIdx) by apply IdxLtMaxIdx.
							lia.
						}
						rewrite <- HfreeslotsEqn1. rewrite HfreeslotsEq.

						(* develop getKSEntries and show equality with list at s10 *)
						assert(HKSEntriesEq :   (getKSEntries pd s) =   (getKSEntries pd s10)).
						{
							assert(HksentriespdEqs11s10 : 	getKSEntries pd s11 = getKSEntries pd s10).
							{ intuition. subst s11.
								eapply getKSEntriesEqSHE ; intuition.
								-- rewrite Hlookuppds10. trivial.
							}
							assert(HksentriespdEqs12s11 : 	getKSEntries pd s12 = getKSEntries pd s11).
							{ intuition. subst s12.
								assert(HstatesEqs11 : s =
																					{|
																						currentPartition := currentPartition s11;
																						memory :=
																							add sh1eaddr
																								(SHE
																									 {|
																										 PDchild := PDchild sh1entry0;
																										 PDflag := PDflag sh1entry0;
																										 inChildLocation := blockToShareChildEntryAddr
																									 |}) (memory s11) beqAddr |}) by intuition.
									rewrite HstatesEqs11. (* s = currentPartition s11 ...*)
								eapply getKSEntriesEqSHE ; intuition.
								-- subst s11. cbn. rewrite beqsh1pd. cbn.
										rewrite <- beqAddrFalse in *.
										repeat rewrite removeDupIdentity ; intuition.
										rewrite Hlookuppds10. trivial.
								-- unfold isSHE. subst s11. cbn. rewrite beqAddrTrue. trivial.
							}
							subst s12. rewrite HksentriespdEqs12s11. rewrite HksentriespdEqs11s10.
							reflexivity.
						}
						rewrite HKSEntriesEq. intuition.
	} (* end of inclFreeSlotsBlockEntries *)

	assert(HDisjointKSEntriess : DisjointKSEntries s).
	{ (* DisjointKSEntries s *)
		unfold DisjointKSEntries.
		intros pd1 pd2 HPDTpd1 HPDTpd2 Hpd1pd2NotEq.

		assert(Hcons10 : DisjointKSEntries s10) by (unfold consistency in * ; unfold consistency1 in * ; intuition).
		unfold DisjointKSEntries in Hcons10.

		(* we must show all KSEntries lists are disjoint
			check all possible values for pd1 AND pd2 in the modified state s
				-> no match
					-> prove pd1's free slots list and pd2's free slot list
									have NOT changed in the modified state, so they are still disjoint
										-> compute the list at each modified state and check not changed from s0 -> OK
	*)
		(* Check all values for pd1 and pd2 *)
		destruct (beqAddr sh1eaddr pd1) eqn:beqsh1pd1; try(exfalso ; congruence).
		*	(* sh1eaddr = pd1 *)
			rewrite <- DependentTypeLemmas.beqAddrTrue in beqsh1pd1.
			rewrite <- beqsh1pd1 in *.
			unfold isPDT in *. unfold isSHE in *.
			destruct (lookup sh1eaddr (memory s) beqAddr) eqn:Hlookupscefirst ; try(exfalso ; congruence).
			destruct v ; try(exfalso ; congruence).
		* (* sh1eaddr <> pd1 *)
			destruct (beqAddr sh1eaddr pd2) eqn:beqsh1pd2; try(exfalso ; congruence).
			**	(* sh1eaddr = pd2 *)
				rewrite <- DependentTypeLemmas.beqAddrTrue in beqsh1pd2.
				rewrite <- beqsh1pd2 in *.
				unfold isPDT in *. unfold isSHE in *.
				destruct (lookup sh1eaddr (memory s) beqAddr) eqn:Hlookupscefirst ; try(exfalso ; congruence).
				destruct v ; try(exfalso ; congruence).
			** (* sh1eaddr <> pd2 *)
					(* DUP *)
					assert(Hlookuppd2Eq : lookup pd2 (memory s) beqAddr = lookup pd2 (memory s10) beqAddr).
					{
						rewrite HsEq. unfold isPDT.
						cbn. rewrite beqAddrTrue.
						rewrite beqsh1pd2.
						rewrite <- beqAddrFalse in *.
						repeat rewrite removeDupIdentity ; intuition.
					}
					assert(HPDTpd2Eq : isPDT pd2 s = isPDT pd2 s10).
					{ unfold isPDT. rewrite Hlookuppd2Eq. intuition. }
					assert(HPDTpd2s10 : isPDT pd2 s10) by (rewrite HPDTpd2Eq in * ; assumption).

						assert(Hlookuppd1Eq : lookup pd1 (memory s) beqAddr = lookup pd1 (memory s10) beqAddr).
						{
																			rewrite HsEq. unfold isPDT.
						cbn. rewrite beqAddrTrue.
						rewrite beqsh1pd1.
						rewrite <- beqAddrFalse in *.
						repeat rewrite removeDupIdentity ; intuition.
						}
					assert(HPDTpd1Eq : isPDT pd1 s = isPDT pd1 s10).
					{ unfold isPDT. rewrite Hlookuppd1Eq. intuition. }
					assert(HPDTpd1s10 : isPDT pd1 s10) by (rewrite HPDTpd1Eq in * ; assumption).

					(* specialize disjoint for pd1 and pd2 at s0 *)
					specialize (Hcons10 pd1 pd2 HPDTpd1s10 HPDTpd2s10 Hpd1pd2NotEq).
					apply isPDTLookupEq in HPDTpd1s10. destruct HPDTpd1s10 as [pd1entry Hlookuppd1s10].
					apply isPDTLookupEq in HPDTpd2s10. destruct HPDTpd2s10 as [pd2entry Hlookuppd2s10].

					destruct Hcons10 as [optionfreeslotslistpd1 (optionfreeslotslistpd2 & (Hoptionfreeslotslistpd1 & (Hoptionfreeslotslistpd2 & Hcons10)))].
					(* we expect identical lists at s0 and s *)
					exists optionfreeslotslistpd1. exists optionfreeslotslistpd2.

					(*assert(HstatesFreeSlotsList : exists s11 s12,
	s11 = {|
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
                {|
                  PDchild := PDchild sh1entry0;
                  PDflag := PDflag sh1entry0;
                  inChildLocation := blockToShareChildEntryAddr
                |}) (memory s11) beqAddr |}
						).
					{	eexists ?[s11]. eexists ?[s12]. intuition. }
						destruct HstatesFreeSlotsList as [s11 (s12 & (Hs11 & Hs12))].*)

						assert(HKSEntriespd1Eq :  (getKSEntries pd1 s) =   (getKSEntries pd1 s10)).
						{
							assert(Hksentriespd1Eqs11s10 : 	getKSEntries pd1 s11 = getKSEntries pd1 s10).
							{ intuition. subst s11.
								eapply getKSEntriesEqSHE ; intuition.
								-- rewrite Hlookuppd1s10. trivial.
							}
							assert(Hksentriespd1Eqs12s11 : 	getKSEntries pd1 s12 = getKSEntries pd1 s11).
							{ intuition. subst s12. rewrite Hs11. (* s = {| currentPartition := currentPartition s11; ...*)
								eapply getKSEntriesEqSHE ; intuition.
								-- subst s11. cbn. rewrite beqsh1pd1. cbn.
										rewrite <- beqAddrFalse in *.
										repeat rewrite removeDupIdentity ; intuition.
										rewrite Hlookuppd1s10. trivial.
								-- unfold isSHE. subst s11. cbn. rewrite beqAddrTrue. trivial.
							}
							(*assert(Hs12Eq : s = s12).
							{ subst s12. rewrite HsEq. subst s11. intuition. }*)
								rewrite Hs12Eq. rewrite Hksentriespd1Eqs12s11.
								rewrite Hksentriespd1Eqs11s10.
								reflexivity.
						}
						assert(HKSEntriespd2Eq :  (getKSEntries pd2 s) =   (getKSEntries pd2 s10)).
						{
							assert(Hksentriespd2Eqs11s10 : 	getKSEntries pd2 s11 = getKSEntries pd2 s10).
							{ intuition. subst s11.
								eapply getKSEntriesEqSHE ; intuition.
								-- rewrite Hlookuppd2s10. trivial.
							}
							assert(Hksentriespd2Eqs12s11 : 	getKSEntries pd2 s12 = getKSEntries pd2 s11).
							{ intuition. subst s12. rewrite Hs11. (* s = {| currentPartition := currentPartition s11; ...*)
								eapply getKSEntriesEqSHE ; intuition.
								-- subst s11. cbn. rewrite beqsh1pd2. cbn.
										rewrite <- beqAddrFalse in *.
										repeat rewrite removeDupIdentity ; intuition.
										rewrite Hlookuppd2s10. trivial.
								-- unfold isSHE. subst s11. cbn. rewrite beqAddrTrue. trivial.
							}
							(* assert(Hs12Eq : s = s12).
							{ subst s12. rewrite HsEq. subst s11. intuition. }*)
								rewrite Hs12Eq. rewrite Hksentriespd2Eqs12s11.
								rewrite Hksentriespd2Eqs11s10.
								reflexivity.
						}
						rewrite HKSEntriespd2Eq in *.
						rewrite HKSEntriespd1Eq in *.
						intuition.
	} (* end of DisjointKSEntries *)

assert (HblockInParent : In blockToShareInCurrPartAddr (getMappedBlocks currentPart s0))
	by admit. (* from block found*)

	assert(HnoDupUsedPaddrLists : noDupUsedPaddrList s).
	{ (* noDupUsedPaddrList s *)
		(* equality of lists getPartitions and getChildren for already proven any partition
				except globalidPDchild whose NoDup property is indirectly proven
					knowing the equivalent new mapped list and its lentgh compared to the old one *)
		assert(Hcons0 : noDupUsedPaddrList s0)
			by (unfold consistency in * ; unfold consistency2 in * ; intuition).
		unfold noDupUsedPaddrList.
		intros part HPDTpds.
		unfold getUsedPaddr.

		assert(HPDTEq : isPDT part s = isPDT part s0).
		{
			unfold isPDT in *. simpl.
			rewrite Hs. simpl. repeat rewrite beqAddrTrue.
			destruct (beqAddr sh1eaddr part) eqn:beqsh1part ; try(exfalso ; congruence).
			- (* sh1eaddr = part *)
				rewrite <- DependentTypeLemmas.beqAddrTrue in beqsh1part.
				rewrite beqsh1part in *.
				unfold isSHE in *.
				destruct (lookup part (memory s) beqAddr) ; try(exfalso ; congruence).
				destruct v ; try(exfalso ; congruence).
			- (* sh1eaddr = part *)
				rewrite beqscesh1.
				simpl.
				destruct (beqAddr sceaddr part) eqn:beqscepart ; try(exfalso ; congruence).
				-- (* sceaddr = part *)
						rewrite <- DependentTypeLemmas.beqAddrTrue in beqscepart.
						rewrite beqscepart in *.
						unfold isSCE in *.
						destruct (lookup part (memory s) beqAddr) ; try(exfalso ; congruence).
						destruct v ; try(exfalso ; congruence).
				-- (* sceaddr = part *)
						rewrite beqscesh1.
						simpl.
						rewrite beqscepart.
						rewrite beqnewBsce.
						simpl.
						rewrite beqnewBsh1.
						simpl.
						rewrite beqnewBsh1.
						simpl.
						destruct (beqAddr newBlockEntryAddr part) eqn:beqnewBpart ; try(exfalso ; congruence).
						--- (* newBlockEntryAddr = part *)
								rewrite <- DependentTypeLemmas.beqAddrTrue in beqnewBpart.
								rewrite beqnewBpart in *.
								rewrite HlookupnewBs in *.
								exfalso ; congruence.
						--- (* newBlockEntryAddr = part *)
								destruct (beqAddr globalIdPDChild newBlockEntryAddr) eqn:Hf ; try(exfalso ; congruence).
								simpl.
								rewrite Hf.
								rewrite <- beqAddrFalse in *.
								repeat rewrite removeDupIdentity ; intuition.
								simpl.
								destruct (beqAddr globalIdPDChild part) eqn:beqidpdpart ; try(exfalso ; congruence).
								---- (* globalIdPDChild = part *)
										rewrite <- DependentTypeLemmas.beqAddrTrue in beqidpdpart.
										rewrite beqidpdpart in *.
										rewrite Hpdinsertions0 in *.
										trivial.
								---- (* globalIdPDChild <> part *)
										rewrite <- beqAddrFalse in *.
										repeat rewrite removeDupIdentity ; intuition.
		}

		assert(HconfigPadrEq : getConfigPaddr part s = getConfigPaddr part s0).
		{
			destruct (beqAddr globalIdPDChild part) eqn:beqidpdpart ; try(exfalso ; congruence).
			- (* globalIdPDChild =  part *)
				rewrite <- DependentTypeLemmas.beqAddrTrue in beqidpdpart.
				rewrite <- beqidpdpart in *.
				intuition.
			- (* globalIdPDChild <> part *)
				rewrite <- beqAddrFalse in *.
				intuition.
				assert(HconfigEq : forall partition : paddr,
									(partition = globalIdPDChild -> False) ->
									isPDT partition s0 ->
									getConfigPaddr partition s = getConfigPaddr partition s0)
						by intuition.
				rewrite HPDTEq in *.
				eapply HconfigEq ; intuition.
		}

		assert(HcurrentPartitionInPartitionsLists0 : currentPartitionInPartitionsList s0)
			by (unfold consistency in * ; unfold consistency1 in * ; intuition).
		unfold currentPartitionInPartitionsList in *.
		assert(HcurrEq : currentPart = currentPartition s0) by intuition.
		rewrite <- HcurrEq in *.

		apply Lib.NoDupSplitInclIff.

		unfold noDupUsedPaddrList in *.
		rewrite HPDTEq in *.
		specialize (Hcons0 part HPDTpds).
		unfold getUsedPaddr in *.
		rewrite Lib.NoDupSplitInclIff in Hcons0.
		assert(Hcons0' : noDupUsedPaddrList s0)
			by (unfold consistency in * ; unfold consistency2 in * ; intuition).
		assert(HPDTcurrParts0 : isPDT currentPart s0) by intuition.
		specialize (Hcons0' currentPart HPDTcurrParts0).
		unfold getUsedPaddr in *.
		rewrite Lib.NoDupSplitInclIff in Hcons0'.
		split. split.
		- (* getConfigPaddr *)
			rewrite HconfigPadrEq in *. intuition.
		- (* getMappedPaddr *)
			-- destruct (beqAddr globalIdPDChild part) eqn:beqidpdpart ; try(exfalso ; congruence).
			--- (* pdinsertion =  part *)
					rewrite <- DependentTypeLemmas.beqAddrTrue in beqidpdpart.
					rewrite <- beqidpdpart in *.
					assert(HsharedBlockPointsToChilds0 : sharedBlockPointsToChild s0)
						by (unfold consistency in * ; unfold consistency2 in * ; intuition).
					unfold sharedBlockPointsToChild in *.
					specialize (HsharedBlockPointsToChilds0 currentPart globalIdPDChild).

					assert(HVs0 : verticalSharing s0) by intuition.
					unfold verticalSharing in HVs0.
					specialize (HVs0 currentPart globalIdPDChild
								HcurrentPartitionInPartitionsLists0 HidpdIsChild).
					unfold getUsedPaddr in HVs0.
					assert(Hincl : incl (getMappedPaddr globalIdPDChild s0)
         							(getMappedPaddr currentPart s0)).
					{
						intros addr HaddrInMappedidpd.
						specialize (HVs0 addr).
						eapply HVs0 ; intuition.
					}

					(* - newBlockEntryAddr and its contained addresses were not not in the child
								at s0 otherwise the parent block would have been shared already
									which is not the case *)
					assert(HBlockNotIn : Lib.disjoint (getAllPaddrBlock (startAddr (blockrange bentry6))
           (endAddr (blockrange bentry6)))
															(getMappedPaddr globalIdPDChild s0)).
					{
						intros addr HaddrInBlock.
						intro HaddrInMappedChilds0.
						specialize (HsharedBlockPointsToChilds0 
																					addr
																					blockToShareInCurrPartAddr
																					sh1eaddr
																					HcurrentPartitionInPartitionsLists0
																					HidpdIsChild).
						assert(HaddrInUsed: In addr (getUsedPaddr globalIdPDChild s0)).
						{
							unfold getUsedPaddr.
							apply in_or_app. intuition.
						}

						assert(HaddrInParentBlock : In addr (getAllPaddrAux [blockToShareInCurrPartAddr] s0)).
						{	simpl.
							specialize (HaddrInBTSIfInnewB addr) ; intuition.
						}

						assert(Hsh1entry : sh1entryAddr blockToShareInCurrPartAddr sh1eaddr s0).
						{
							intuition.
							assert(Hsh1s0 : exists (sh1entry : Sh1Entry) (sh1entryaddr : paddr),
														lookup sh1entryaddr (memory s0) beqAddr = Some (SHE sh1entry) /\
														sh1entryPDchild sh1entryaddr PDChildAddr s0 /\
														sh1entryAddr blockToShareInCurrPartAddr sh1entryaddr s0)
								by intuition.
							destruct Hsh1s0 as [Hsh1 (Hsh1addr & Hsh1s0)].
							intuition.
							unfold sh1entryAddr in *.
							apply isBELookupEq in HBEbtss0. destruct HBEbtss0 as [Hbentrybts Hlookupbtss0].
							rewrite Hlookupbtss0 in *.
							intuition.
						}

							specialize (HsharedBlockPointsToChilds0 HaddrInUsed
																											HaddrInParentBlock
																											HblockInParent
																											Hsh1entry).
							(* Contradict *)
							rewrite <- HSh1Offset in *.
							unfold isSHE in *.
							unfold sh1entryPDchild in *. unfold sh1entryPDflag in *.
							destruct (lookup sh1eaddr (memory s0)) eqn:Hlookupsh1s0 ; try(exfalso ; congruence).
							destruct v ; try(exfalso ; congruence).
							destruct HsharedBlockPointsToChilds0 as [Hsh1entrypdchilds0 | sh1entrypdflags0].
							(*destruct HsharedInChilds0 as [Hsh1entryaddrs0 | Hsh1entrychilds0].*)
							+ (* case pdchild = child1 *)
									rewrite <- Hsh1PDchildbtsNulls0 in *.
									subst globalIdPDChild. rewrite Hsh1entrypdchilds0 in *.
									assert(HnullAddrExists0 : nullAddrExists s0)
										by (unfold consistency in * ; unfold consistency1 in * ; intuition).
									unfold nullAddrExists in *. unfold isPADDR in *.
									unfold isPDT in *.
									destruct (lookup nullAddr (memory s0) beqAddr) ; try(exfalso ; congruence).
									destruct v ; try(exfalso ; congruence).
								+ (* case pdflag is set *)
									rewrite <- sh1entrypdflags0 in *. congruence.
					}

					(* NoDup of old mapped list extended with block because there was NoDup
								in the child at s0 and they are disjoint *)
					assert(HNoDups0' : NoDup((getAllPaddrBlock (startAddr (blockrange bentry6))
		       (endAddr (blockrange bentry6))) ++
															(getMappedPaddr globalIdPDChild s0))).
					{
						rewrite Lib.NoDupSplitInclIff ; intuition.
						eapply NoDupPaddrBlockAux ; intuition.
					}

					(* NoDup in new mapped list because equivalent to old one extended with
							newBlockEntryAddr and NoDup in the latter and length are equal *)
					eapply NoDup_incl_NoDup with (getAllPaddrBlock (startAddr (blockrange bentry6))
                 (endAddr (blockrange bentry6)) ++getMappedPaddr globalIdPDChild s0) ; intuition.

					assert(HNoDuplength : length (getMappedPaddr globalIdPDChild s) 
																	= length (getAllPaddrBlock (startAddr (blockrange bentry6))
     																										(endAddr (blockrange bentry6))
																			++ getMappedPaddr globalIdPDChild s0))
						by intuition.
					lia.
					intuition.
					intro addr.
					specialize (Hidpdchildmapped addr).
					intuition.

			--- (* pdinsertion <> part *)
					rewrite <- beqAddrFalse in *.
					assert(HconfigmappedEq : (forall partition : paddr,
									 (partition = globalIdPDChild -> False) ->
									 isPDT partition s0 ->
									 getMappedPaddr partition s = getMappedPaddr partition s0))
						by intuition.
					assert(HmappedEq : getMappedPaddr part s = getMappedPaddr part s0).
					{ eapply HconfigmappedEq ; intuition. }
					rewrite HmappedEq. intuition.
		- (* Lib.disjoint (getConfigPaddr part s) (getMappedPaddr part s) *)

			-- destruct (beqAddr globalIdPDChild part) eqn:beqidpdpart ; try(exfalso ; congruence).
				--- (* globalIdPDChild =  part *)
						rewrite <- DependentTypeLemmas.beqAddrTrue in beqidpdpart.
						rewrite <- beqidpdpart in *.
						rewrite Hidpdchildconfigaddr.
						intros addr HaddrInConfigs0.
						rewrite Hidpdchildmapped.
						intro HaddrInMappeds.
						apply in_app_or in HaddrInMappeds.
						destruct Hcons0 as [(HNoDupConfigs0 & HNoDupMappeds0) HDisjointConfigMappeds0].
						specialize (HDisjointConfigMappeds0 addr HaddrInConfigs0).
						destruct HaddrInMappeds as [HaddrInBlock | HaddrInMappeds0]; intuition.

						(* all config addresses must be accessible by Kernel Data Isolation property *)
						assert(HKDIs0 : kernelDataIsolation s0) by intuition.
						unfold kernelDataIsolation in HKDIs0.
						specialize (HKDIs0 currentPart globalIdPDChild
															HcurrentPartitionInPartitionsLists0 HglobalInPartTree).
						apply Lib.disjointPermut in HKDIs0.
						specialize (HKDIs0 addr HaddrInConfigs0).
						assert(HaddrInParentBlock : In addr (getAllPaddrAux [blockToShareInCurrPartAddr] s0)).
						{	simpl.
							specialize (HaddrInBTSIfInnewB addr) ; intuition.
						}
						assert(HbtsInAccessibleMapped : In addr (getAccessibleMappedPaddr currentPart s0)).
						{
							eapply addrInAccessibleBlockIsAccessibleMapped with blockToShareInCurrPartAddr; intuition.
							assert(HaccTrue : addrIsAccessible = true)
								by (rewrite negb_false_iff in * ; trivial).
							rewrite HaccTrue in *.
							trivial.
						}
						intuition.
				--- (* globalIdPDChild <> part *)
						rewrite HconfigPadrEq.
						rewrite <- beqAddrFalse in *.
						assert(HconfigmappedEq : (forall partition : paddr,
										 (partition = globalIdPDChild -> False) ->
										 isPDT partition s0 ->
										 getMappedPaddr partition s = getMappedPaddr partition s0))
							by intuition.
						assert(HmappedEq : getMappedPaddr part s = getMappedPaddr part s0).
						{ eapply HconfigmappedEq ; intuition. }
						rewrite HmappedEq. intuition.
	} (* end of noDupUsedPaddrList *)


(* add global knowledge *)
		assert(HNoDupidpdchild : NoDup (getAllPaddrBlock (startAddr (blockrange bentry6))
					              (endAddr (blockrange bentry6)) ++
					            getMappedPaddr globalIdPDChild s0)).
		{

			(* we show addr can't be at the same time in [newB] and
					UsedPaddr globalIdPDChild s0 by using NoDup *)
			assert(HNoDupUsed : noDupUsedPaddrList s) by intuition. (* proved earlier *)
			unfold noDupUsedPaddrList in *.
			specialize (HNoDupUsed globalIdPDChild HPDTs).
			unfold getUsedPaddr in HNoDupUsed.
			apply Lib.NoDupSplit in HNoDupUsed.
			destruct HNoDupUsed as [HNoDupConfig HNoDupMapped].

			assert(HnewBaddrNotInMapped : Lib.disjoint (getAllPaddrBlock (startAddr (blockrange bentry6))
						              (endAddr (blockrange bentry6)))
						            (getMappedPaddr globalIdPDChild s0)).
			{
						unfold Lib.disjoint.
						intros addr HaddrInnewB HaddrInMapped.
						(* if addr in Mapped, then in used, then all blocks in parent
								where the adress lies points to this child.
									But at s0, no sh1 flags are set, so false *)
						assert(HnotShareds0 : sharedBlockPointsToChild s0)
							by (unfold consistency in * ; unfold consistency2 in * ; intuition).
						unfold sharedBlockPointsToChild in HnotShareds0.
						assert(HcurrPartInPartitionTree : In currentPart (getPartitions multiplexer s0))
							by (intuition ; subst currentPart ; unfold consistency in * ; unfold consistency1 in * ; intuition). (* consistency s0*)
						assert(HaddrInUsed : In addr (getUsedPaddr globalIdPDChild s0)).
						{
							unfold getUsedPaddr. apply in_or_app. intuition.
						}
						assert(HaddrInParentBlock : In addr (getAllPaddrAux [blockToShareInCurrPartAddr] s0)).
									{ eapply HaddrInBTSIfInnewB ; intuition. }
						assert(Hsh1entrys0 : sh1entryAddr blockToShareInCurrPartAddr sh1eaddr s0).
						{ unfold sh1entryAddr. unfold isBE in *.
							destruct (lookup blockToShareInCurrPartAddr (memory s0) beqAddr) ; try(exfalso ; congruence).
							destruct v ; try(exfalso ; congruence).
							subst sh1eaddr. trivial.
						}
						specialize (HnotShareds0 currentPart globalIdPDChild addr
														blockToShareInCurrPartAddr sh1eaddr
														HcurrPartInPartitionTree HidpdIsChild HaddrInUsed
														HaddrInParentBlock HblockInParent	Hsh1entrys0).
						assert(HSHEs0 : isSHE sh1eaddr s0) by intuition. (* consitency s0*)
						unfold sh1entryPDchild in *. unfold sh1entryPDflag in *.
						rewrite <- HSh1Offset in *.
						apply isSHELookupEq in HSHEs0. destruct HSHEs0 as [sh1entrys0 Hlookupsh10].
						rewrite Hlookupsh10 in *.
						rewrite <- Hsh1PDchildbtsNulls0 in *.
						rewrite <- Hsh1PDflagbtsNulls0 in *.
						destruct HnotShareds0 as [HpdchildNulls0 | HpdflagNulls0].
						+ (*global = nullAddr -> contrad *)
							unfold nullAddrExists in *. unfold isPADDR in *.
							rewrite HpdchildNulls0 in *.
							unfold isPDT in *.
							destruct (lookup nullAddr (memory s) beqAddr); try(exfalso ; congruence).
							destruct v ; try(exfalso ; congruence).
						+ (* flag is not null *)
							exfalso ; congruence.
				}
				assert(HNoDupMappeds0 : NoDup (getMappedPaddr globalIdPDChild s0)).
				{
					assert(HNoDupUseds0 : noDupUsedPaddrList s0)
						by (unfold consistency in * ; unfold consistency2 in * ; intuition). (* consistency s0*)
					unfold noDupUsedPaddrList.
					specialize (HNoDupUseds0 globalIdPDChild HPDTs0).
					unfold getUsedPaddr in HNoDupUseds0. apply Lib.NoDupSplit in HNoDupUseds0.
					intuition.
				} (* NoDupUsed at s0*)
				assert(HNoDupnewB : NoDup((getAllPaddrBlock (startAddr (blockrange bentry6))
						              (endAddr (blockrange bentry6))))).
				{
					eapply NoDupPaddrBlock ; intuition.
				}  (*by NoDupPaddrBlock lemma*)
				apply Lib.NoDupSplitInclIff.
				intuition.
		}

		(* propagated from newInsertNewEntry *)
		assert(HaccessiblemappedEq :
		(forall addr : paddr,
						In addr (getAccessibleMappedPaddr globalIdPDChild s) <->
							In addr ((getAllPaddrBlock (startAddr (blockrange bentry6))
				                          (endAddr (blockrange bentry6))) ++
									(getAccessibleMappedPaddr globalIdPDChild s0)))) by intuition.

		assert(HmappedparentEq : forall partition : paddr,
														partition <> globalIdPDChild ->
														isPDT partition s0 ->
														 getMappedPaddr partition s = getMappedPaddr partition s0)
			by intuition.

		assert(HconfigpaddrEq : forall partition : paddr,
		partition <> globalIdPDChild ->
		isPDT partition s0 ->
		getConfigPaddr partition s = getConfigPaddr partition s0) by intuition.

		assert(HusedpaddrEq : forall partition : paddr,
		partition <> globalIdPDChild ->
		isPDT partition s0 ->
		getUsedPaddr partition s = getUsedPaddr partition s0).
		{
			intros part HpartidpdNotEq HPDTparts0.
			unfold getUsedPaddr. f_equal.
			apply HconfigpaddrEq ; intuition.
			apply HmappedparentEq ; intuition.
		}

		(* propagated from newInsertNewEntry *)

		assert(HpartitionsEq : forall partition : paddr,
		partition <> globalIdPDChild ->
		isPDT partition s0 ->
		getPartitions partition s = getPartitions partition s0) by intuition.

		assert(HchildrenEq : forall partition : paddr,
		partition <> globalIdPDChild ->
		isPDT partition s0 ->
		getChildren partition s = getChildren partition s0) by intuition.

		assert(HmappedblocksEq : forall partition : paddr,
				partition <> globalIdPDChild ->
				isPDT partition s0 ->
				(getMappedBlocks partition s) = getMappedBlocks partition s0) by intuition.

		assert(HaccessiblemappedEqNotInPart :
			forall partition : paddr,
			partition <> globalIdPDChild ->
			isPDT partition s0 ->
			(getAccessibleMappedPaddr partition s) = getAccessibleMappedPaddr partition s0)
				by intuition.

	assert(HnoDupPartitionTrees : noDupPartitionTree s).
	{ (* noDupPartitionTree s *)
		(* equality of list getPartitions already proven so immediate proof *)
		assert(Hcons0 : noDupPartitionTree s0)
			by (unfold consistency in * ; unfold consistency1 in * ; intuition).
		unfold noDupPartitionTree.
		assert(HgetPartitionspdEq1 : getPartitions multiplexer s = getPartitions multiplexer olds)
			by intuition.
		assert(HgetPartitionspdEq2 : getPartitions multiplexer olds = getPartitions multiplexer s0)
			by intuition.
		rewrite HgetPartitionspdEq1. rewrite HgetPartitionspdEq2. intuition.
	} (* end of noDupPartitionTree *)

	assert(HisParents : isParent s).
	{ (* isParent s *)
		(* equality of lists getPartitions and getChildren for any partition already proven
			+ no change of pdentry so immediate proof *)
		admit.
	} (* end of isParent *)

	assert(HisChilds : isChild s).
	{ (* isChild s *)
		(* equality of lists getPartitions and getChildren for any partition already proven
			+ no change of pdentry so immediate proof *)
		admit.
	} (* end of isChild *)


	assert(HaccessibleChildPaddrIsAccessibleIntoParents : accessibleChildPaddrIsAccessibleIntoParent s).
	{ (* accessibleChildPaddrIsAccessibleIntoParent s *)
		(* DUP: similar to vertical sharing *)
		assert(Hcons0: accessibleChildPaddrIsAccessibleIntoParent s0)
			by (unfold consistency in * ; unfold consistency2 in * ; intuition).
		unfold accessibleChildPaddrIsAccessibleIntoParent in *.

		intros parent child addr HparentInPartTree HchildInChildList HaddrInAccessibleMappedChilds.
		assert(HPDTparents : isPDT parent s).
		{
			apply partitionsArePDT ; intuition.
		}

		assert(HPDTchilds : isPDT child s).
		{
			eapply childrenArePDT with parent ; intuition.
		}

		destruct H31 as [Hoptionfreeslotslists (olds & (n0 & (n1 & (n2 & (nbleft & Hlists)))))].

		assert(HgetPartitionspdEq : getPartitions multiplexer s = getPartitions multiplexer s0).
		{
			assert(HgetPartitionspdEq1 : getPartitions multiplexer s = getPartitions multiplexer olds)
						by intuition.
			assert(HgetPartitionspdEq2 : getPartitions multiplexer olds = getPartitions multiplexer s0)
						by intuition.
			rewrite HgetPartitionspdEq1. rewrite HgetPartitionspdEq2. intuition.
		}
		rewrite HgetPartitionspdEq in *.

		assert(HpdchildrenEq : getChildren globalIdPDChild s = getChildren globalIdPDChild s0).
		{
			assert(HgetChildrenpdEq1 : getChildren globalIdPDChild s = getChildren globalIdPDChild olds)
						by intuition.
			assert(HgetChildrenpdEq2 : getChildren globalIdPDChild olds = getChildren globalIdPDChild s0)
						by intuition.
			rewrite HgetChildrenpdEq1. rewrite HgetChildrenpdEq2. intuition.
		}
		assert(forall block, In block (getAccessibleMappedBlocks globalIdPDChild s) <->
										In block (newBlockEntryAddr:: (getAccessibleMappedBlocks globalIdPDChild s0)))
				by intuition.
		assert(Hidpdchildmapped : forall addr,
			In addr (getAccessibleMappedPaddr globalIdPDChild s) <->
			In addr
			(getAllPaddrBlock (startAddr (blockrange bentry2)) (endAddr (blockrange bentry2))
					++ getAccessibleMappedPaddr globalIdPDChild s0)) by intuition.

		(*assert(Hidpdchildconfig : getConfigBlocks globalIdPDChild s = getConfigBlocks globalIdPDChild s0).
		{
			assert(Heq1 : getConfigBlocks globalIdPDChild s = getConfigBlocks globalIdPDChild olds) by intuition.
			assert(Heq2 : getConfigBlocks globalIdPDChild olds = getConfigBlocks globalIdPDChild s0) by intuition.
			rewrite Heq1. rewrite Heq2. trivial.
		} (* constructed along the way *)*)

		(*assert(Hidpdaccessiblemappedaddr : getAccessibleMappedPaddr globalIdPDChild s = getAccessibleMappedPaddr globalIdPDChild s0).
		{
			assert(Heq1 : getAccessibleMappedPaddr globalIdPDChild s = getAccessibleMappedPaddr globalIdPDChild olds) by intuition.
			assert(Heq2 : getAccessibleMappedPaddr globalIdPDChild olds = getAccessibleMappedPaddr globalIdPDChild s0) by intuition.
			rewrite Heq1. rewrite Heq2. trivial.
		} (* constructed along the way *)
		rewrite Hidpdaccessiblemappedaddr in *.*)

		destruct (beqAddr child globalIdPDChild) eqn:beqchildpd ; try(exfalso ; congruence).
		- (* child = globalIdPDChild *)
				rewrite <- DependentTypeLemmas.beqAddrTrue in beqchildpd.
				rewrite beqchildpd in *.

				assert(HparentidpdNotEq : parent <> globalIdPDChild). (* child not currentPart *)
				{
					eapply childparentNotEq with s0; intuition.
					unfold consistency in * ; unfold consistency1 in * ; intuition.
					assert(HchildrenparentEq : getChildren parent s = getChildren parent s0).
					{ destruct (beqAddr parent globalIdPDChild) eqn:beqparentpd ; try(exfalso ; congruence).
						- (* parent = globalIdPDChild *)
							(* even in the false case, the children did not change for any partition *)
							rewrite <- DependentTypeLemmas.beqAddrTrue in beqparentpd.
							rewrite beqparentpd in *.
							intuition.
						- (* parent <> globalIdPDChild *)
							assert(HChildrenEqNotInParts0 : forall partition : paddr,
												(partition = globalIdPDChild -> False) ->
												isPDT partition s0 ->
												getChildren partition s = getChildren partition s0)
								by intuition.
							rewrite <- beqAddrFalse in *.
							eapply HChildrenEqNotInParts0 ; intuition.
							assert(HlookuppsEq : lookup parent (memory s) beqAddr = lookup parent (memory s0) beqAddr).
							{
								(* check all values *)
								apply isPDTLookupEq in HPDTparents. destruct HPDTparents as [parententry Hlookupparents].
								apply isSCELookupEq in HSCEs. destruct HSCEs as [scentrys Hlookupsces].
								destruct (beqAddr sceaddr parent) eqn:beqscepdentry; try(exfalso ; congruence).
								rewrite <- DependentTypeLemmas.beqAddrTrue in beqscepdentry.
								rewrite beqscepdentry in *. congruence.
								(* sceaddr <> parent *)
								destruct (beqAddr newBlockEntryAddr parent) eqn:newpdentry ; try(exfalso ; congruence).
								rewrite <- DependentTypeLemmas.beqAddrTrue in newpdentry.
								rewrite newpdentry in *. congruence.
								(* newBlockEntryAddr <> parent *)
								destruct (beqAddr globalIdPDChild parent) eqn:beqpdpdentry; try(exfalso ; congruence).
								rewrite <- DependentTypeLemmas.beqAddrTrue in beqpdpdentry.
								rewrite beqpdpdentry in *. congruence.
								(* globalIdPDChild <> parent *)
								rewrite Hs.
								cbn. rewrite beqAddrTrue.
								rewrite beqscepdentry.
								destruct (beqAddr newBlockEntryAddr sceaddr) eqn:newsceentry.
								rewrite <- DependentTypeLemmas.beqAddrTrue in newsceentry. congruence.
								simpl.
								rewrite newpdentry.
								rewrite beqAddrTrue.
								rewrite <- beqAddrFalse in *.
								repeat rewrite removeDupIdentity ; intuition.
								destruct (beqAddr globalIdPDChild newBlockEntryAddr) eqn:Hf ; try(exfalso ; congruence).
								rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
								simpl.
								destruct (beqAddr globalIdPDChild parent) eqn:Hff ; try(exfalso ; congruence).
								rewrite <- DependentTypeLemmas.beqAddrTrue in Hff. congruence.
								rewrite <- beqAddrFalse in *.
								repeat rewrite removeDupIdentity ; intuition.
							}
							unfold isPDT in *.
							rewrite HlookuppsEq in *.
							destruct (lookup parent (memory s0) beqAddr) ; intuition.
					}
					rewrite HchildrenparentEq in *.
					rewrite <- HpdchildrenEq in *. trivial.
				}

				assert(HPDTparents0 : isPDT parent s0).
				{ eapply partitionsArePDT ; intuition.
					unfold consistency in * ; unfold consistency1 in * ; intuition.
					unfold consistency in * ; unfold consistency1 in * ; intuition.
				}
				assert(HchildrenparentEq : getChildren parent s = getChildren parent s0).
				{ assert(HChildrenEqNotInParts0 : forall partition : paddr,
												(partition = globalIdPDChild -> False) ->
												isPDT partition s0 ->
												getChildren partition s = getChildren partition s0)
								by intuition.
					rewrite <- beqAddrFalse in *.
					eapply HChildrenEqNotInParts0 ; intuition.
				}
				rewrite HchildrenparentEq in *.

				(*assert(Hparent : parent = currentPart).
				{
					assert(HisParents0 : isParent s0)
						by (unfold consistency in * ; unfold consistency1 in * ; intuition). (* consistency *)
					assert(HisChilds0 : isChild s0)
						by (unfold consistency in * ; unfold consistency1 in * ; intuition). (* consistency *)
					assert(In currentPart (getPartitions multiplexer s0))
						by (rewrite HcurrPartEq in * ; unfold consistency in * ; unfold consistency1 in * ; intuition). (* consistency s0*)
					apply uniqueParent with globalIdPDChild s0; intuition.
				}
				subst parent.*)

				assert(HAmappedparentEq : getAccessibleMappedPaddr parent s = getAccessibleMappedPaddr parent s0).
				{
					assert(HAMappedPaddrEqNotInParts0 : (forall partition : paddr,
											(partition = globalIdPDChild -> False) ->
											isPDT partition s0 ->
											getAccessibleMappedPaddr partition s = getAccessibleMappedPaddr partition s0))
						by intuition.
					eapply HAMappedPaddrEqNotInParts0 ; intuition.
				}


				(*unfold getUsedPaddr in HnAddrInUsedChild.
				specialize (HVs0 addr).
				unfold getUsedPaddr in HVs0.
				rewrite Hidpdchildconfigaddr in *.

				apply in_app_or in HnAddrInUsedChild.*)


				(*destruct HnAddrInUsedChild as [HnAddrInUsedChild | HnAddrInUsedChild].
				(* Case getConfigPaddr s0 *)
				apply HVs0. apply in_app_iff. left. assumption.

				specialize (Hidpdchildmapped addr).
				(*destruct Hidpdchildmapped as [Hidpdchildmapped HidpdchildmappedR].*)
				specialize(Hidpdchildmapped HnAddrInUsedChild).*)
				specialize (Hidpdchildmapped addr).
				rewrite Hidpdchildmapped in *.
				apply in_app_or in HaddrInAccessibleMappedChilds.
				destruct HaddrInAccessibleMappedChilds as [HaddrInAccessibleMappedChilds | HaddrInAccessibleMappedChilds].
				(* Case (getAllPaddrBlock (startAddr (blockrange bentry2))
							                (endAddr (blockrange bentry2))) *)
				(* -> false because newB was not mapped at s0 *)



				* (*assert(HaddrInParentBlock : In addr (getAllPaddrAux [newBlockEntryAddr] s)).
					{
							simpl. rewrite HlookupnewBs. trivial.
							assert(Hstart62: (startAddr (blockrange bentry6)) = (startAddr (blockrange bentry2))).
							{ 	assert(Hstart65 : (startAddr (blockrange bentry6)) = (startAddr (blockrange bentry5))).
									{
										subst bentry6.
										unfold CBlockEntry.
										destruct (lt_dec (blockindex bentry5) kernelStructureEntriesNb) ; intuition.
										simpl. destruct blockentry_d. destruct bentry5. intuition.
									}
									rewrite Hstart65.
									assert(Hstart54 : (startAddr (blockrange bentry5)) = (startAddr (blockrange bentry4))).
									{
										subst bentry5.
										unfold CBlockEntry.
										destruct (lt_dec (blockindex bentry4) kernelStructureEntriesNb) ; intuition.
										simpl. destruct blockentry_d. destruct bentry4. intuition.
									}
									rewrite Hstart54.
									assert(Hstart43 : (startAddr (blockrange bentry4)) = (startAddr (blockrange bentry3))).
									{
										subst bentry4.
										unfold CBlockEntry.
										destruct (lt_dec (blockindex bentry3) kernelStructureEntriesNb) ; intuition.
										simpl. destruct blockentry_d. destruct bentry3. intuition.
									}
									rewrite Hstart43.
									subst bentry3.
									unfold CBlockEntry.
									destruct (lt_dec (blockindex bentry2) kernelStructureEntriesNb) ; intuition.
									simpl. destruct blockentry_d. destruct bentry2. intuition.
							}
							assert(Hend62: (endAddr (blockrange bentry6)) = (endAddr (blockrange bentry2))).
							{ 	assert(Hend65 : (endAddr (blockrange bentry6)) = (endAddr (blockrange bentry5))).
									{
										subst bentry6.
										unfold CBlockEntry.
										destruct (lt_dec (blockindex bentry5) kernelStructureEntriesNb) ; intuition.
										simpl. destruct blockentry_d. destruct bentry5. intuition.
									}
									rewrite Hend65.
									assert(Hend54 : (endAddr (blockrange bentry5)) = (endAddr (blockrange bentry4))).
									{
										subst bentry5.
										unfold CBlockEntry.
										destruct (lt_dec (blockindex bentry4) kernelStructureEntriesNb) ; intuition.
										simpl. destruct blockentry_d. destruct bentry4. intuition.
									}
									rewrite Hend54.
									assert(Hend43 : (endAddr (blockrange bentry4)) = (endAddr (blockrange bentry3))).
									{
										subst bentry4.
										unfold CBlockEntry.
										destruct (lt_dec (blockindex bentry3) kernelStructureEntriesNb) ; intuition.
										simpl. destruct blockentry_d. destruct bentry3. intuition.
									}
									rewrite Hend43.
									subst bentry3.
									unfold CBlockEntry.
									destruct (lt_dec (blockindex bentry2) kernelStructureEntriesNb) ; intuition.
									simpl. destruct blockentry_d. destruct bentry2. intuition.
							}
							rewrite Hstart62 in *. rewrite Hend62 in *.
							rewrite app_nil_r. trivial.
					}*)
					assert(HparentInMappedlist : In newBlockEntryAddr (getMappedBlocks currentPart s0))
							by intuition. (* by found block or showing no modifs from s*)
					assert(HparentInAccessibleMappedlist : In newBlockEntryAddr (getAccessibleMappedBlocks currentPart s0))
							by intuition. (* by found block or showing no modifs from s*)
					unfold getMappedPaddr.
					induction (getMappedBlocks currentPart s0).
					** intuition.
					** simpl. simpl in HparentInMappedlist. simpl in HaddrInParentBlock.
							destruct HparentInMappedlist as [HparentInMappedlist | HparentInMappedlist].
							subst a.
							unfold isBE in HBEbtss0.
							destruct (lookup blockToShareInCurrPartAddr (memory s0) beqAddr) ; try(exfalso ; congruence).
							destruct v ; try(exfalso ; congruence).
							apply in_app_iff. left. rewrite app_nil_r in *. assumption.
							destruct (lookup a (memory s0) beqAddr) ; intuition.
							destruct v ; intuition.

				*	(* Case (getAccessibleMappedPaddr globalIdPDChild s0) *)
					specialize (Hcons0 parent globalIdPDChild addr HparentInPartTree HchildInChildList).
					apply Hcons0. 
					rewrite HAmappedparentEq in *. assumption.
					apply HVs0. apply in_app_iff. right. assumption.

	- (* child <> globalIdPDChild *)
		destruct (beqAddr parent globalIdPDChild) eqn:beqparentpd ; try(exfalso ; congruence).
		-- (* parent = globalIdPDChild *)
				rewrite <- DependentTypeLemmas.beqAddrTrue in beqparentpd.
				rewrite beqparentpd in *.
				assert(HglobalChildNotEq : globalIdPDChild <> child).
				{ eapply childparentNotEq with s ; try (rewrite HparentEq in  ; intuition. }

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

	} (* end of accessibleChildPaddrIsAccessibleIntoParent *)


	assert(HnoDupKSEntriesLists : noDupKSEntriesList s).
	{ (* noDupKSEntriesList s *)
		admit.
	} (* end of noDupKSEntriesList *)

	assert(HnoDupMappedBlocksLists : noDupMappedBlocksList s).
	{ (* noDupMappedBlocksList s *)
		admit.
	} (* end of noDupMappedBlocksList *)


assert(Hcons1 : consistency1 s).
{
	(** consistency1 **)
	unfold consistency1.
	intuition. admit.
}

(* last checkpoint of consistency2 is s0 since the Sh1 changes didn't happen
		when inserting the entry when the last checkpoint took place *)
assert(Hcons2 : consistency2 s).
{
	(** consistency2 **)
	unfold consistency2.
	(* TODO: move up with rest *)
	assert(HsharedBlockPointsToChilds : sharedBlockPointsToChild s).
	{ (* sharedBlockPointsToChild s*)

			unfold sharedBlockPointsToChild.

			intros parent child addr parentblock sh1entryaddr HparentPartTree HchildIsChild
						 HaddrIsUsed HaddrInParentBlock HParentBlockIsMapped Hsh1entryAddr.

			assert(HsharedToChilds0 : sharedBlockPointsToChild s0)
					by (unfold consistency in * ; unfold consistency2 in * ; intuition). (* consistency2 s0 *)

			destruct (beqAddr parent globalIdPDChild) eqn:beqparentpdchild ; try(exfalso ; congruence).
			- (* parent = globalIdPDChild *)
				rewrite <- DependentTypeLemmas.beqAddrTrue in beqparentpdchild.
				rewrite beqparentpdchild in *.
				(*assert(HNoDupPartTree : noDupPartitionTree s)
					by (unfold consistency in * ; unfold consistency1 in * ; intuition). (* consistency s*)*)
				assert(HglobalChildNotEq : globalIdPDChild <> child)
					by (eapply childparentNotEq with s; intuition).

				assert(HChildGlobalNotEq : child <> globalIdPDChild)
					by (intro Hf ; apply eq_sym in Hf ; intuition).
				assert(HusedblocksEq : getUsedPaddr child s = getUsedPaddr child s0).
				{ eapply HusedpaddrEq ; intuition.
					eapply childrenArePDT with globalIdPDChild ; intuition.
					unfold consistency in * ; unfold consistency1 in * ; intuition.
					rewrite HpdchildrenEq in *. intuition.
				}

				rewrite HusedblocksEq in *. rewrite HpdchildrenEq in *. rewrite HparentEq in *.

				specialize (HsharedToChilds0 globalIdPDChild child addr parentblock sh1entryaddr
														HparentPartTree HchildIsChild HaddrIsUsed).

				destruct (beqAddr parentblock newBlockEntryAddr) eqn:beqblocknewB ; try(exfalso ; congruence).
				-- (* parentblock = newBlockEntryAddr *)
						rewrite <- DependentTypeLemmas.beqAddrTrue in beqblocknewB.
						rewrite beqblocknewB in *.

						(* specialisation of vetical sharing for the addresses in the child that
								didn't change, so all addresses of the child are contained in globalidpdchild.
								This means the address is in getMappedPaddr global s0.
							But, we are here in the case where the address is in [newB].
								This is false because an address can't be in [newB] and
										UsedPaddr globalIdPDChild s0
								at the same time because of the NoDup consistency property *)

						assert(HVs0 : verticalSharing s0) by intuition.
						unfold verticalSharing in HVs0.

						specialize (HVs0 globalIdPDChild child HparentPartTree HchildIsChild).
						unfold incl in *.
						specialize (HVs0 addr HaddrIsUsed).

						assert(HaddrInBlockIsMapped : In addr (getMappedPaddr globalIdPDChild s)).
						{ eapply addrInBlockIsMapped with newBlockEntryAddr ; intuition. } (* addrInBlockIsMapped lemma*)

						(* we show addr can't be at the same time in [newB] and
								UsedPaddr globalIdPDChild s0 by using NoDup *)

						apply Lib.NoDupSplitInclIff in HNoDupidpdchild.
						destruct HNoDupidpdchild as [HNoDups Hdisjointuseds].
						unfold Lib.disjoint in Hdisjointuseds.
						simpl in HaddrInParentBlock. rewrite HlookupnewBs in *.
						rewrite app_nil_r in *.
						specialize (Hdisjointuseds addr HaddrInParentBlock).
						congruence.

				-- (* parentblock <> newBlockEntryAddr *)
						assert(HlookupparentEq : lookup parentblock (memory s) beqAddr = lookup parentblock (memory s0) beqAddr)
							by admit. (*no entry change so s0*)
						unfold sh1entryAddr. unfold sh1entryPDchild. unfold sh1entryPDflag.

						assert(HaddrInBlocks0 : In addr (getAllPaddrAux [parentblock] s0)).
						{
							simpl.
							unfold getAllPaddrAux in HaddrInParentBlock.
							rewrite HlookupparentEq in *.
							assumption.
						} (* block not changed*)
						specialize (HpdchildMappedBlocks parentblock).
						destruct HpdchildMappedBlocks as [HpdchildMappedBlocks HpdchildMappedBlocksR].
						specialize (HpdchildMappedBlocks HParentBlockIsMapped).

						assert(Hlookupsh1Eq : lookup (CPaddr (parentblock + sh1offset)) (memory s) beqAddr =
											lookup (CPaddr (parentblock + sh1offset)) (memory s0) beqAddr)
							by admit. (* only possible match is sh1eaddr -> bts -> not in globalIdPDChild *)
						rewrite Hlookupsh1Eq in *.

						simpl in HpdchildMappedBlocks.

						rewrite <- beqAddrFalse in beqblocknewB.
						destruct HpdchildMappedBlocks as [Hf | HpdchildMappedBlocks]; try (exfalso ; congruence).

						unfold sh1entryAddr in *. rewrite HlookupparentEq in *.
						specialize (HsharedToChilds0 HaddrInBlocks0 HpdchildMappedBlocks).
						apply HsharedToChilds0 ; trivial.

			- (* parent <> globalIdPDChild *)
				destruct (beqAddr child globalIdPDChild) eqn:beqchildpdchild ; try(exfalso ; congruence).
				--- (* child = globalIdPDChild *)
						rewrite <- DependentTypeLemmas.beqAddrTrue in beqchildpdchild.
						rewrite beqchildpdchild in *.
						assert(HcurrPartidpdNotEq : currentPart <> globalIdPDChild) by admit.
							(* child not eq not parent *)
						rewrite <- beqAddrFalse in *.
						assert(HusedblocksEq : getUsedPaddr currentPart s = getUsedPaddr currentPart s0).
						{ apply HusedpaddrEq ; intuition. }

							destruct (beqAddr parentblock newBlockEntryAddr) eqn:beqblocknewB ; try(exfalso ; congruence).
							-- (* parentblock = newBlockEntryAddr *)
									rewrite <- DependentTypeLemmas.beqAddrTrue in beqblocknewB.
									rewrite beqblocknewB in *.
									assert(HnewNotInParent : ~ In newBlockEntryAddr (getMappedBlocks parent s)) by admit.
									congruence.
							-- (* parentblock <> newBlockEntryAddr *)
									assert(HlookupparentEq : lookup parentblock (memory s) beqAddr = lookup parentblock (memory s0) beqAddr)
										by admit.
									unfold sh1entryAddr in *. unfold sh1entryPDchild. unfold sh1entryPDflag.
									rewrite HlookupparentEq in *.

									(* globalidpdchild is child, and parentblock is not newB so didn't change compared to s0
												-> leads to s0 -> OK *)

									assert(HaddrInBlocks0 : In addr (getAllPaddrAux [parentblock] s0)).
									{
										simpl.
										unfold getAllPaddrAux in HaddrInParentBlock.
										rewrite HlookupparentEq in *.
										assumption.
									} (* block not changed*)

									assert(HaddrInBlockisBE : isBE parentblock s0).
									{
										apply addrInBlockisBE with addr ; intuition.
									}
									apply isBELookupEq in HaddrInBlockisBE.
									destruct HaddrInBlockisBE as [bentryparent Hlookupparents0].


									destruct (beqAddr (CPaddr (parentblock + sh1offset)) sh1eaddr) eqn:beqsh1sh1 ; try(exfalso ; congruence).
									---- (* (CPaddr (parentblock + sh1offset)) = sh1eaddr *)
											rewrite <- DependentTypeLemmas.beqAddrTrue in beqsh1sh1.
											rewrite beqsh1sh1 in *.
											rewrite HsEq. cbn. rewrite beqAddrTrue.
											simpl. intuition. subst sh1entry0.
											simpl. left. trivial.
									---- (* (CPaddr (parentblock + sh1offset)) <> sh1eaddr *)
												assert(Hsh1Eq : lookup (CPaddr (parentblock + sh1offset)) (memory s) beqAddr = lookup (CPaddr (parentblock + sh1offset)) (memory s0) beqAddr)
													by admit.
												rewrite Hsh1Eq.
												rewrite HparentEq in *.
												rewrite <- beqAddrFalse in *.

												assert(isPDT parent s0) by admit. (*
													by (apply partitionsArePDT with multiplexer ; intuition).*)

												assert(HparentchildrenEq : getChildren parent s = getChildren parent s0)
													by (apply HchildrenEq ; intuition).
												rewrite HparentchildrenEq in *.

												assert(HparentMappedBlocksEq : (getMappedBlocks parent s) = getMappedBlocks parent s0)
													by (apply HmappedblocksEq ; intuition).
												rewrite HparentMappedBlocksEq in *.


												assert(Husedpdchild : In addr (getUsedPaddr globalIdPDChild s) ->
												       				In addr  ((getConfigPaddr globalIdPDChild s0 ++ getMappedPaddr globalIdPDChild s0)
																		++ getAllPaddrAux [newBlockEntryAddr] s)).
												{
													unfold getUsedPaddr.
													rewrite Hidpdchildconfigaddr.
													intro HInUsed.
													apply in_app_or in HInUsed.
													destruct HInUsed as [HInUsed | HInUsed].
													apply in_app_iff. left. apply in_app_iff. left. assumption.
													specialize (Hidpdchildmapped addr).
													destruct Hidpdchildmapped as [Hidpdchildmapped HidpdchildmappedR].
													specialize (Hidpdchildmapped HInUsed).
													simpl. rewrite HlookupnewBs.
													apply in_app_or in Hidpdchildmapped.
													apply in_app_iff. rewrite app_nil_r.
													destruct Hidpdchildmapped as [Hidpdchildmapped | Hidpdchildmapped].
													right. assumption.
													left. apply in_app_iff. right. assumption.
												}

												apply Husedpdchild in HaddrIsUsed.
												rewrite in_app_iff in HaddrIsUsed.

												destruct HaddrIsUsed as [HaddrIsUseds0 | HaddrIsUsed].
												----- (* addr in globalidpd's UsedPaddr s0*)
															assert (Haddrusedblocks0 : getUsedPaddr globalIdPDChild s0 = (getConfigPaddr globalIdPDChild s0 ++ getMappedPaddr globalIdPDChild s0)).
															{ unfold getUsedPaddr. trivial. }
															rewrite <- Haddrusedblocks0 in *.
															specialize (HsharedToChilds0 parent globalIdPDChild addr parentblock sh1entryaddr
																														HparentPartTree HchildIsChild
																														HaddrIsUseds0 HaddrInBlocks0
																														HParentBlockIsMapped Hsh1entryAddr).
															rewrite Hlookupparents0 in *.
															unfold sh1entryPDchild in *. unfold sh1entryPDflag in *.
															subst sh1entryaddr. assumption.

												----- (* addr in [newB] -> should be false because parentblock <> newB
																					so In addr [newB] <> In addr [parentblock] *)
																assert(HcurrentPartInPartitionTree : In currentPart (getPartitions multiplexer s0))
																	by (intuition ; subst currentPart ;
																			unfold consistency in * ; unfold consistency1 in * ; intuition). (* consistency s0 *)
																assert(HisChilds0 : isChild s0)
																	by (unfold consistency in * ; unfold consistency1 in * ; intuition).
																assert(HisParents0 : isParent s0)
																	by (unfold consistency in * ; unfold consistency1 in * ; intuition).
																specialize (uniqueParent globalIdPDChild currentPart parent s0
																							HisChilds0 HisParents0
																							HcurrentPartInPartitionTree
																							HparentPartTree  HglobalInPartTree
																							HidpdIsChild HchildIsChild).
																intro Hparent.
																subst parent.

																assert(HBTSMapped : In blockToShareInCurrPartAddr (getMappedBlocks currentPart s0))
																		by intuition.
																assert(HNoDupUsedPaddrs : noDupUsedPaddrList s0)
																	by (unfold consistency in * ; unfold consistency1 in * ; intuition). (* via consistency *)

																(* DUP *)
																assert(HaddrInParentBlocks : In addr (getAllPaddrAux [blockToShareInCurrPartAddr] s0)).
																{
																	eapply HaddrInBTSIfInnewB ; intuition.
																	simpl in HaddrIsUsed. rewrite HlookupnewBs in *.
																	rewrite app_nil_r in *. trivial.
																}
																	assert(HaddrInparentblock : In addr (getAllPaddrAux [parentblock] s0)).
																	{
																		simpl in *. rewrite HlookupparentEq in *. assumption.
																	} (* given not changed in s0*)

																	assert(HparentBTsNotEq : parentblock <> blockToShareInCurrPartAddr)
																		by admit. (* cause sh1eaddr <> (CPaddr (parentblock + sh1offset))*)
																	assert(HPDTcurrParts0 : isPDT currentPart s0) by intuition. (* consistency *)

																	specialize (DisjointPaddrInPart currentPart parentblock blockToShareInCurrPartAddr addr s0
																								HNoDupUsedPaddrs HPDTcurrParts0 HParentBlockIsMapped HBTSMapped
																								HparentBTsNotEq HaddrInparentblock). (* DisjointPaddrInPart lemma *)
																	intro Hf. congruence.

				--- (* child <> globalIdPDChild *)
							assert(HlookupparentEq : lookup parentblock (memory s) beqAddr = lookup parentblock (memory s0) beqAddr)
								by admit.
							unfold sh1entryAddr in *. unfold sh1entryPDchild. unfold sh1entryPDflag.
							rewrite HlookupparentEq in *.

							(* globalidpdchild is child, and parentblock is not newB so didn't change compared to s0
										-> leads to s0 -> OK *)

							assert(HaddrInBlocks0 : In addr (getAllPaddrAux [parentblock] s0)).
							{
								simpl.
								unfold getAllPaddrAux in HaddrInParentBlock.
								rewrite HlookupparentEq in *.
								assumption.
							} (* block not changed*)

							assert(Hsh1Eq : lookup (CPaddr (parentblock + sh1offset)) (memory s) beqAddr = lookup (CPaddr (parentblock + sh1offset)) (memory s0) beqAddr)
											by admit. (*otherwise parentblock = newB which is false *)
							rewrite Hsh1Eq.
							rewrite HparentEq in *.
							rewrite <- beqAddrFalse in *.

							assert(isPDT parent s0) by admit. (*
								by (apply partitionsArePDT with multiplexer ; intuition).*)

							assert(HparentchildrenEq : getChildren parent s = getChildren parent s0)
									by (apply HchildrenEq ; intuition).
							rewrite HparentchildrenEq in *.

							assert(HparentMappedBlocks : (getMappedBlocks parent s) = getMappedBlocks parent s0).
							{	eapply HmappedblocksEq ; intuition. }
							rewrite HparentMappedBlocks in *.

							assert(HchildusedBlocksEq : (getUsedPaddr child s) = getUsedPaddr child s0).
							{ eapply HusedpaddrEq ; intuition.
								eapply childrenArePDT with parent ; intuition.
								unfold consistency in * ; unfold consistency1 in * ; intuition.
							}

							rewrite HchildusedBlocksEq in *.

							specialize (HsharedToChilds0 parent child addr parentblock sh1entryaddr
													HparentPartTree HchildIsChild HaddrIsUsed HaddrInBlocks0
													HParentBlockIsMapped Hsh1entryAddr).
							unfold sh1entryPDchild in *. unfold sh1entryPDflag in *.
							destruct (lookup parentblock (memory s0) beqAddr) ; try(exfalso ; congruence).
							destruct v ; try(exfalso ; congruence).
							subst sh1entryaddr. assumption.
	}
}
assert(Hconsistency : consistency s).
{
	unfold consistency.

	split.
	- (** consistency1 **)
		intuition.


	- (** consistency2 **)
		intuition.
}

split. intuition. (* consistency s*)

- (** security properties **)

assert(HVS : verticalSharing s).

	{ (* verticalSharing s*)

		apply AddMemoryBlockVS with idPDchild idBlockToShare r w e currentPart
  blockToShareInCurrPartAddr addrIsNull rcheck isChildCurrPart globalIdPDChild
  nbfreeslots zero isFull childfirststructurepointer slotIsNull addrIsAccessible
  addrIsPresent PDChildAddr pdchildIsNull vidtBlockGlobalId blockstart blockend blockToShareChildEntryAddr
  pdentry pdentry0 pdentry1 bentry bentry0 bentry1 bentry2 bentry3 bentry4 bentry5
  bentry6 sceaddr scentry newBlockEntryAddr newFirstFreeSlotAddr
  predCurrentNbFreeSlots sh1eaddr sh1entry sh1entry0 sh1entry1 sh1entrybts
  Hoptionlists olds n0 n1 n2 nbleft s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12; intuition.
	unfold AddMemoryBlockPropagatedProperties ; intuition.
	admit.
}


assert(HKI : kernelDataIsolation s).

	{ (* kernelDataIsolation s*)

		apply AddMemoryBlockKI with idPDchild idBlockToShare r w e currentPart
  blockToShareInCurrPartAddr addrIsNull rcheck isChildCurrPart globalIdPDChild
  nbfreeslots zero isFull childfirststructurepointer slotIsNull addrIsAccessible
  addrIsPresent PDChildAddr pdchildIsNull vidtBlockGlobalId blockstart blockend blockToShareChildEntryAddr
  pdentry pdentry0 pdentry1 bentry bentry0 bentry1 bentry2 bentry3 bentry4 bentry5
  bentry6 sceaddr scentry newBlockEntryAddr newFirstFreeSlotAddr
  predCurrentNbFreeSlots sh1eaddr sh1entry sh1entry0 sh1entry1 sh1entrybts
  Hoptionlists olds n0 n1 n2 nbleft s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12; intuition.
	unfold AddMemoryBlockPropagatedProperties ; intuition.
	admit.
}


assert(HI : partitionsIsolation s).

	{ (* partitionsIsolation s*)

		apply AddMemoryBlockHI with idPDchild idBlockToShare r w e currentPart
  blockToShareInCurrPartAddr addrIsNull rcheck isChildCurrPart globalIdPDChild
  nbfreeslots zero isFull childfirststructurepointer slotIsNull addrIsAccessible
  addrIsPresent PDChildAddr pdchildIsNull vidtBlockGlobalId blockstart blockend blockToShareChildEntryAddr
  pdentry pdentry0 pdentry1 bentry bentry0 bentry1 bentry2 bentry3 bentry4 bentry5
  bentry6 sceaddr scentry newBlockEntryAddr newFirstFreeSlotAddr
  predCurrentNbFreeSlots sh1eaddr sh1entry sh1entry0 sh1entry1 sh1entrybts
  Hoptionlists olds n0 n1 n2 nbleft s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12; intuition.
	unfold AddMemoryBlockPropagatedProperties ; intuition.
	admit.
}

intuition.

Admitted.

