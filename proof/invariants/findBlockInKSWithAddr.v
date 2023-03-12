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

(**  * Summary 
    In this file we formalize and prove all invariants of the MAL and MALInternal functions *)
Require Import Model.Monad Model.Lib Model.MAL.
Require Import Core.Internal.
Require Import Proof.Consistency Proof.DependentTypeLemmas Proof.Hoare
               Proof.Isolation Proof.StateLib Proof.WeakestPreconditions
			   Proof.invariants.Invariants Proof.InternalLemmas.
Require Import Compare_dec Bool List Coq.Logic.ProofIrrelevance Lia.

Lemma findBlockInKSWithAddrAux n (kernelstructurestart blockEntryAddr : paddr) (P : state -> Prop) :
{{  fun (s : state)  => P s /\ consistency s
										/\ isKS kernelstructurestart s}}
Internal.findBlockInKSWithAddrAux n kernelstructurestart blockEntryAddr
{{fun (blockaddr : paddr) (s : state) => P s /\ consistency s /\
																				(blockaddr = nullAddr \/
																	(exists entry, lookup blockaddr s.(memory) beqAddr = Some (BE entry)
																			/\ blockaddr = blockEntryAddr
																			/\ bentryPFlag blockaddr true s
																			/\ In blockaddr (filterOptionPaddr(getKSEntriesAux n
																																kernelstructurestart
																																s ))
																																)
) }}.
Proof.
(* revert mandatory to generalize the induction hypothesis *)
revert kernelstructurestart blockEntryAddr P.
	induction n.
- (* n = 0 *)
	intros;simpl.
	(* MALInternal.getNullAddr *)
	eapply weaken. unfold MALInternal.getNullAddr.
	eapply WP.ret. intros. simpl. intuition.
- (* n = S n*)
	intros. simpl.
	eapply bindRev.
	{ (** leb *)
		eapply weaken. apply Paddr.leb.
		intros. simpl. apply H.
	}
	intro isEntryAddrAboveStart.
	eapply bindRev.
	{ (** zero *)
		eapply weaken. apply Index.zero.
		intros. simpl. apply H.
	}
	intro zero.
	eapply bindRev.
	{ (** getSh1EntryAddrFromKernelStructureStart *)
		eapply weaken. apply getSh1EntryAddrFromKernelStructureStart.
		intros. simpl. apply H.
	}
	intro maxEntryAddrInStructure.
	eapply bindRev.
	{ (** ltb *)
		eapply weaken. apply Paddr.ltb.
		intros. simpl. apply H.
	}
	intro isEntryAddrBelowEnd.
	case_eq (isEntryAddrAboveStart && isEntryAddrBelowEnd).
		+ (* case_eq isEntryAddrAboveStart && isEntryAddrBelowEnd = true *)
			intros.
			eapply bindRev.
			{ (** checkEntry *)
				eapply weaken. apply checkEntry.
				intros. simpl. apply H0.
			}
			intro entryExists.
			case_eq entryExists.
				* (* case_eq entryExists = true *)
					intros. simpl.
					eapply bindRev.
					{ (** MAL.readBlockPresentFromBlockEntryAddr *)
						eapply weaken. apply readBlockPresentFromBlockEntryAddr.
						intros. simpl. split. apply H1. intuition.
					}
					intro isPresent.
					case_eq isPresent.
					-- (* case_eq isPresent = true *)
						intros. simpl. eapply weaken. apply ret.
						intros. simpl. intuition.
						assert(HBE : isBE blockEntryAddr s)
							by intuition.
						right. apply isBELookupEq in HBE. destruct HBE.
						exists x. intuition.

						assert(HNextKSOffsetIsPADDR : NextKSOffsetIsPADDR s)
							by (unfold consistency in * ; unfold consistency1 in * ; intuition).
						unfold NextKSOffsetIsPADDR in *.
						assert(HisKScurr : isKS kernelstructurestart s) by intuition.
						specialize (HNextKSOffsetIsPADDR kernelstructurestart
														(CPaddr (kernelstructurestart + nextoffset))
														HisKScurr).
						assert(HNextKSIsKS : NextKSIsKS s)
								by (unfold consistency in * ; unfold consistency1 in * ; intuition).
						unfold NextKSIsKS in *.
						specialize (HNextKSIsKS kernelstructurestart
															(CPaddr (kernelstructurestart + nextoffset))).
						unfold nextKSAddr in *.
						unfold isKS in *.
						destruct (lookup kernelstructurestart (memory s) beqAddr) eqn:Hlookupcurr ; try(exfalso ; congruence).
						destruct v ; try(exfalso ; congruence).
						unfold isPADDR in *.
						intuition.
						unfold nextKSentry in *. subst.

						unfold Paddr.addPaddrIdx.
						unfold CPaddr in *.
						simpl in *.
						
						destruct (le_dec (kernelstructurestart + nextoffset) maxAddr) eqn:Hnextoffset ; try lia.
						---	(* nextaddr is well formed *)
							assert(HpEq : ADT.CPaddr_obligation_1 (kernelstructurestart + nextoffset) l =
													StateLib.Paddr.addPaddrIdx_obligation_1 kernelstructurestart
										nextoffset l).
							{ apply proof_irrelevance. }
							rewrite HpEq in *.

							destruct (lookup
											{|
											p := kernelstructurestart + nextoffset;
											Hp :=
												StateLib.Paddr.addPaddrIdx_obligation_1 kernelstructurestart
												nextoffset l
											|} (memory s) beqAddr) eqn:Hlookupnext ; intuition.
													destruct v ; intuition.

							specialize (HNextKSIsKS	p HisKScurr).
							intuition.

							destruct (beqAddr p nullAddr) eqn:beqpNull.
							---- (* p = nullAddr *)
									(* there is no following struct *)
									rewrite <- DependentTypeLemmas.beqAddrTrue in beqpNull.
									rewrite beqpNull in *.

									assert(HnullAddrExists : nullAddrExists s)
										by (unfold consistency in * ; unfold consistency1 in * ; intuition).
									unfold nullAddrExists in *. unfold isPADDR in *.

									destruct (lookup nullAddr (memory s) beqAddr) eqn:Hlookupp ; intuition ; try(exfalso ; congruence).
									destruct v ; intuition ; try(exfalso ; congruence).

									assert(HidxEq : CIndex 7 = CIndex (kernelStructureEntriesNb-1)).
									{
										unfold CIndex. simpl in *.
										destruct (le_dec 7 maxIdx) ; trivial.
									}

									assert(kernelStructureEntriesNb < maxIdx-1)
										by (apply KSEntriesNbLessThanMaxIdx).

									assert(kernelStructureEntriesNb-1 < maxIdx)
										by lia.

									assert(CIndex (kernelStructureEntriesNb-1) < CIndex kernelStructureEntriesNb).
									{
										unfold CIndex.
										destruct (le_dec (kernelStructureEntriesNb - 1) maxIdx) ; intuition.
										destruct (le_dec kernelStructureEntriesNb maxIdx) ; intuition.
									}
									assert((CIndex (kernelStructureEntriesNb - 1) < maxIdx+1)).
									{
										unfold CIndex. 
										destruct (le_dec (kernelStructureEntriesNb - 1) maxIdx) ; intuition.
									}
									assert(CIndex (kernelStructureEntriesNb - 1) < kernelStructureEntriesNb).
									{
										unfold CIndex. 
										destruct (le_dec (kernelStructureEntriesNb - 1) maxIdx) ; intuition.
									}
									rewrite andb_true_iff in H.

									eapply blockInRangeInStruct ; intuition ; try lia.
									intuition.
									
									unfold sh1offset in *. unfold blkoffset in *.
									simpl in *.
									rewrite PeanoNat.Nat.add_0_r in *.

									assert(beqAddr blockEntryAddr nullAddr = false).
									{
										rewrite <- beqAddrFalse. intro Hfalse.
										rewrite Hfalse in *.
										unfold isBE in *.
										rewrite Hlookupp in *.
										exfalso ; congruence.
									}

									assert(kernelStructureEntriesNb-1 < sh1offset).
									{
										unfold sh1offset. unfold blkoffset.
										unfold CIndex.
										destruct (le_dec 0 maxIdx) ; intuition ; simpl.
										destruct (le_dec kernelStructureEntriesNb maxIdx) ; intuition.
									}

									assert(HwellFormedSh1 : wellFormedFstShadowIfBlockEntry s)
										by (unfold consistency in * ; unfold consistency1 in * ; intuition).
									unfold wellFormedFstShadowIfBlockEntry.
									assert(HBE : isBE kernelstructurestart s)
										by (unfold isBE ; rewrite Hlookupcurr ; trivial).
									specialize (HwellFormedSh1 kernelstructurestart HBE).
									unfold isSHE in *.

									unfold StateLib.Paddr.leb in *.
									simpl in *.
									rewrite PeanoNat.Nat.leb_le in *.
									unfold StateLib.Paddr.ltb in *.
									rewrite PeanoNat.Nat.ltb_lt in *.
									rewrite PeanoNat.Nat.le_neq in *.
									intuition.

									destruct (le_dec (kernelstructurestart + CIndex kernelStructureEntriesNb) maxAddr) ; intuition.

									unfold CPaddr in *.
									destruct (le_dec (kernelstructurestart + sh1offset) maxAddr) ; intuition.
									unfold CIndex in *. simpl in *.
									destruct (le_dec 7 maxIdx) ; intuition. simpl in *.
									assert(HEqpred : 7 = kernelStructureEntriesNb-1) by intuition.
									rewrite HEqpred in *.
									destruct (le_dec (kernelstructurestart + (kernelStructureEntriesNb - 1)) maxAddr) ; intuition ; try lia.
									destruct (le_dec kernelStructureEntriesNb maxIdx) ; intuition ; try lia.
									destruct blockEntryAddr. simpl in *.
									assert(HEqpred' :7 = kernelStructureEntriesNb-1) by intuition.
									rewrite HEqpred' in *.
									lia.

									unfold isKS.
									rewrite Hlookupcurr. intuition.

									(*unfold isBE. rewrite H5. trivial.*)

							---- (* p <> nullAddr *)
								(* DUP *)
								rewrite <- beqAddrFalse in beqpNull.
								intuition.
								destruct (lookup p (memory s) beqAddr) eqn:Hlookupp ; intuition.
								destruct v ; intuition.

								unfold StateLib.Index.pred.

								(*assert(maxNbPrepare < maxIdx - 1)
									by apply maxNbPrepareNbLessThanMaxIdx.

								destruct (le_dec maxNbPrepare maxIdx) ; intuition ; try lia.
								simpl.*)

								rewrite filterOptionPaddrSplit.
								rewrite in_app_iff. left.

								assert(HEqpred : 7 = kernelStructureEntriesNb-1) by intuition.
								rewrite HEqpred in *.

								assert(kernelStructureEntriesNb < maxIdx-1)
									by (apply KSEntriesNbLessThanMaxIdx).

								assert(kernelStructureEntriesNb-1 < maxIdx)
									by lia.

								unfold CIndex.
								destruct (le_dec (kernelStructureEntriesNb - 1) maxIdx) ; intuition ; try lia.

								rewrite andb_true_iff in H.
								eapply blockInRangeInStruct ; intuition ; try lia.

								unfold sh1offset in *. unfold blkoffset in *.
								simpl in *.
								rewrite PeanoNat.Nat.add_0_r in *.

								assert(beqAddr blockEntryAddr nullAddr = false).
								{
									rewrite <- beqAddrFalse. intro Hfalse.
									rewrite Hfalse in *.
									unfold isBE in *.
									assert(HnullAddrExists : nullAddrExists s)
										by (unfold consistency in * ; unfold consistency1 in * ; intuition).
									unfold nullAddrExists in *. unfold isPADDR in *.

									destruct (lookup nullAddr (memory s) beqAddr) eqn:Hlookupnull ; intuition ; try(exfalso ; congruence).
									destruct v ; intuition ; try(exfalso ; congruence).
								}

								unfold CIndex in *.
								destruct (le_dec kernelStructureEntriesNb maxIdx) ; intuition.
								simpl in *.

								assert(kernelStructureEntriesNb-1 < sh1offset).
								{
									unfold sh1offset. unfold blkoffset.
									unfold CIndex.
									destruct (le_dec 0 maxIdx) ; intuition ; simpl.
									destruct (le_dec kernelStructureEntriesNb maxIdx) ; intuition.
								}

								assert(HwellFormedSh1 : wellFormedFstShadowIfBlockEntry s)
									by (unfold consistency in * ; unfold consistency1 in * ; intuition).
								unfold wellFormedFstShadowIfBlockEntry.
								assert(HBE : isBE kernelstructurestart s)
									by (unfold isBE ; rewrite Hlookupcurr ; trivial).
								specialize (HwellFormedSh1 kernelstructurestart HBE).
								unfold isSHE in *.

								destruct (le_dec (kernelstructurestart + kernelStructureEntriesNb) maxAddr) ; intuition.
								
								unfold StateLib.Paddr.leb in *.
								simpl in *.
								rewrite PeanoNat.Nat.leb_le in *.
								unfold StateLib.Paddr.ltb in *.
								rewrite PeanoNat.Nat.ltb_lt in *.
								rewrite PeanoNat.Nat.le_neq in *.
								intuition.

								unfold CPaddr. unfold CIndex. simpl in *.
								(*destruct (le_dec 7 maxIdx) ; intuition. simpl in *.*)
								assert(HEqpred' : 7 = kernelStructureEntriesNb-1) by intuition.
								rewrite HEqpred' in *.
								destruct (le_dec (kernelstructurestart + (kernelStructureEntriesNb - 1)) maxAddr) ; intuition ; try lia.
								destruct blockEntryAddr. simpl in *.
								assert(HEqpred'': 7 = kernelStructureEntriesNb-1) by intuition.
								rewrite HEqpred'' in *.
								lia.

								unfold isKS.
								rewrite Hlookupcurr. intuition.
										
						--- (* next is not well formed, contradiction *)
							intuition.
						
							assert(HnullAddrExists : nullAddrExists s)
								by (unfold consistency in * ; unfold consistency1 in * ; intuition).
							unfold nullAddrExists in *. unfold isPADDR in *.

							destruct (lookup nullAddr (memory s) beqAddr) eqn:Hlookupp ; intuition ; try(exfalso ; congruence).
							destruct v ; intuition ; try(exfalso ; congruence).

							unfold nullAddr in *.
							unfold CPaddr in *.
							destruct (le_dec 0 maxAddr) ; intuition.
							assert(HpEq : ADT.CPaddr_obligation_1 0 l = ADT.CPaddr_obligation_2)
								by apply proof_irrelevance.
							rewrite HpEq in *.
							exfalso ; congruence.
				-- (* case_eq isPresent = false *)
					intros. eapply weaken. apply ret.
					intros. simpl. intuition.
			* (* case_eq entryExists = false *)
				intros. simpl. eapply weaken. apply ret.
				intros. simpl. intuition.
		+	(* case_eq isEntryAddrAboveStart && isEntryAddrBelowEnd = false *)
			intros.
			eapply bindRev.
			{ (** readNextFromKernelStructureStart *)
				eapply weaken. apply readNextFromKernelStructureStart.
				intros. simpl. split. apply H0. intuition.
				unfold consistency in *. unfold consistency1 in *. intuition.
			}
			intro nextKernelStructure.
			eapply bindRev.
			{ (** Internal.compareAddrToNull *)
				eapply weaken. apply compareAddrToNull.
				intros. simpl. apply H0.
			}
			intro isnull.
			case_eq isnull.
				* (* case_eq isnull = true *)
					intros.
					{ (** ret *)
						eapply weaken. apply ret.
						intros. simpl. intuition.
					}
				* (* case_eq isnull = false *)
					{ (** induction hypothesis *)
						intros.
						eapply strengthen. eapply weaken.
						
						+	eapply IHn.
						+	intros. simpl. split. apply H1. intuition.
							assert(HKS : isKS kernelstructurestart s)
								by intuition.
							apply isKSLookupEq in HKS. destruct HKS as [x (HKS&Hblockidx)].
							destruct H4. (*exists offset : paddr,
												(offset = ...*)
							intuition.
							assert(HnextKSIsKS : NextKSIsKS s)
								by (unfold consistency in * ; unfold consistency1 in * ; intuition).
							unfold NextKSIsKS in *.
							apply HnextKSIsKS with 	(addr:=kernelstructurestart)
													(nextKSaddr:=CPaddr (kernelstructurestart + nextoffset))
													(nextKS:=nextKernelStructure) ;
							intuition.
							- unfold nextKSAddr. rewrite HKS ; trivial.
							- unfold nextKSentry in *. subst x0. intuition.
							(* Prove nextKernelStructure <> nullAddr *)
							- rewrite <- beqAddrFalse in *. intuition.
						+ intros. simpl in *. intuition.
							(* block in next ks *)
							right.
							destruct H11. (*  exists entry : BlockEntry, ...*)
							intuition.
							exists x. intuition.
							subst.
							destruct H6 as [offset Hoffset]. (* exists offset : paddr,
																(offset = ...*)
							destruct Hoffset as [Hoffset HnextKSentry].
							destruct Hoffset as [Hoffset HnextKSaddr].
							assert(HNextKSOffsetIsPADDR : NextKSOffsetIsPADDR s)
								by (unfold consistency in * ; unfold consistency1 in * ; intuition).
							unfold NextKSOffsetIsPADDR in *.
							assert(HisKScurr : isKS kernelstructurestart s) by intuition.
							specialize (HNextKSOffsetIsPADDR kernelstructurestart
															(CPaddr (kernelstructurestart + nextoffset))
															HisKScurr).
							assert(HNextKSIsKS : NextKSIsKS s)
									by (unfold consistency in * ; unfold consistency1 in * ; intuition).
							unfold NextKSIsKS in *.
							specialize (HNextKSIsKS kernelstructurestart
																(CPaddr (kernelstructurestart + nextoffset))).
							unfold nextKSAddr in *.
							unfold isKS in *.
							destruct (lookup kernelstructurestart (memory s) beqAddr) eqn:Hlookupcurr ; try(exfalso ; congruence).
							destruct v ; try(exfalso ; congruence).
							unfold isPADDR in *.
							intuition.
							unfold nextKSentry in *. subst.

							unfold Paddr.addPaddrIdx.
							unfold CPaddr in *.
							simpl in *.
							
							destruct (le_dec (kernelstructurestart + nextoffset) maxAddr) eqn:Hnextoffset ; try lia.
							---	(* nextaddr is well formed *)
								assert(HpEq : ADT.CPaddr_obligation_1 (kernelstructurestart + nextoffset) l =
														StateLib.Paddr.addPaddrIdx_obligation_1 kernelstructurestart
											nextoffset l).
								{ apply proof_irrelevance. }
								rewrite HpEq in *.

								destruct (lookup
												{|
												p := kernelstructurestart + nextoffset;
												Hp :=
													StateLib.Paddr.addPaddrIdx_obligation_1 kernelstructurestart
													nextoffset l
												|} (memory s) beqAddr) eqn:Hlookupnext ; intuition.
														destruct v ; intuition.

								specialize (HNextKSIsKS	p HisKScurr).
								intuition.
								subst.

								destruct (beqAddr p nullAddr) eqn:beqpNull.
								---- (* p = nullAddr *)
										(* there is no following struct *)
										rewrite <- DependentTypeLemmas.beqAddrTrue in beqpNull.
										rewrite beqpNull in *.

										assert(HnullAddrExists : nullAddrExists s)
											by (unfold consistency in * ; unfold consistency1 in * ; intuition).
										unfold nullAddrExists in *. unfold isPADDR in *.

										destruct (lookup nullAddr (memory s) beqAddr) eqn:Hlookupp ; intuition ; try(exfalso ; congruence).
								---- (* p <> nullAddr *)
										rewrite <- beqAddrFalse in beqpNull.
										intuition.

										destruct (lookup p (memory s) beqAddr) eqn:Hlookupp ; intuition.
										destruct v ; intuition.

										rewrite filterOptionPaddrSplit.
										rewrite in_app_iff. right.
										intuition.
							--- (* false, nulladdr not null *)
								unfold nullAddr in *.
								unfold CPaddr in *.
								destruct (le_dec 0 maxAddr) ; intuition.
								assert(HpEq : ADT.CPaddr_obligation_2 =
										ADT.CPaddr_obligation_1 0 l)
									by apply proof_irrelevance.
								rewrite HpEq in *.
								congruence.
					}
Qed.


Lemma findBlockInKSWithAddr (idPD blockEntryAddr: paddr) (P : state -> Prop) :
{{ fun s => P s /\ consistency s /\ isPDT idPD s}}
Internal.findBlockInKSWithAddr idPD blockEntryAddr 
{{fun (blockaddr : paddr) (s : state) => P s /\ consistency s /\
										(blockaddr = nullAddr \/
											(exists entry, lookup blockaddr s.(memory) beqAddr = Some (BE entry)
													/\ blockaddr = blockEntryAddr
													/\ bentryPFlag blockaddr true s
													/\ In blockaddr (getMappedBlocks idPD s))) }}.
Proof.
unfold Internal.findBlockInKSWithAddr.
eapply bindRev.
{ (** readPDStructurePointer *)
	eapply weaken. apply readPDStructurePointer.
	intros. simpl. split. apply H. intuition.
}
intro kernelstructurestart.
eapply bindRev.
{ (** Internal.compareAddrToNull *)
	eapply weaken. apply compareAddrToNull.
	intros. simpl. apply H.
}
intro kernelstructureisnull.
case_eq kernelstructureisnull.
+ (* case_eq kernelstructureisnull = true *)
	intros.
	{ (** ret *)
		eapply weaken. apply ret.
		intros. simpl. intuition.
	}
+ (* case_eq kernelstructureisnull = false *)
	intro Hkernelstructureisnull.
	{ (** findBlockInKSWithAddrAux *)
	eapply strengthen. eapply weaken. apply findBlockInKSWithAddrAux ; intuition.
	intros. simpl in *. split. apply H. intuition.
	rewrite <- beqAddrFalse in *. intuition.
	assert(HPDT : isPDT idPD s)
		by assumption.
	apply isPDTLookupEq in HPDT. destruct HPDT as [pdentry Hlookuppd].

	assert(HStructurePointerIsKS : StructurePointerIsKS s)
		by (unfold consistency in * ; unfold consistency1 in * ; intuition).
	unfold StructurePointerIsKS in *.
	specialize (HStructurePointerIsKS idPD pdentry Hlookuppd).
	unfold pdentryStructurePointer in *.
	rewrite Hlookuppd in *. subst. intuition.
	
	intros. intuition. apply H. apply H. intuition.
	(* block in next ks *)
	right.
	rewrite <- beqAddrFalse in *.
	intuition.
	destruct H5 as [bentry Hbentry]. (* exists entry : BlockEntry,
										lookup a (memory s) beqAddr = Some (BE entry)... *)
	exists bentry. intuition.
	subst a.
	
	unfold getMappedBlocks. unfold getKSEntries.
	assert(HPDT : isPDT idPD s)
		by intuition.
	apply isPDTLookupEq in HPDT. destruct HPDT as [pdentry Hlookuppdentry].
	unfold pdentryStructurePointer in *. rewrite Hlookuppdentry in *.
	subst kernelstructurestart.
	destruct (beqAddr (structure pdentry) nullAddr) eqn:HstructureNull.
	- (* (structure pdentry) = nullAddr *)
		rewrite <- DependentTypeLemmas.beqAddrTrue in HstructureNull.
		exfalso ; congruence.
	-  (* (structure pdentry) <> nullAddr *)
		induction ((filterOptionPaddr (getKSEntriesAux maxNbPrepare (structure pdentry) s (*(CIndex maxNbPrepare)*)))).
		-- intuition.
		-- simpl in *. intuition.
			--- (* a = blockEntryAddr *)
				subst blockEntryAddr.
				rewrite H4. (* lookup a ... *)
				unfold bentryPFlag in *. rewrite H4 in *.
				rewrite <- H5 in *. (* true = present bentry *)
				intuition.
			--- destruct (lookup a (memory s) beqAddr) ; intuition.
				destruct v ; intuition.
				destruct (present b) ; intuition.
	}
Qed.



