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

(**  * Summary
    This file contains the invariants of [findBlockInKS, findBelongingBlock] and
		associated lemmas.
*)
Require Import Model.Monad Model.Lib Model.MAL.
Require Import Core.Internal.
Require Import Proof.Consistency Proof.DependentTypeLemmas Proof.Hoare
               Proof.Isolation Proof.StateLib Proof.WeakestPreconditions
			   Proof.invariants.Invariants Proof.InternalLemmas.
Require Import Compare_dec Bool List Coq.Logic.ProofIrrelevance Lia.
Import List.ListNotations.

Fixpoint isNextKernList (s: state) (kernelsList: list paddr) (baseKern: paddr) :=
match kernelsList with
| nil => True
| nextKern::nextList => lookup (CPaddr (baseKern + nextoffset)) (memory s) beqAddr = Some (PADDR nextKern)
                        /\ isNextKernList s nextList nextKern
end.

Lemma findBlockComp  (entryaddr referenceaddr : paddr) (comparator : index) (P : state -> Prop)  :
{{fun s  =>  P s
						/\ isBE entryaddr s}}
Internal.findBlockComp entryaddr referenceaddr comparator
{{fun isMatch s => P s
                   /\ exists blockstart,
                        bentryStartAddr entryaddr blockstart s
                        /\ (indexEq comparator (CIndex 0) = true ->
                              beqAddr blockstart referenceaddr = isMatch)
                        /\ (indexEq comparator (CIndex 0) = false ->
                              exists bentry,
                                lookup entryaddr (memory s) beqAddr = Some (BE bentry)
                                /\ paddrLe blockstart referenceaddr
                                    && paddrLe referenceaddr (endAddr (blockrange bentry)) = isMatch)
}}.
Proof.
unfold Internal.findBlockComp.
eapply bindRev.
{ (** MAL.readBlockStartFromBlockEntryAddr *)
	eapply weaken. apply readBlockStartFromBlockEntryAddr.
	intros. simpl. split. apply H. intuition.
}
intro blockstart.
eapply bindRev.
{ (** MALInternal.Index.zero *)
	eapply weaken. apply Index.zero.
	intros. simpl. apply H.
}
intro zero. simpl.
destruct indexEq eqn:Hcomp.
- (* beqIdx comparator zero = true *)
	case_eq (beqAddr blockstart referenceaddr).
	+ (* case_eq beqAddr blockstart referenceaddr = true *)
		intros.
		{ (** ret *)
			eapply weaken. apply ret.
			intros. simpl. destruct H0 as [H0 Hzero]. subst zero. intuition. exists blockstart. intuition. congruence.
		}
	+ (* case_eq beqAddr blockstart referenceaddr = false *)
		intros.
		{ (** ret *)
			eapply weaken. apply ret.
			intros. simpl. destruct H0 as [H0 Hzero]. subst zero. intuition. exists blockstart. intuition. congruence.
		}
- (* beqIdx comparator zero = false *)
	eapply bindRev.
	{ (** MAL.readBlockEndFromBlockEntryAddr *)
		eapply weaken. apply readBlockEndFromBlockEntryAddr.
		intros. simpl. split. apply H. intuition.
	}
	intro blockend.
	eapply bindRev.
	{ (** MALInternal.Paddr.leb *)
		eapply weaken. apply Paddr.leb.
		intros. simpl. apply H.
	}
	intro aboveStart.
	eapply bindRev.
	{ (** MALInternal.Paddr.leb *)
		eapply weaken. apply Paddr.leb.
		intros. simpl. apply H.
	}
	intro belowEnd.
	case_eq (aboveStart && belowEnd).
	+ (* case_eq aboveStart && belowEnd = true *)
		intros.
		{ (** ret *)
			eapply weaken. apply ret.
			intros. simpl. intuition. exists blockstart. subst zero. rewrite Hcomp in *. intuition.
      subst aboveStart. subst belowEnd. unfold bentryEndAddr in H4.
      destruct (lookup entryaddr (memory s) beqAddr) eqn:Hlookup; try(exfalso; congruence).
      destruct v; try(exfalso; congruence). exists b. subst blockend. intuition.
		}
	+ (* case_eq aboveStart && belowEnd = false *)
		intros.
		{ (** ret *)
			eapply weaken. apply ret.
			intros. simpl. intuition. exists blockstart. subst zero. rewrite Hcomp in *. intuition.
      subst aboveStart. subst belowEnd. unfold bentryEndAddr in H4.
      destruct (lookup entryaddr (memory s) beqAddr) eqn:Hlookup; try(exfalso; congruence).
      destruct v; try(exfalso; congruence). exists b. subst blockend. intuition.
		}
Qed.

Lemma findBlockInKSInStructAux n (currentidx : index)
																(currentkernelstructure referenceaddr : paddr)
																(compoption : index) (P : state -> Prop) :
{{  fun s : state => P s /\ consistency1 s
										/\ isKS currentkernelstructure s
										/\ currentidx < kernelStructureEntriesNb
}}
Internal.findBlockInKSInStructAux n currentidx currentkernelstructure referenceaddr compoption
{{fun (blockaddr : paddr) (s : state) => P s /\ consistency1 s /\
		(blockaddr = nullAddr
				\/ (exists entry, lookup blockaddr s.(memory) beqAddr = Some (BE entry)
					/\ bentryPFlag blockaddr true s
					/\ (exists finalidx, (In blockaddr (filterOptionPaddr(getKSEntriesInStructAux (maxIdx+1)
																								currentkernelstructure
																								s
																								finalidx))
										/\ finalidx < kernelStructureEntriesNb))
          /\ exists blockstart: paddr,
                  bentryStartAddr blockaddr blockstart s
                  /\ (indexEq compoption (CIndex 0) = true ->
                        beqAddr blockstart referenceaddr = true)
                  /\ (indexEq compoption (CIndex 0) = false ->
                        exists bentry idx,
                          lookup (CPaddr (currentkernelstructure + blkoffset + idx)) (memory s) beqAddr
                            = Some (BE bentry)
                          /\ paddrLe blockstart referenceaddr
                              && paddrLe referenceaddr (endAddr (blockrange bentry)) = true)
))
}}.
Proof.
(* revert mandatory to generalize the induction hypothesis *)
revert currentidx currentkernelstructure referenceaddr compoption.
induction n.
- (* n = 0 *)
	intros;simpl.
	{	(* MALInternal.getNullAddr *)
		eapply weaken. unfold MALInternal.getNullAddr.
		eapply WP.ret. intros. simpl. intuition.
	}
- (* n = S n*)
	intros.
	eapply bindRev.
	{ (** getBlockEntryAddrFromKernelStructureStart *)
		eapply weaken. apply getBlockEntryAddrFromKernelStructureStart.
		intros. split. apply H. unfold consistency1 in *.
		cbn. intuition.
	}
	intro entryaddr. simpl.
	eapply bindRev.
	{ (** MAL.readBlockPresentFromBlockEntryAddr *)
		eapply weaken. apply readBlockPresentFromBlockEntryAddr.
		intros. simpl. split. apply H. intuition.
	}
	intro ispresent.
	eapply bindRev.
	{ (** findBlockComp *)
		eapply weaken. apply findBlockComp.
		intros. simpl. split. apply H. intuition.
	}
	intro matchcomp.
	case_eq (ispresent && matchcomp).
	+ (* case_eq ispresent && matchcomp = true *)
		intros.
		{ (** ret *)
			eapply weaken. apply ret.
			intros. simpl. intuition. right.
			assert(HmatchTrue : matchcomp = true).
			{
				rewrite andb_true_iff in *. intuition.
			}
			rewrite HmatchTrue in *.
			assert(HBEentryaddr : isBE entryaddr s)
				by intuition.
			apply isBELookupEq in HBEentryaddr.
			destruct HBEentryaddr as [bentry Hlookups].
			exists bentry. intuition.
			assert(HpresentTrue : ispresent = true).
			{
				rewrite andb_true_iff in *. intuition.
			}
			rewrite HpresentTrue in *. intuition.
			- exists currentidx.
			  assert(HmaxIdx : maxIdx + 1 = S maxIdx) by (apply MaxIdxNextEq).
			  rewrite HmaxIdx. simpl.
			  unfold Paddr.addPaddrIdx.
			  simpl in *. rewrite PeanoNat.Nat.add_0_r in *.
			  unfold CPaddr in *.
			  destruct (le_dec (currentkernelstructure + currentidx) maxAddr) ; intuition.
			  +	assert(HpEq : ADT.CPaddr_obligation_1 (currentkernelstructure + currentidx) l =
										  StateLib.Paddr.addPaddrIdx_obligation_1 currentkernelstructure
                 currentidx l).
				  { apply proof_irrelevance. }
				  rewrite HpEq in *.
				  subst entryaddr.
				  rewrite Hlookups in *.
				  destruct (beqIdx currentidx zero) eqn:beqcurrIdxZero.
				  -- simpl. left. trivial.
				  -- unfold beqIdx in beqcurrIdxZero. rewrite PeanoNat.Nat.eqb_neq in beqcurrIdxZero.
						  destruct (StateLib.Index.pred currentidx) eqn:HpredIdx ; intuition.
						  simpl. left. trivial.
						  unfold StateLib.Index.pred in *.
						  destruct (gt_dec currentidx 0) ; try(exfalso ; congruence).
						  unfold zero in *. unfold CIndex in *. destruct (le_dec 0 maxIdx) ; intuition.
						  simpl in *. lia. (* contradiction *)
			  + destruct entryaddr. simpl in *.
				  inversion H1 as [Heq]. (* {| p := p; Hp := Hp |} =
										  {| p := 0; Hp := ADT.CPaddr_obligation_2 |}*)
				  subst p.
				  assert(HnullAddrExistss : nullAddrExists s)
						  by (unfold consistency1 in * ; intuition).
				  unfold nullAddrExists in *. unfold isPADDR in *. unfold nullAddr in *.
				  unfold CPaddr in *. destruct (le_dec 0 maxAddr) ; intuition.
				  assert(HpEq : Hp = ADT.CPaddr_obligation_1 0 l ).
				  { apply proof_irrelevance. }
				  rewrite <- HpEq in *.
				  rewrite Hlookups in *. congruence.
      - subst entryaddr. destruct H2 as [blockstart Hblockstart]. exists blockstart. intuition.
        unfold bentryStartAddr in H1.
        destruct H10 as [bentryBis Hbentry]. exists bentryBis. exists currentidx. intuition.
		}
	+ (* case_eq ispresent && matchcomp = false *)
		intros.
		eapply bindRev.
		{ (** getKernelStructureEntriesNb *)
			eapply weaken. apply getKernelStructureEntriesNb.
			intros. simpl. apply H0.
		}
		intro maxentriesnb.
		eapply bindRev.
		{ (** succ *)
			eapply weaken. apply Index.succ.
			intros. simpl. split. apply H0. intuition.
			apply PeanoNat.Nat.lt_le_incl.
			rewrite KSEntriesNbLessThanMaxIdx in *.
			apply PeanoNat.Nat.lt_add_lt_sub_l in H9.
			rewrite PeanoNat.Nat.add_comm. assumption.
		}
		intro nextidx.
		eapply bindRev.
		{ (** Index.ltb *)
			eapply weaken. apply Index.ltb.
			intros. simpl. apply H0.
		}
		intro isnotlastidx.
		case_eq (isnotlastidx).
		* (* case_eq isnotlastidx = true *)
			intros.
			{ (** induction hypothesis *)
				fold findBlockInKSInStructAux.
				eapply weaken. eapply strengthen. eapply IHn.
				intros. simpl. intuition. intuition. intuition.
				- intros. simpl in *. intuition.
				- (* nextidx < kernelStructureEntriesNb checked before *)
					intros. intuition.
					unfold StateLib.Index.ltb in *.
					assert(HnextidxLTB : true = StateLib.Index.ltb nextidx maxentriesnb)
							by intuition.
					apply eq_sym in HnextidxLTB.
					apply PeanoNat.Nat.ltb_lt in HnextidxLTB. subst.
					unfold CIndex in *. destruct (le_dec kernelStructureEntriesNb maxIdx).
					simpl in *. assumption.
					contradict n0. apply PeanoNat.Nat.lt_le_incl.
					apply NPeano.Nat.lt_pred_lt.
					rewrite Minus.pred_of_minus.
					apply KSEntriesNbLessThanMaxIdx.
			}
		* (* case_eq isnotlastidx = false *)
			intros.
			{ (** ret *)
				eapply weaken. apply ret.
				intros. simpl. intuition.
			}
Qed.

Lemma findBlockInKSAux n (currentkernelstructure idblock : paddr)
																(compoption : index) (P : state -> Prop) :
{{  fun s : state => P s /\ consistency1 s
										/\ isKS currentkernelstructure s}}
Internal.findBlockInKSAux n currentkernelstructure idblock compoption
{{fun (blockaddr : paddr) (s : state) => P s /\ consistency1 s /\
((blockaddr = nullAddr
  (*/\ (exists kernList, isListOfKernelsAux kernList currentkernelstructure s
        /\ length kernList >= n)*))
 \/
	(exists entry, lookup blockaddr s.(memory) beqAddr = Some (BE entry)
		/\ bentryPFlag blockaddr true s
		/\  (In blockaddr (filterOptionPaddr(getKSEntriesAux n currentkernelstructure s )))
    /\ exists blockstart : paddr,
            bentryStartAddr blockaddr blockstart s
            /\ (indexEq compoption (CIndex 0) = true ->
                    beqAddr blockstart idblock = true)
            /\ (indexEq compoption (CIndex 0) = false ->
                  exists (kernelsList firstKernList: list paddr) (lastElem: paddr) (idx: nat)
                      (bentry: BlockEntry),
                    isNextKernList s kernelsList currentkernelstructure
                    /\ currentkernelstructure::kernelsList = firstKernList++[lastElem]
                    /\ lookup (CPaddr (lastElem + blkoffset + idx)) (memory s) beqAddr = Some (BE bentry)
                    /\ paddrLe blockstart idblock && paddrLe idblock (endAddr (blockrange bentry)) = true)
	)
)
}}.
Proof.
(* revert mandatory to generalize the induction hypothesis *)
revert currentkernelstructure idblock compoption P.
induction n.
- (* n = 0 *)
	intros;simpl.
	(* MALInternal.getNullAddr *)
	eapply weaken. unfold MALInternal.getNullAddr.
	eapply WP.ret. intros. simpl. intuition. (*left. split. reflexivity. exists []. unfold isListOfKernelsAux.
  intuition.*)
- (* n = S n*)
	unfold Internal.findBlockInKSAux.
	intros.
	eapply bindRev.
	{ (** MALInternal.Index.zero *)
		eapply weaken. apply Index.zero.
		intros. simpl. apply H.
	}
	intro zero.
	eapply bindRev.
	{ (** Internal.findBlockInKSInStructAux *)
		eapply weaken. apply findBlockInKSInStructAux.
		intros. simpl. split. apply H. intuition.
		- (* zero < kernelStructureEntriesNb by axiom *)
			apply CIndex0ltKSEntriesNb. assumption.
		(*- (* zero < maxIdx - 1 by axiom *)
			apply CIndex0ltMaxIdx. assumption.*)
	}
	intro foundblock.
	eapply bindRev.
	{ (** Internal.compareAddrToNull *)
		eapply weaken. apply compareAddrToNull.
		intros. simpl. apply H.
	}
	intro foundblockisnull.
	case_eq foundblockisnull.
	+ (* case_eq foundblockisnull = true *)
		intros.
		eapply bindRev.
		{ (** MAL.readNextFromKernelStructureStart *)
			eapply weaken. apply readNextFromKernelStructureStart.
			intros. simpl. split. apply H0. unfold consistency1 in *.
			unfold consistency1 in *. intuition.
		}
		intro nextkernelstructure.
		eapply bindRev.
		{ (** Internal.compareAddrToNull *)
			eapply weaken. apply compareAddrToNull.
			intros. simpl. apply H0.
		}
		intro nextKSisnull.
		case_eq nextKSisnull.
		* (* case_eq nextKSisnull = true *)
			intros.
		{ (** ret *)
			eapply weaken. apply ret.
			intros. simpl. intuition.
		}
		* (* case_eq nextKSisnull = false *)
			intros.
			{ (** induction hypothesis *)
				fold findBlockInKSAux.
				eapply strengthen. eapply weaken.
						
				+ eapply IHn.
				+ intros. simpl. split. apply H1.

				assert(isKS nextkernelstructure s).
				{ 
					assert(HKS : isKS currentkernelstructure s)
						by intuition.
					intuition.
					* (* foundblock = nullAddr *)
						apply isKSLookupEq in HKS. destruct HKS as [x (HKS&Hblockidx)].
						destruct H4. (* exists offset : paddr, ...*)
						intuition.
						assert(HnextKSIsKS : NextKSIsKS s)
							by (unfold consistency1 in * ; intuition).
						unfold NextKSIsKS in *.
						subst x0.
						apply HnextKSIsKS with 	(addr:=currentkernelstructure)
												(nextKSaddr:=CPaddr (currentkernelstructure + nextoffset))
												(nextKS:=nextkernelstructure) ;
						intuition.
						(* Prove nextKernelStructure <> nullAddr *)
						rewrite <- beqAddrFalse in *. congruence.
					* (* foundblock in current ks structure*)
						(* DUP *)
						apply isKSLookupEq in HKS. destruct HKS as [x (HKS&Hblockidx)].
						destruct H4. (* exists offset : paddr, ...*)
						intuition.
						assert(HnextKSIsKS : NextKSIsKS s)
							by (unfold consistency1 in * ; intuition).
						unfold NextKSIsKS in *.
						subst x0.
						apply HnextKSIsKS with 	(addr:=currentkernelstructure)
																		(nextKSaddr:=CPaddr (currentkernelstructure + nextoffset))
																		(nextKS:=nextkernelstructure) ;
						intuition.
						(* Prove nextKernelStructure <> nullAddr *)
						rewrite <- beqAddrFalse in *. congruence.
				}
				intuition.

			+ simpl. intros. intuition.
				* (*foundblock = nullAddr *)
					right.
					destruct H11 as [aentry Ha]. (*exists entry : BlockEntry,
												lookup a (memory s) beqAddr = Some (BE entry) ...*)
					exists aentry. intuition.
          -- subst.
					  destruct H6 as [offset Hoffset]. (*exists offset : paddr,
														  (offset = CPaddr ...*)
					  destruct Hoffset as [Hoffset HnextKSentry].
					  destruct Hoffset as [Hoffset HnextKSaddr].
					  assert(HNextKSOffsetIsPADDR : NextKSOffsetIsPADDR s)
						  by (unfold consistency1 in * ; intuition).
					  unfold NextKSOffsetIsPADDR in *.
					  assert(HisKScurr : isKS currentkernelstructure s) by intuition.
					  specialize (HNextKSOffsetIsPADDR currentkernelstructure
													  (CPaddr (currentkernelstructure + nextoffset))
													  HisKScurr).
					  assert(HNextKSIsKS : NextKSIsKS s)
							  by (unfold consistency1 in * ; intuition).
					  unfold NextKSIsKS in *.
					  specialize (HNextKSIsKS currentkernelstructure
														  (CPaddr (currentkernelstructure + nextoffset))).
					  unfold nextKSAddr in *.
					  unfold isKS in *.
					  destruct (lookup currentkernelstructure (memory s) beqAddr) eqn:Hlookupcurr
                  ; try(exfalso ; congruence).
					  destruct v ; try(exfalso ; congruence).
					  unfold isPADDR in *.
					  intuition.
					  unfold nextKSentry in *. subst.

					  unfold Paddr.addPaddrIdx.
					  unfold CPaddr in *.
					  simpl in *.
					  destruct (le_dec (currentkernelstructure + nextoffset) maxAddr) eqn:Hnextoffset ; try lia.
					  ---	(* nextaddr is well formed *)
						  assert(HpEq : ADT.CPaddr_obligation_1 (currentkernelstructure + nextoffset) l =
												  StateLib.Paddr.addPaddrIdx_obligation_1 currentkernelstructure
									  nextoffset l).
						  { apply proof_irrelevance. }
						  rewrite HpEq in *.

						  destruct (lookup
										  {|
										  p := currentkernelstructure + nextoffset;
										  Hp :=
											  StateLib.Paddr.addPaddrIdx_obligation_1 currentkernelstructure
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
									  by (unfold consistency1 in * ; intuition).
								  unfold nullAddrExists in *. unfold isPADDR in *.

								  destruct (lookup nullAddr (memory s) beqAddr) eqn:Hlookupp ; intuition;
                        try(exfalso ; congruence).
						  ---- (* p <> nullAddr *)
								  (* DUP *)
								  rewrite <- beqAddrFalse in beqpNull.
								  intuition.

								  assert(maxNbPrepare > 0)
									  by apply maxNbPrepareNotZero.
								  
								  assert(CIndex maxNbPrepare > MALInternal.zero).
								  {
									  unfold MALInternal.zero.
									  unfold CIndex.
									  destruct (le_dec 0 maxIdx) ; intuition.
									  assert(maxNbPrepare < maxIdx-1)
										  by apply maxNbPrepareNbLessThanMaxIdx.
									  destruct (le_dec maxNbPrepare maxIdx) ; intuition ; try lia.
								  }
								  unfold StateLib.Index.leb.
								  destruct (PeanoNat.Nat.leb (CIndex maxNbPrepare) MALInternal.zero) eqn:Hcong ; intuition;
                        try lia.
								  rewrite PeanoNat.Nat.leb_le in *. lia.

								  destruct (lookup p (memory s) beqAddr) eqn:Hlookupp ; intuition.
								  destruct v ; intuition.
								  rewrite filterOptionPaddrSplit.
								  rewrite in_app_iff. right.
								  simpl.
								  intuition.
								  --- (* false *)
								  unfold nullAddr in *.
								  unfold CPaddr in *.
								  destruct (le_dec 0 maxAddr) ; intuition.
								  assert(HpEq : ADT.CPaddr_obligation_2 =
										  ADT.CPaddr_obligation_1 0 l)
									  by apply proof_irrelevance.
								  rewrite HpEq in *.
								  congruence.
          -- destruct H15 as [blockstart Hprops]. exists blockstart. intuition.
             destruct H18 as [nextKernelList (firstNextKernList & (kernelStructure & (idx & (bentry &Hprops))))].
             set(kernelsList:= nextkernelstructure::nextKernelList).
             set(firstKernList:= currentkernelstructure::firstNextKernList).
             exists kernelsList. exists firstKernList. exists kernelStructure. exists idx. exists bentry.
             destruct Hprops as [HisNext (Hfirst & (HlookupKern & Hrange))]. intuition.
             ++ subst kernelsList. simpl. destruct H6 as [offset ((Hoffset & HcurrKern) & HnextKern)].
                subst offset. unfold nextKSentry in HnextKern.
                destruct (lookup (CPaddr (currentkernelstructure + nextoffset)) (memory s) beqAddr)
                      eqn:HlookupCurr; try(exfalso; congruence).
                destruct v; try(exfalso; congruence). subst p. intuition.
             ++ subst kernelsList. subst firstKernList. simpl. f_equal. assumption.
				* (* impossible, foundblock is null *)
					rewrite <- DependentTypeLemmas.beqAddrTrue in *.
					subst.
					unfold consistency1 in *.
					unfold nullAddrExists in *.
					intuition. unfold isPADDR in *.
					destruct H5 as [bentryNull (HlookupNull & _)].
					rewrite HlookupNull in *. exfalso ; congruence.
		}
	+ (* case_eq foundblockisnull = false *)
		intros. simpl.
		{ (** ret *)
			eapply weaken. apply ret.
			intros. simpl. intuition.
			right.
			destruct H6 as [bentry Hbentry]. (*exists entry : BlockEntry,
											lookup foundblock (memory s) beqAddr = ...*)
			exists bentry. intuition.
      *	destruct H6 as [finalidx HBlockInStructAux]. (*exists finalidx : index, ...*)
			  assert(HNextKSOffsetIsPADDR : NextKSOffsetIsPADDR s)
						  by (unfold consistency1 in * ; intuition).
					  unfold NextKSOffsetIsPADDR in *.
					  assert(HisKScurr : isKS currentkernelstructure s) by intuition.
					  specialize (HNextKSOffsetIsPADDR currentkernelstructure
													  (CPaddr (currentkernelstructure + nextoffset))
													  HisKScurr).
					  assert(HNextKSIsKS : NextKSIsKS s)
							  by (unfold consistency1 in * ; intuition).
					  unfold NextKSIsKS in *.
					  specialize (HNextKSIsKS currentkernelstructure
														  (CPaddr (currentkernelstructure + nextoffset))).
					  unfold nextKSAddr in *.
					  unfold isKS in *.
					  destruct (lookup currentkernelstructure (memory s) beqAddr) eqn:Hlookupcurr;
                  try(exfalso; congruence).
					  destruct v ; try(exfalso ; congruence).
					  unfold isPADDR in *.
					  intuition.
					  unfold nextKSentry in *. subst.
					  unfold Paddr.addPaddrIdx.
					  unfold CPaddr in *.
					  simpl in *.
					  destruct (le_dec (currentkernelstructure + nextoffset) maxAddr) eqn:Hnextoffset ; try lia.
					  ---	(* nextaddr is well formed *)
						  assert(HpEq : ADT.CPaddr_obligation_1 (currentkernelstructure + nextoffset) l =
												  StateLib.Paddr.addPaddrIdx_obligation_1 currentkernelstructure
									  nextoffset l).
						  { apply proof_irrelevance. }
						  rewrite HpEq in *.

						  destruct (lookup
										  {|
										  p := currentkernelstructure + nextoffset;
										  Hp :=
											  StateLib.Paddr.addPaddrIdx_obligation_1 currentkernelstructure
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
									  by (unfold consistency1 in * ; intuition).
								  unfold nullAddrExists in *. unfold isPADDR in *.

								  destruct (lookup nullAddr (memory s) beqAddr) eqn:Hlookupp ; intuition;
                        try(exfalso; congruence).
								  destruct v ; intuition.
								  subst p.
								  (* DUP *)
								  eapply getKSEntriesInStructAuxInside with (idx := finalidx)(n:=(maxIdx + 1))(m:= (maxIdx+1));
                        intuition ; try lia.
								  +++ unfold isKS. rewrite Hlookupcurr. assumption.
								  +++ destruct finalidx.
									  assert(HidxEq : CIndex 7 = CIndex (kernelStructureEntriesNb-1)).
									  {
										  unfold CIndex. simpl in *.
										  destruct (le_dec 7 maxIdx) ; trivial.
									  }
									  rewrite HidxEq.
									  unfold CIndex.
									  assert(kernelStructureEntriesNb < maxIdx-1)
										  by (apply KSEntriesNbLessThanMaxIdx).
									  destruct (le_dec (kernelStructureEntriesNb - 1) maxIdx) ; intuition ; try lia.
								  +++ assert(HidxEq : CIndex 7 = CIndex (kernelStructureEntriesNb-1)).
									  {
										  unfold CIndex. simpl in *.
										  destruct (le_dec 7 maxIdx) ; trivial.
									  }
									  rewrite HidxEq.
									  unfold CIndex.
									  assert(kernelStructureEntriesNb < maxIdx-1)
										  by (apply KSEntriesNbLessThanMaxIdx).
									  destruct (le_dec (kernelStructureEntriesNb-1) maxIdx) ; intuition ; simpl ; try lia.
									  simpl in *. lia.
								  +++ assert(HidxEq : CIndex 7 = CIndex (kernelStructureEntriesNb-1)).
									  {
										  unfold CIndex. simpl in *.
										  destruct (le_dec 7 maxIdx) ; trivial.
									  }
									  rewrite HidxEq.
									  unfold CIndex.
									  assert(kernelStructureEntriesNb < maxIdx-1)
										  by (apply KSEntriesNbLessThanMaxIdx).
									  destruct (le_dec (kernelStructureEntriesNb-1) maxIdx) ; intuition ; simpl ; try lia.
									  simpl in *. lia.
								  +++ assert(HidxEq : CIndex 7 = CIndex (kernelStructureEntriesNb-1)).
									  {
										  unfold CIndex. simpl in *.
										  destruct (le_dec 7 maxIdx) ; trivial.
									  }
									  rewrite HidxEq.
									  unfold CIndex.
									  assert(kernelStructureEntriesNb < maxIdx-1)
										  by (apply KSEntriesNbLessThanMaxIdx).
									  destruct (le_dec (kernelStructureEntriesNb-1) maxIdx) ; intuition ; simpl ; try lia.
						  ---- (* p <> nullAddr *)
								  (* DUP *)
								  rewrite <- beqAddrFalse in beqpNull.
								  intuition.

								  assert(maxNbPrepare > 0)
									  by apply maxNbPrepareNotZero.
								  
								  assert(CIndex maxNbPrepare > MALInternal.zero).
								  {
									  unfold MALInternal.zero.
									  unfold CIndex.
									  destruct (le_dec 0 maxIdx) ; intuition.
									  assert(maxNbPrepare < maxIdx-1)
										  by apply maxNbPrepareNbLessThanMaxIdx.
									  destruct (le_dec maxNbPrepare maxIdx) ; intuition ; try lia.
								  }
								  unfold StateLib.Index.leb.
								  destruct (PeanoNat.Nat.leb (CIndex maxNbPrepare) MALInternal.zero) eqn:Hcong; intuition;
                      try lia.
								  rewrite PeanoNat.Nat.leb_le in *. lia.

								  destruct (lookup p (memory s) beqAddr) eqn:Hlookupp ; intuition.
								  destruct v ; intuition.
								  rewrite filterOptionPaddrSplit.
								  rewrite in_app_iff. left.

								  (* DUP *)
								  eapply getKSEntriesInStructAuxInside with (idx := finalidx)(n:=(maxIdx + 1))(m:= (maxIdx+1));
                        intuition ; try lia.
								  +++ unfold isKS. rewrite Hlookupcurr. assumption.
								  +++ destruct finalidx.
									  assert(HidxEq : CIndex 7 = CIndex (kernelStructureEntriesNb-1)).
									  {
										  unfold CIndex. simpl in *.
										  destruct (le_dec 7 maxIdx) ; trivial.
									  }
									  rewrite HidxEq.
									  unfold CIndex.
									  assert(kernelStructureEntriesNb < maxIdx-1)
										  by (apply KSEntriesNbLessThanMaxIdx).
									  destruct (le_dec (kernelStructureEntriesNb - 1) maxIdx) ; intuition ; try lia.
								  +++ assert(HidxEq : CIndex 7 = CIndex (kernelStructureEntriesNb-1)).
									  {
										  unfold CIndex. simpl in *.
										  destruct (le_dec 7 maxIdx) ; trivial.
									  }
									  rewrite HidxEq.
									  unfold CIndex.
									  assert(kernelStructureEntriesNb < maxIdx-1)
										  by (apply KSEntriesNbLessThanMaxIdx).
									  destruct (le_dec (kernelStructureEntriesNb-1) maxIdx) ; intuition ; simpl ; try lia.
									  simpl in *. lia.
								  +++ assert(HidxEq : CIndex 7 = CIndex (kernelStructureEntriesNb-1)).
									  {
										  unfold CIndex. simpl in *.
										  destruct (le_dec 7 maxIdx) ; trivial.
									  }
									  rewrite HidxEq.
									  unfold CIndex.
									  assert(kernelStructureEntriesNb < maxIdx-1)
										  by (apply KSEntriesNbLessThanMaxIdx).
									  destruct (le_dec (kernelStructureEntriesNb-1) maxIdx) ; intuition ; simpl ; try lia.
									  simpl in *. lia.
								  +++ assert(HidxEq : CIndex 7 = CIndex (kernelStructureEntriesNb-1)).
									  {
										  unfold CIndex. simpl in *.
										  destruct (le_dec 7 maxIdx) ; trivial.
									  }
									  rewrite HidxEq.
									  unfold CIndex.
									  assert(kernelStructureEntriesNb < maxIdx-1)
										  by (apply KSEntriesNbLessThanMaxIdx).
									  destruct (le_dec (kernelStructureEntriesNb-1) maxIdx) ; intuition ; simpl ; try lia.

					  --- (* false, null is not null -> contradiction  *)
						  unfold nullAddr in *.
						  unfold CPaddr in *.
						  destruct (le_dec 0 maxAddr) ; intuition.
						  assert(HpEq : ADT.CPaddr_obligation_2 =
								  ADT.CPaddr_obligation_1 0 l)
							  by apply proof_irrelevance.
						  rewrite HpEq in *.
						  congruence.
      * destruct H10 as [blockstart Hprops]. exists blockstart. intuition. exists []. exists [].
        exists currentkernelstructure. destruct H13 as [bentryBis (idx & Hprops)]. exists idx. exists bentryBis.
        unfold isNextKernList. intuition.
	}
Qed.


Lemma findBelongingBlock (idPD referenceaddr: paddr) (P : state -> Prop) :
{{ fun s => P s /\ consistency1 s /\ isPDT idPD s}}
Internal.findBelongingBlock idPD referenceaddr
{{fun (blockaddr : paddr) (s : state) => P s /\ consistency1 s /\
			(blockaddr = nullAddr
					\/ (exists entry, lookup blockaddr s.(memory) beqAddr = Some (BE entry)
						/\ bentryPFlag blockaddr true s))
}}.
Proof.
unfold Internal.findBelongingBlock.
eapply bindRev.
{ (** MALInternal.Index.zero *)
	eapply weaken. apply Index.zero.
	intros. simpl. apply H.
}
intro zero.
eapply bindRev.
{ (** MALInternal.Index.succ *)
	eapply weaken. apply Index.succ.
	intros. simpl. split. apply H.
	intuition. rewrite H1. unfold CIndex. destruct (le_dec 0 maxIdx).
	simpl. apply PeanoNat.Nat.lt_le_incl. apply maxIdxBigEnough.
	contradict n. apply PeanoNat.Nat.lt_le_incl. apply maxIdxNotZero.
}
intro one.
eapply bindRev.
{ (** MAL.readPDStructurePointer *)
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
	{ (** Internal.findBlockInKSAux *)
		eapply weaken. eapply strengthen.
		eapply findBlockInKSAux with (P:= P).
		intros. simpl. intuition.
		eapply H. apply H.
		intuition.
		right. destruct H1 as [bentry (Hbentry & (HbentryPFlag & Hleft))]. (*exists entry : BlockEntry, ...*)
		exists bentry. intuition.
		intros. simpl. intuition.
		rewrite <- beqAddrFalse in *. intuition.
		assert(HPDT : isPDT idPD s)
			by assumption.
		apply isPDTLookupEq in HPDT. destruct HPDT as [pdentry Hlookuppd].

		assert(HStructurePointerIsKS : StructurePointerIsKS s)
			by (unfold consistency1 in * ; intuition).
		unfold StructurePointerIsKS in *.
		specialize (HStructurePointerIsKS idPD pdentry Hlookuppd).
		unfold pdentryStructurePointer in *.
		rewrite Hlookuppd in *. subst. intuition.
	}
Qed.

Lemma findBlockInKS (idPD blockEntryAddr: paddr) (P : state -> Prop) :
{{ fun s => P s /\ consistency1 s /\ isPDT idPD s}}
Internal.findBlockInKS idPD blockEntryAddr
{{fun (blockaddr : paddr) (s : state) => P s /\ consistency1 s /\
			(blockaddr = nullAddr
			\/ (exists entry, lookup blockaddr s.(memory) beqAddr = Some (BE entry)
					/\ bentryPFlag blockaddr true s
					/\ In blockaddr (getMappedBlocks idPD s)
          /\ exists blockstart : paddr,
                bentryStartAddr blockaddr blockstart s
                /\ beqAddr blockstart blockEntryAddr = true))
}}.
Proof.
unfold Internal.findBlockInKS.
eapply bindRev.
{ (** MALInternal.Index.zero *)
	eapply weaken. apply Index.zero.
	intros. simpl. apply H.
}
intro zero.
eapply bindRev.
{ (** MAL.readPDStructurePointer *)
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
	{ (** Internal.findBlockInKSAux *)
		eapply strengthen. eapply weaken.
		apply findBlockInKSAux.
		intros. simpl. split. apply H. intuition.

		rewrite <- beqAddrFalse in *. intuition.
		assert(HPDT : isPDT idPD s)
			by assumption.
		apply isPDTLookupEq in HPDT. destruct HPDT as [pdentry Hlookuppd].

		assert(HStructurePointerIsKS : StructurePointerIsKS s)
			by (unfold consistency1 in * ; intuition).
		unfold StructurePointerIsKS in *.
		specialize (HStructurePointerIsKS idPD pdentry Hlookuppd).
		unfold pdentryStructurePointer in *.
		rewrite Hlookuppd in *. subst. intuition.

		intros. simpl. intuition.
		apply H. apply H.

		rewrite <- beqAddrFalse in *.
		intuition.
		right.
		destruct H6 as [bentry (Hbentry & (HbentryPFlag & Hksentries))]. (*exists entry : BlockEntry, ...*)
		exists bentry. intuition.
	  - unfold getMappedBlocks.
	    unfold getKSEntries.
	    assert(HPDT : isPDT idPD s) by assumption.
	    apply isPDTLookupEq in HPDT. destruct HPDT as [idpdentry Hlookupidpd].
	    unfold pdentryStructurePointer in *.
	    unfold isPDT in *.
	    rewrite Hlookupidpd in *.
	    subst.
	    destruct (beqAddr (structure idpdentry) nullAddr) eqn:HksNull ; trivial.
	    + 	(* (structure idpdentry) = nullAddr *)
		    (* contradiction
			    -> nulladdr cannot have a valid nextoffset *)
		    rewrite <- DependentTypeLemmas.beqAddrTrue in HksNull.
		    rewrite HksNull in *.
		    exfalso ; congruence.
	    +	(* (structure idpdentry) <> nullAddr *)
		    induction ((filterOptionPaddr (getKSEntriesAux maxNbPrepare (structure idpdentry) s))) ; simpl in *;
                intuition.
		    subst.
		    unfold bentryPFlag in *. rewrite Hbentry in *.
		    destruct (present bentry) ; simpl ; try lia ; intuition.
		    destruct (lookup a0 (memory s) beqAddr) ; intuition.
		    destruct v;  intuition.
		    destruct (present b) ; intuition.
    - destruct H6 as [blockstart Hprops]. exists blockstart. subst zero. intuition.
	}
Qed.