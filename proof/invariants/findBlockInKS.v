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
    This file contains the invariants of [findBlockInKS, findExactBlockInKS, findBelongingBlock]
	  and associated lemmas.
*)
Require Import Model.Monad Model.Lib Model.MAL.
Require Import Core.Internal.
Require Import Proof.Consistency Proof.DependentTypeLemmas Proof.Hoare
               Proof.Isolation Proof.StateLib Proof.WeakestPreconditions
			   Proof.invariants.Invariants Proof.InternalLemmas.
Require Import Compare_dec Bool List Coq.Logic.ProofIrrelevance Lia Arith.EqNat.
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

(*DUP*)
Lemma findExactBlockComp  (entryaddr startaddr endaddr : paddr) (P : state -> Prop)  :
{{fun s  =>  P s
						/\ isBE entryaddr s}}
Internal.findExactBlockComp entryaddr startaddr endaddr
{{fun isMatch s => P s
                   /\ exists blockstart blockend,
                        bentryStartAddr entryaddr blockstart s
                        /\ bentryEndAddr entryaddr blockend s
                        /\ (beqAddr blockstart startaddr && beqAddr blockend endaddr) = isMatch
}}.
Proof.
unfold Internal.findExactBlockComp.
eapply bindRev.
{ (** MAL.readBlockStartFromBlockEntryAddr *)
	eapply weaken. apply readBlockStartFromBlockEntryAddr.
	intros. simpl. split. apply H. intuition.
}
intro blockstart.
eapply bindRev.
{ (** MAL.readBlockEndFromBlockEntryAddr *)
	eapply weaken. apply readBlockEndFromBlockEntryAddr.
	intros. simpl. split. apply H. intuition.
}
intro blockend. simpl.
case_eq (beqAddr blockstart startaddr).
- (* case_eq beqAddr blockstart startaddr = true *)
	intros.
  case_eq (beqAddr blockend endaddr).
  + (* case_eq beqAddr blockend endaddr = true *)
	  intros.
	  { (** ret *)
		  eapply weaken. apply ret.
		  intros. simpl. intuition. exists blockstart. exists blockend. intuition.
	  }
  + (* case_eq beqAddr blockend endaddr = false *)
	  intros.
	  { (** ret *)
		  eapply weaken. apply ret.
		  intros. simpl. intuition. exists blockstart. exists blockend. intuition. rewrite H. rewrite H0. intuition.
	  }
- (* case_eq beqAddr blockstart starteaddr = false *)
	intros.
	{ (** ret *)
		eapply weaken. apply ret.
		intros. simpl. intuition. exists blockstart. exists blockend. intuition. rewrite H. apply andb_false_l.
	}
Qed.

Lemma findExactBlockInKSInStructAux n (currentidx : index)
																(currentkernelstructure startaddr endaddr : paddr)
																(P : state -> Prop) :
{{  fun s : state => P s /\ consistency1 s
										/\ isKS currentkernelstructure s
										/\ currentidx < kernelStructureEntriesNb
                    /\ kernelStructureEntriesNb - currentidx < n
                    /\ (((In startaddr (getAllPaddrAux (filterPresent (filterOptionPaddr (getKSEntriesInStructAux
															  (kernelStructureEntriesNb-currentidx) currentkernelstructure s
                                (CIndex (kernelStructureEntriesNb-1)))) s) s))
                          \/ exists block blockstart blockend,
                                bentryStartAddr block blockstart s
                                /\ bentryEndAddr block blockend s
                                /\ bentryPFlag block true s
                                /\ In startaddr (getAllPaddrBlock blockstart blockend)
                                /\ In block (filterOptionPaddr (getKSEntriesInStructAux (maxIdx+1)
                                              currentkernelstructure s (CIndex (kernelStructureEntriesNb-1))))
                                /\ (beqAddr blockstart startaddr && beqAddr blockend endaddr = false
                                    (*\/ bentryPFlag block false s*)))
                        \/ ~In startaddr (getAllPaddrAux (filterPresent (filterOptionPaddr
                                          (getKSEntriesInStructAux (maxIdx+1) currentkernelstructure s (CIndex
                                            (kernelStructureEntriesNb - 1)))) s) s))
}}
Internal.findExactBlockInKSInStructAux n currentidx currentkernelstructure startaddr endaddr
{{fun (blockaddr : paddr) (s : state) => P s /\ consistency1 s /\
		((blockaddr = nullAddr
          /\ ((exists block blockstart blockend,
                    bentryStartAddr block blockstart s
                    /\ bentryEndAddr block blockend s
                    /\ bentryPFlag block true s
                    /\ In startaddr (getAllPaddrBlock blockstart blockend)
                    /\ In block (filterOptionPaddr (getKSEntriesInStructAux (maxIdx+1)
                                  currentkernelstructure s (CIndex (kernelStructureEntriesNb-1))))
                    /\ (beqAddr blockstart startaddr && beqAddr blockend endaddr = false
                        (*\/ bentryPFlag block false s*)))
              \/ ~In startaddr (getAllPaddrAux (filterPresent (filterOptionPaddr (getKSEntriesInStructAux
                                    (maxIdx+1) currentkernelstructure s (CIndex (kernelStructureEntriesNb - 1))))
                                    s) s)))
				\/ (exists entry, lookup blockaddr s.(memory) beqAddr = Some (BE entry)
					/\ bentryPFlag blockaddr true s
					/\ (exists finalidx, (In blockaddr (filterPresent (filterOptionPaddr (getKSEntriesInStructAux
                                        (maxIdx+1) currentkernelstructure s finalidx)) s)
										/\ finalidx < kernelStructureEntriesNb))
          /\ exists blockstart blockend: paddr,
                  bentryStartAddr blockaddr blockstart s
                  /\ bentryEndAddr blockaddr blockend s
                  /\ In blockaddr (filterPresent (filterOptionPaddr (getKSEntriesInStructAux (maxIdx+1)
                                currentkernelstructure s (CIndex (kernelStructureEntriesNb-1)))) s)
                  /\ beqAddr blockstart startaddr = true
                  /\ beqAddr blockend endaddr = true
))
}}.
Proof.
(* revert mandatory to generalize the induction hypothesis *)
revert currentidx currentkernelstructure startaddr endaddr.
induction n.
- (* n = 0 *)
	intros.
	{	(* MALInternal.getNullAddr *)
		eapply weaken. unfold MALInternal.getNullAddr.
		eapply WP.ret. intros. simpl. intuition; lia.
	}
- (* n = S n*)
	intros.
	eapply bindRev.
	{ (** getBlockEntryAddrFromKernelStructureStart *)
		eapply weaken. apply getBlockEntryAddrFromKernelStructureStart.
		intros. split. apply H. unfold consistency1 in *.
		cbn. intuition.
	}
	intro entryaddr. (*simpl.*)
	eapply bindRev.
	{ (** MAL.readBlockPresentFromBlockEntryAddr *)
		eapply weaken. apply readBlockPresentFromBlockEntryAddr.
		intros. simpl. split. apply H. intuition.
	}
	intro ispresent.
	eapply bindRev.
	{ (** findBlockComp *)
		eapply weaken. apply findExactBlockComp.
		intros. simpl. split. apply H. intuition.
	}
	intro matchcomp.
	case_eq (ispresent && matchcomp).
	+ (* case_eq ispresent && matchcomp = true *)
		intros.
		{ (** ret *)
			eapply weaken. apply ret.
			intros. cbn -[kernelStructureEntriesNb]. split. intuition. split. intuition. right.
			assert(HmatchTrue : matchcomp = true).
			{
				rewrite andb_true_iff in *. intuition.
			}
			rewrite HmatchTrue in *.
			assert(HBEentryaddr : isBE entryaddr s)
				by intuition.
			apply isBELookupEq in HBEentryaddr.
			destruct HBEentryaddr as [bentry Hlookups].
			exists bentry. split. assumption.
			assert(HpresentTrue : ispresent = true).
		  {
			  rewrite andb_true_iff in *. intuition.
		  }
		  rewrite HpresentTrue in *. split. intuition.
			split.
      {
        exists currentidx.
		    assert(HmaxIdx : maxIdx + 1 = S maxIdx) by (apply MaxIdxNextEq).
		    rewrite HmaxIdx. simpl.
		    unfold Paddr.addPaddrIdx.
		    simpl in *. rewrite PeanoNat.Nat.add_0_r in *.
		    unfold CPaddr in *.
		    destruct (le_dec (currentkernelstructure + currentidx) maxAddr).
		    +	assert(HpEq : ADT.CPaddr_obligation_1 (currentkernelstructure + currentidx) l =
									    StateLib.Paddr.addPaddrIdx_obligation_1 currentkernelstructure
                 currentidx l).
			    { apply proof_irrelevance. }
			    rewrite HpEq in *.
          assert(entryaddr =
                   {|
                     p := currentkernelstructure + currentidx;
                     Hp := StateLib.Paddr.addPaddrIdx_obligation_1 currentkernelstructure currentidx l
                   |}) by intuition.
			    subst entryaddr.
			    rewrite Hlookups in *. split; try(intuition; congruence).
          set(nextAddr:= {|
                           p := currentkernelstructure + currentidx;
                           Hp := StateLib.Paddr.addPaddrIdx_obligation_1 currentkernelstructure currentidx l
                         |}). fold nextAddr in H0. fold nextAddr in Hlookups.
          assert(Hpresent: bentryPFlag nextAddr true s) by intuition. unfold bentryPFlag in Hpresent.
          rewrite Hlookups in Hpresent. apply eq_sym in Hpresent.
          apply presentIsInFilterPresent with bentry; try(assumption).
			    destruct (beqIdx currentidx zero) eqn:beqcurrIdxZero.
			    -- simpl. left. trivial.
			    -- unfold beqIdx in beqcurrIdxZero. rewrite PeanoNat.Nat.eqb_neq in beqcurrIdxZero.
             unfold StateLib.Index.pred. unfold zero in beqcurrIdxZero. unfold CIndex in beqcurrIdxZero.
             destruct (le_dec 0 maxIdx); try(lia). simpl in beqcurrIdxZero.
             destruct (gt_dec currentidx 0); try(lia). simpl. left. reflexivity.
        + assert(Hentry: entryaddr = {| p := 0; Hp := ADT.CPaddr_obligation_2 |}) by intuition.
          assert(Hnull: nullAddrExists s) by (unfold consistency1 in *; intuition).
          unfold nullAddrExists in Hnull. unfold isPADDR in Hnull.
          assert(HeqNull: entryaddr = nullAddr).
          {
            rewrite Hentry. unfold nullAddr. unfold CPaddr. destruct (le_dec 0 maxAddr); try(lia).
            f_equal. apply proof_irrelevance.
          }
          rewrite HeqNull in Hlookups. rewrite Hlookups in Hnull. exfalso; congruence.
      }
		  destruct H0 as (((Hprops & Hentry & HBE) & HPFlag) & Hblock).
      destruct Hblock as [blockstart [blockend (Hstart & Hend & Hbounds)]]. exists blockstart. exists blockend.
      split. assumption. split. assumption. apply andb_prop in Hbounds. split; try(assumption).
      rewrite MaxIdxNextEq.
			assert(HentryTmp: In entryaddr (filterOptionPaddr (getKSEntriesInStructAux (S maxIdx)
                                      currentkernelstructure s currentidx))).
      {
        simpl. unfold blkoffset in *. rewrite <-plus_n_O in *. unfold CPaddr in *. unfold Paddr.addPaddrIdx.
        destruct (le_dec (currentkernelstructure + currentidx) maxAddr).
        + assert(Hentryaddr: forall Hi, entryaddr = {| p := currentkernelstructure + currentidx;
                                                       Hp := Hi |}).
          { rewrite Hentry. intro. f_equal. apply proof_irrelevance. }
          rewrite <-Hentryaddr. rewrite Hlookups.
          destruct (indexEq currentidx zero) eqn:HbeqIdxZero; try(simpl; left; reflexivity).
          unfold indexEq in *. apply beq_nat_false in HbeqIdxZero. unfold StateLib.Index.pred.
          unfold zero in HbeqIdxZero. unfold CIndex in HbeqIdxZero. destruct (le_dec 0 maxIdx); try(lia).
          simpl in HbeqIdxZero. destruct (gt_dec currentidx 0); try(lia). simpl. left; reflexivity.
        + assert(Hnull: nullAddrExists s) by (unfold consistency1 in *; intuition).
          unfold nullAddrExists in Hnull. unfold isPADDR in Hnull.
          assert(HeqNull: entryaddr = nullAddr).
          {
            rewrite Hentry. unfold nullAddr. unfold CPaddr. destruct (le_dec 0 maxAddr); try(lia). f_equal.
            apply proof_irrelevance.
          }
          rewrite HeqNull in *. exfalso. rewrite Hlookups in Hnull. congruence.
      }
      assert(kernelStructureEntriesNb < maxIdx - 1) by (apply KSEntriesNbLessThanMaxIdx).
      assert(present bentry = true).
      { unfold bentryPFlag in HPFlag. rewrite Hlookups in HPFlag. apply eq_sym in HPFlag. assumption. }
      apply presentIsInFilterPresent with bentry; try(assumption).
      apply getKSEntriesInStructAuxInside with (S maxIdx) currentidx; try(assumption); unfold CIndex;
          destruct (le_dec (kernelStructureEntriesNb - 1) maxIdx); try(lia); cbn -[kernelStructureEntriesNb];
          try(lia); intuition.

        (*assert(Hres: In startaddr (getAllPaddrAux [entryaddr] s)).
        {
          unfold isBE in H6.
          destruct (lookup entryaddr (memory s) beqAddr) eqn:HlookupEntry; try(exfalso; congruence).
          destruct v; try(exfalso; congruence). simpl.
          destruct H2 as [blockstart [blockend (Hstart & Hend & Hbounds)]].
          assert(HwellFormed: wellFormedBlock s) by (unfold consistency1 in *; intuition).
          apply andb_prop in H. destruct H. subst matchcomp. subst ispresent.
          specialize(HwellFormed entryaddr blockstart blockend H3 Hstart Hend). destruct HwellFormed.
          unfold bentryStartAddr in Hstart. unfold bentryEndAddr in Hend. rewrite HlookupEntry in *.
          subst blockstart. subst blockend. 
          apply andb_prop in Hbounds. destruct Hbounds as (Hstart & Hend).
          rewrite <-DTL.beqAddrTrue in Hstart. rewrite Hstart in *. rewrite app_nil_r.
          apply getAllPaddrBlockIncl; lia.
        }
        assert(Hcontra: In startaddr (getAllPaddrAux (filterOptionPaddr (getKSEntriesInStructAux (S maxIdx)
                                        currentkernelstructure s (CIndex (kernelStructureEntriesNb - 1)))) s)).
        {
          apply blockIsMappedAddrInPaddrList with entryaddr; assumption.
        }
        exfalso. contradict H9. rewrite MaxIdxNextEq. assumption.*)
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
			intros. simpl. split. apply H0.
      destruct H0 as (((((HPs & Hconsist & HkernIsKS & HidxIsKern & HcurridxBounded & HpropsOr) & Hentryaddr)
                      & HPFlag) & Hblock) & HmaxEntries).
			apply PeanoNat.Nat.lt_le_incl.
			rewrite KSEntriesNbLessThanMaxIdx in HidxIsKern. lia.
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
				fold findExactBlockInKSInStructAux.
				eapply weaken. eapply strengthen. eapply IHn.
				intros s blockOut Hprops. cbn -[kernelStructureEntriesNb] in *.
        destruct Hprops as (HPs & Hconsist & HpropsOr). intuition.
				intros s Hprops. cbn -[kernelStructureEntriesNb].
        destruct Hprops as (((((((HPs & Hconsist & HKS & HidxIsKern & HcurridxBounded & HpropsOr)
                            & Hentry & HBE) & HPFlag) & Hblock) & Hmax) & HnextidxIsSucc) & HnextidxLtMax).
				unfold StateLib.Index.ltb in HnextidxLtMax.
				apply eq_sym in HnextidxLtMax.
				apply PeanoNat.Nat.ltb_lt in HnextidxLtMax. rewrite Hmax in HnextidxLtMax.
        pose proof KSEntriesNbLessThanMaxIdx as HkernNb.
				unfold CIndex in HnextidxLtMax. destruct (le_dec kernelStructureEntriesNb maxIdx); try(exfalso; lia).
				simpl in HnextidxLtMax. split. assumption. split. assumption. split. assumption. split. assumption.
				unfold StateLib.Index.succ in HnextidxIsSucc.
        destruct (lt_dec currentidx maxIdx); try(exfalso; congruence).
        injection HnextidxIsSucc as HnextIsCurrPlusOne. rewrite <-HnextIsCurrPlusOne.
        cbn -[kernelStructureEntriesNb]. split. lia.
        destruct HpropsOr as [HpropsOr | HnotInKernel]; try(right; assumption). left. (*TODO HERE remove ?*)
        destruct HpropsOr as [HcallRec | HfoundWrong]; try(right; assumption).
        destruct (PeanoNat.Nat.ltb (CIndex (kernelStructureEntriesNb - 1))
                                    (kernelStructureEntriesNb - (currentidx+1))) eqn:HltNbKernNleft.
        { (* CIndex (kernelStructureEntriesNb - 1) < kernelStructureEntriesNb - (currentidx+1) *)
          exfalso. apply PeanoNat.Nat.ltb_lt in HltNbKernNleft. unfold CIndex in HltNbKernNleft.
          destruct (le_dec (kernelStructureEntriesNb - 1) maxIdx); try(lia).
          cbn -[kernelStructureEntriesNb] in HltNbKernNleft. lia.
        }
        (* CIndex (kernelStructureEntriesNb - 1) >= n *)
        apply PeanoNat.Nat.ltb_ge in HltNbKernNleft.
        assert(HsuccRec: (kernelStructureEntriesNb - currentidx)
                          = S (kernelStructureEntriesNb - (currentidx + 1))) by lia.
        rewrite HsuccRec in HcallRec.
        assert(Hrec: filterOptionPaddr (getKSEntriesInStructAux (S (kernelStructureEntriesNb - (currentidx + 1)))
                                  currentkernelstructure s (CIndex (kernelStructureEntriesNb - 1)))
                      = filterOptionPaddr (getKSEntriesInStructAux (kernelStructureEntriesNb - (currentidx + 1))
                                  currentkernelstructure s (CIndex (kernelStructureEntriesNb - 1)) ++
                              getKSEntriesInStructAux 1 currentkernelstructure s
                                  (CIndex ((CIndex (kernelStructureEntriesNb - 1))
                                            - (kernelStructureEntriesNb - (currentidx + 1)))))).
        {
          assert(HkernelEntries: kernelEntriesAreValid s) by (unfold consistency1 in *; intuition).
          assert(Hnull: nullAddrExists s) by (unfold consistency1 in *; intuition).
          unfold nullAddrExists in Hnull.
          assert(HeqNull: {| p := 0; Hp := ADT.CPaddr_obligation_2 |} = nullAddr).
          {
            unfold nullAddr. unfold CPaddr. destruct (le_dec 0 maxAddr); try(lia). f_equal.
            apply proof_irrelevance.
          }
          apply getKSEntriesInStructAuxRec; try(lia).
          - assert(HtrivIdx: CIndex (kernelStructureEntriesNb - 1) <= CIndex (kernelStructureEntriesNb - 1))
                  by lia.
            specialize(HkernelEntries currentkernelstructure (CIndex (kernelStructureEntriesNb - 1)) HKS
                  HtrivIdx). unfold CPaddr in HkernelEntries.
            destruct (le_dec (currentkernelstructure + CIndex (kernelStructureEntriesNb - 1)) maxAddr);
                  try(lia). rewrite HeqNull in HkernelEntries. unfold isBE in HkernelEntries.
            unfold isPADDR in Hnull. destruct (lookup nullAddr (memory s) beqAddr); try(exfalso; congruence).
            destruct v; exfalso; congruence.
          - intros idx Hi HidxValid. specialize(HkernelEntries currentkernelstructure idx HKS HidxValid).
            unfold CPaddr in HkernelEntries.
            destruct (le_dec (currentkernelstructure + idx) maxAddr); try(lia).
            assert(HeqEntry:
                      {|
                        p := currentkernelstructure + idx;
                        Hp := ADT.CPaddr_obligation_1 (currentkernelstructure + idx) l1
                      |} = {| p := currentkernelstructure + idx; Hp := Hi |}).
            { f_equal. apply proof_irrelevance. }
            rewrite HeqEntry in HkernelEntries. assumption.
        }
        rewrite Hrec in HcallRec. rewrite filterOptionPaddrSplit in HcallRec.
        rewrite filterPresentSplit in HcallRec. rewrite getAllPaddrAuxSplit in HcallRec.
        apply in_app_or in HcallRec. destruct HcallRec as [HcallRec | HstartInFirst]; try(left; assumption).
        assert(Hsimpl: CIndex (CIndex (kernelStructureEntriesNb - 1) - (kernelStructureEntriesNb -
                                                                        (currentidx + 1)))
                      = currentidx).
        {
          unfold CIndex. destruct (le_dec (kernelStructureEntriesNb - 1) maxIdx); try(lia).
          cbn -[kernelStructureEntriesNb].
          destruct (le_dec (kernelStructureEntriesNb - 1 - (kernelStructureEntriesNb - (currentidx+1))) maxIdx);
              try(lia). destruct currentidx. cbn -[kernelStructureEntriesNb].
          assert(Heq: kernelStructureEntriesNb - 1 - (kernelStructureEntriesNb - (i + 1)) = i).
          {
            rewrite PeanoNat.Nat.sub_add_distr. apply PeanoNat.Nat.add_sub_eq_l.
            assert(i < kernelStructureEntriesNb) by intuition. lia.
          }
          assert(Hres: forall Hi1 Hi2, {| i := kernelStructureEntriesNb-1-(kernelStructureEntriesNb-(i+1));
                                          Hi := Hi1 |}
                                      = {| i := i; Hi := Hi2 |}).
          {
            rewrite Heq. intros. f_equal. apply proof_irrelevance.
          }
          apply Hres.
        }
        rewrite Hsimpl in HstartInFirst. simpl in HstartInFirst. unfold Paddr.addPaddrIdx in HstartInFirst.
        unfold CPaddr in Hentry. unfold blkoffset in Hentry. unfold CIndex in Hentry.
        destruct (le_dec 0 maxIdx); try(lia). simpl in Hentry. rewrite <-plus_n_O in Hentry.
        assert(currentkernelstructure + currentidx <= maxAddr).
        {
          destruct (le_dec (currentkernelstructure + currentidx) maxAddr); try(lia). exfalso.
          rewrite Hentry in HBE. assert(Hnull: nullAddrExists s) by (unfold consistency1 in *; intuition).
          unfold nullAddrExists in Hnull.
          assert(HeqNull: {| p := 0; Hp := ADT.CPaddr_obligation_2 |} = nullAddr).
          {
            unfold nullAddr. unfold CPaddr. destruct (le_dec 0 maxAddr); try(lia). f_equal.
            apply proof_irrelevance.
          }
          rewrite HeqNull in HBE. unfold isBE in HBE. unfold isPADDR in Hnull.
          destruct (lookup nullAddr (memory s) beqAddr); try(congruence). destruct v; congruence.
        }
        destruct (le_dec (currentkernelstructure + currentidx) maxAddr); try(lia).
        assert(Hentryaddr: forall Hi, entryaddr = {| p := currentkernelstructure + currentidx;
                                                     Hp := Hi |}).
        { rewrite Hentry. intro. f_equal. apply proof_irrelevance. }
        rewrite <-Hentryaddr in HstartInFirst. unfold isBE in HBE.
        destruct (lookup entryaddr (memory s) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence).
        assert(HstartInFirstBis: In startaddr (getAllPaddrAux [entryaddr] s) /\ ispresent = true).
        {
          unfold bentryPFlag in HPFlag. destruct (indexEq currentidx zero).
          - simpl in HstartInFirst.
            destruct (lookup entryaddr (memory s) beqAddr); try(simpl in HstartInFirst; exfalso; congruence).
            destruct v; try(simpl in HstartInFirst; exfalso; congruence).
            destruct (present b0); try(simpl in HstartInFirst; exfalso; congruence). split; assumption.
          - destruct (StateLib.Index.pred currentidx); try(simpl in HstartInFirst; exfalso; congruence).
            simpl in HstartInFirst.
            destruct (lookup entryaddr (memory s) beqAddr); try(simpl in HstartInFirst; exfalso; congruence).
            destruct v; try(simpl in HstartInFirst; exfalso; congruence).
            destruct (present b0); try(simpl in HstartInFirst; exfalso; congruence). split; assumption.
        }
        destruct HstartInFirstBis as (HstartInFirstBis & HPFlagTrue).
        simpl in HstartInFirstBis. destruct Hblock as [blockstart [blockend (Hstart & Hend & Hbounds)]].
        right. exists entryaddr. exists blockstart. exists blockend. unfold bentryStartAddr in *.
        unfold bentryEndAddr in *. unfold bentryPFlag in *.
        destruct (lookup entryaddr (memory s) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence). subst blockstart. subst blockend. split. reflexivity. split.
        reflexivity. split. subst ispresent. apply eq_sym. assumption. split.
        rewrite app_nil_r in HstartInFirstBis. assumption. apply andb_false_iff in H.
		    assert(HentryTmp: In entryaddr (filterOptionPaddr (getKSEntriesInStructAux (S maxIdx)
                                        currentkernelstructure s currentidx))).
        {
          simpl. unfold Paddr.addPaddrIdx.
          destruct (le_dec (currentkernelstructure + currentidx) maxAddr); try(lia).
          rewrite <-Hentryaddr.
          assert(HkernEntries: kernelEntriesAreValid s) by (unfold consistency1 in *; intuition).
          assert(HidxBounded: currentidx <= CIndex (kernelStructureEntriesNb - 1)).
          {
            unfold CIndex. destruct (le_dec (kernelStructureEntriesNb - 1) maxIdx); try(lia).
            cbn -[kernelStructureEntriesNb]. lia.
          }
          specialize(HkernEntries currentkernelstructure currentidx HKS HidxBounded).
          unfold CPaddr in HkernEntries.
          destruct (le_dec (currentkernelstructure + currentidx) maxAddr); try(lia).
          rewrite <-Hentryaddr in HkernEntries. unfold isBE in HkernEntries.
          destruct (lookup entryaddr (memory s) beqAddr); try(exfalso; congruence).
          destruct v; try(exfalso; congruence).
          destruct (indexEq currentidx zero) eqn:HbeqIdxZero; try(simpl; left; reflexivity).
          unfold indexEq in *. apply beq_nat_false in HbeqIdxZero. unfold StateLib.Index.pred.
          unfold zero in HbeqIdxZero. unfold CIndex in HbeqIdxZero. destruct (le_dec 0 maxIdx); try(lia).
          simpl in HbeqIdxZero. destruct (gt_dec currentidx 0); try(lia). simpl. left; reflexivity.
        }
        split. apply getKSEntriesInStructAuxInside with (S maxIdx) currentidx; try(assumption); unfold CIndex;
            destruct (le_dec (kernelStructureEntriesNb - 1) maxIdx); try(lia); cbn -[kernelStructureEntriesNb];
            try(lia); intuition.
        destruct H as [HnotPres | HnotBounds].
        - exfalso; congruence.
        - subst matchcomp. assumption.
			}
		* (* case_eq isnotlastidx = false *)
			intros.
			{ (** ret *)
				eapply weaken. apply ret.
				intros s Hprops. simpl. destruct Hprops as (((((((HPs & Hconsist & HKS & HidxIsKern & HcurridxBounded &
                      HpropsOr) & Hentry & HBE) & HPFlag) & Hblock) & Hmax) & HnextidxIsSucc) & HnextidxLtMax).
        split. assumption.  split. assumption. left. split. reflexivity.
        destruct HpropsOr as [HpropsOr | HnotInKernel]; try(right; assumption). left.
        destruct HpropsOr as [HinLeftEntries | HexistsWrongBlock]; try(assumption).
        unfold StateLib.Index.ltb in HnextidxLtMax. apply eq_sym in HnextidxLtMax.
        apply PeanoNat.Nat.ltb_ge in HnextidxLtMax. unfold CIndex in Hmax.
        assert(kernelStructureEntriesNb < maxIdx - 1) by (apply KSEntriesNbLessThanMaxIdx).
        destruct (le_dec kernelStructureEntriesNb maxIdx); try(lia). subst maxentriesnb.
        unfold StateLib.Index.succ in HnextidxIsSucc.
        destruct (lt_dec currentidx maxIdx); try(exfalso; congruence). injection HnextidxIsSucc as Hnextidx.
        rewrite <-Hnextidx in HnextidxLtMax. simpl in HnextidxLtMax.
        assert(Hcurr: kernelStructureEntriesNb -1 = currentidx) by lia.
        rewrite <-Hcurr in *. simpl in HinLeftEntries. change 7 with (kernelStructureEntriesNb - 1) in *.
        unfold Paddr.addPaddrIdx in HinLeftEntries. unfold CIndex in HinLeftEntries.
        destruct (le_dec (kernelStructureEntriesNb-1) maxIdx); try(lia).
        cbn -[kernelStructureEntriesNb] in HinLeftEntries.
        unfold blkoffset in Hentry. rewrite <-plus_n_O in Hentry. unfold CPaddr in Hentry.
        destruct (le_dec (currentkernelstructure + (kernelStructureEntriesNb - 1)) maxAddr);
              try(intuition; congruence).
        assert(Hentryaddr: forall Hi, entryaddr = {| p := currentkernelstructure + (kernelStructureEntriesNb -1);
                                                     Hp := Hi |}).
        { rewrite Hentry. intro. f_equal. apply proof_irrelevance. }
        rewrite <-Hentryaddr in HinLeftEntries. unfold isBE in HBE.
        destruct (lookup entryaddr (memory s) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence).
        destruct (PeanoNat.Nat.eqb (kernelStructureEntriesNb - 1) 0) eqn:HkernelNbMOneNotZero.
        { apply beq_nat_true in HkernelNbMOneNotZero. exfalso. simpl in HkernelNbMOneNotZero. lia. }
        unfold StateLib.Index.pred in HinLeftEntries. apply beq_nat_false in HkernelNbMOneNotZero.
        cbn -[kernelStructureEntriesNb] in *. destruct (gt_dec (kernelStructureEntriesNb - 1) 0); try(lia).
        cbn in HinLeftEntries. destruct Hblock as [blockstart [blockend (Hstart & Hend & Hbounds)]].
        exists entryaddr. exists blockstart. exists blockend. unfold bentryStartAddr in *.
        unfold bentryEndAddr in *. unfold bentryPFlag in *.
        destruct (lookup entryaddr (memory s) beqAddr) eqn:HlookupEntry; try(exfalso; congruence).
        destruct v; try(exfalso; congruence).
        destruct (present b0); try(simpl in HinLeftEntries; exfalso; congruence). simpl in HinLeftEntries.
        rewrite HlookupEntry in HinLeftEntries. subst blockstart. subst blockend. split. reflexivity. split.
        reflexivity. split. reflexivity. split. rewrite app_nil_r in HinLeftEntries. assumption.
        apply andb_false_iff in H. split. rewrite MaxIdxNextEq. cbn -[kernelStructureEntriesNb].
        unfold Paddr.addPaddrIdx. unfold CIndex.
        destruct (le_dec (kernelStructureEntriesNb - 1) maxIdx); try(lia). cbn -[kernelStructureEntriesNb].
        destruct (le_dec (currentkernelstructure + (kernelStructureEntriesNb - 1)) maxAddr); try(lia).
        rewrite <-Hentryaddr. rewrite HlookupEntry.
        assert(HkernMinNotZero: kernelStructureEntriesNb - 1 <> 0) by lia.
        apply PeanoNat.Nat.eqb_neq in HkernMinNotZero. rewrite HkernMinNotZero. unfold StateLib.Index.pred.
        cbn -[kernelStructureEntriesNb]. apply PeanoNat.Nat.eqb_neq in HkernMinNotZero.
        destruct (gt_dec (kernelStructureEntriesNb - 1) 0); try(lia). simpl. left; reflexivity.
        (*assert(HkernEntries: kernelEntriesAreValid s) by (unfold consistency1 in *; intuition).
        assert(HidxBounded: kernelStructureEntriesNb - 1 <= CIndex (kernelStructureEntriesNb - 1)).
        {
          unfold CIndex. destruct (le_dec (kernelStructureEntriesNb - 1) maxIdx); try(lia).
          cbn -[kernelStructureEntriesNb]. lia.
        }
        specialize(HkernEntries currentkernelstructure (kernelStructureEntriesNb - 1) HKS HidxBounded).
        unfold CPaddr in HkernEntries.
        destruct (le_dec (currentkernelstructure + (kernelStructureEntriesNb - 1)) maxAddr); try(lia).
        rewrite <-Hentryaddr in HkernEntries. unfold isBE in HkernEntries.
        destruct (lookup entryaddr (memory s) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence).
        destruct (PeanoNat.Nat.eqb (kernelStructureEntriesNb - 1) zero) eqn:HbeqIdxZero; simpl; left; reflexivity.
        *)
        destruct H as [HnotPres | HnotBounds].
        - exfalso; congruence.
        - subst matchcomp. assumption.
			}
Qed.

(*DUP TODO remove if the above works*)
(*Lemma findExactBlockInKSInStructAux n (currentidx : index)
																(currentkernelstructure startaddr endaddr : paddr)
																(P : state -> Prop) :
{{  fun s : state => P s /\ consistency1 s
										/\ isKS currentkernelstructure s
										/\ currentidx < kernelStructureEntriesNb
                    /\ kernelStructureEntriesNb - currentidx < n
                    /\ ((In startaddr (getAllPaddrAux (filterOptionPaddr (getKSEntriesInStructAux
															  (kernelStructureEntriesNb-currentidx) currentkernelstructure s
                                (CIndex (kernelStructureEntriesNb-1)))) s)
                        (*/\ ~In startaddr (getAllPaddrAux (filterOptionPaddr (getKSEntriesInStructAux n
													      currentkernelstructure s (CIndex (kernelStructureEntriesNb-1-currentidx)))) s)*))
                        \/ exists block blockstart blockend,
                              bentryStartAddr block blockstart s
                              /\ bentryEndAddr block blockend s
                              /\ In startaddr (getAllPaddrBlock blockstart blockend)
                              /\ (beqAddr blockstart startaddr && beqAddr blockend endaddr = false
                                  \/ bentryPFlag block false s))
}}
Internal.findExactBlockInKSInStructAux n currentidx currentkernelstructure startaddr endaddr
{{fun (blockaddr : paddr) (s : state) => P s /\ consistency1 s
    /\ (*In startaddr (getAllPaddrAux (filterOptionPaddr (getKSEntriesInStructAux n
							  currentkernelstructure s (CIndex (kernelStructureEntriesNb-1)))) s) /\*)
		((blockaddr = nullAddr
          /\ (exists block blockstart blockend,
                        bentryStartAddr block blockstart s
                        /\ bentryEndAddr block blockend s
                        /\ In startaddr (getAllPaddrBlock blockstart blockend)
                        /\ (beqAddr blockstart startaddr && beqAddr blockend endaddr = false
                            \/ bentryPFlag block false s)))
				\/ (exists entry, lookup blockaddr s.(memory) beqAddr = Some (BE entry)
					/\ bentryPFlag blockaddr true s
					/\ (exists finalidx, (In blockaddr (filterOptionPaddr(getKSEntriesInStructAux (maxIdx+1)
																								currentkernelstructure
																								s
																								finalidx))
										/\ finalidx < kernelStructureEntriesNb))
          /\ exists blockstart blockend: paddr,
                  bentryStartAddr blockaddr blockstart s
                  /\ bentryEndAddr blockaddr blockend s
                  /\ beqAddr blockstart startaddr = true
                  /\ beqAddr blockend endaddr = true
))
}}.
Proof.
(* revert mandatory to generalize the induction hypothesis *)
revert currentidx currentkernelstructure startaddr endaddr.
induction n.
- (* n = 0 *)
	intros;simpl.
	{	(* MALInternal.getNullAddr *)
		eapply weaken. unfold MALInternal.getNullAddr.
		eapply WP.ret. intros. simpl. intuition. exfalso. destruct (i currentidx); lia.
	}
- (* n = S n*)
	intros.
	eapply bindRev.
	{ (** getBlockEntryAddrFromKernelStructureStart *)
		eapply weaken. apply getBlockEntryAddrFromKernelStructureStart.
		intros. split. apply H. unfold consistency1 in *.
		cbn. intuition.
	}
	intro entryaddr. (*simpl.*)
	eapply bindRev.
	{ (** MAL.readBlockPresentFromBlockEntryAddr *)
		eapply weaken. apply readBlockPresentFromBlockEntryAddr.
		intros. simpl. split. apply H. intuition.
	}
	intro ispresent.
	eapply bindRev.
	{ (** findBlockComp *)
		eapply weaken. apply findExactBlockComp.
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
      - subst entryaddr. destruct H2 as [blockstart [blockend (Hblockstart & Hblockend & Hbeqblocks)]].
        exists blockstart. exists blockend. apply andb_prop in Hbeqblocks. intuition.
      - right. apply andb_prop in H. destruct H. subst ispresent. subst matchcomp. unfold isBE in *.
        destruct (lookup entryaddr (memory s) beqAddr) eqn:HlookupEntry; try(exfalso; congruence).
        destruct v; try(exfalso; congruence). exists b. split. reflexivity. split. assumption. split.
        + exists currentidx. rewrite MaxIdxNextEq. simpl. unfold Paddr.addPaddrIdx. unfold CPaddr in H1.
          rewrite PeanoNat.Nat.add_0_r in H1.
          assert(HkernIdxIsValid: currentkernelstructure + currentidx <= maxAddr).
          {
            destruct (le_dec (currentkernelstructure + currentidx) maxAddr) eqn:HaddKernIdx; try(lia).
            exfalso. assert(HentryIsNull: entryaddr = nullAddr).
            {
              subst entryaddr. unfold nullAddr. unfold CPaddr. destruct (le_dec 0 maxAddr); try(lia).
              f_equal. apply proof_irrelevance.
            }
            assert(Hnull: nullAddrExists s) by (unfold consistency1 in *; intuition).
            unfold nullAddrExists in Hnull. unfold isPADDR in Hnull. rewrite HentryIsNull in *.
            rewrite HlookupEntry in Hnull. congruence.
          }
          destruct (le_dec (currentkernelstructure + currentidx) maxAddr) eqn:HaddKernIdx; try(lia).
          assert(Hentry: entryaddr =
                          {|
                             p := currentkernelstructure + currentidx;
                             Hp := StateLib.Paddr.addPaddrIdx_obligation_1 currentkernelstructure currentidx l
                          |}).
          {
            rewrite H1. unfold StateLib.Paddr.addPaddrIdx_obligation_1. unfold ADT.CPaddr_obligation_1.
            reflexivity.
          }
          rewrite <-Hentry in *. rewrite HlookupEntry. destruct (indexEq currentidx zero) eqn:HeqIdxZero.
          * split; try(assumption). simpl. left. reflexivity.
          * split; try(assumption). apply beqIdxFalse in HeqIdxZero. unfold zero in HeqIdxZero.
            unfold StateLib.Index.pred. assert(currentidx > 0).
            {
              unfold CIndex in HeqIdxZero. destruct (le_dec 0 maxIdx); try(lia).
              assert(0 <> currentidx).
              {
                intro Hcontra. contradict HeqIdxZero. destruct currentidx. simpl in Hcontra. subst i.
                f_equal. apply proof_irrelevance.
              }
              lia.
            }
            destruct (gt_dec currentidx 0); try(lia). simpl. left. reflexivity.
        + destruct H2 as [blockstart [blockend (Hstart & Hend & Hbounds)]]. exists blockstart. exists blockend.
          split. assumption. split. assumption. apply andb_prop in Hbounds. assumption.
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
			intros. simpl. split. apply H0.
      destruct H0 as (((((HPs & Hconsist & HkernIsKS & HidxIsKern & HcurridxBounded & HpropsOr) & Hentryaddr)
                      & HPFlag) & Hblock) & HmaxEntries).
			apply PeanoNat.Nat.lt_le_incl.
			rewrite KSEntriesNbLessThanMaxIdx in HidxIsKern. lia.
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
				fold findExactBlockInKSInStructAux.
				eapply weaken. eapply strengthen. eapply IHn.
				intros s blockOut Hprops. cbn -[kernelStructureEntriesNb] in *.
        destruct Hprops as (HPs & Hconsist & HpropsOr). intuition.
				intros s Hprops. cbn -[kernelStructureEntriesNb].
        destruct Hprops as (((((((HPs & Hconsist & HKS & HidxIsKern & HcurridxBounded & HpropsOr)
                            & Hentry & HBE) & HPFlag) & Hblock) & Hmax) & HnextidxIsSucc) & HnextidxLtMax).
				unfold StateLib.Index.ltb in HnextidxLtMax.
				apply eq_sym in HnextidxLtMax.
				apply PeanoNat.Nat.ltb_lt in HnextidxLtMax. rewrite Hmax in HnextidxLtMax.
        pose proof KSEntriesNbLessThanMaxIdx as HkernNb.
				unfold CIndex in HnextidxLtMax. destruct (le_dec kernelStructureEntriesNb maxIdx); try(exfalso; lia).
				simpl in HnextidxLtMax. split. assumption. split. assumption. split. assumption. split. assumption.
				unfold StateLib.Index.succ in HnextidxIsSucc.
        destruct (lt_dec currentidx maxIdx); try(exfalso; congruence).
        injection HnextidxIsSucc as HnextIsCurrPlusOne. rewrite <-HnextIsCurrPlusOne.
        cbn -[kernelStructureEntriesNb]. split. lia.
        destruct HpropsOr as [HcallRec | HfoundWrong]; try(right; assumption).
        destruct (PeanoNat.Nat.ltb (CIndex (kernelStructureEntriesNb - 1))
                                    (kernelStructureEntriesNb - (currentidx+1))) eqn:HltNbKernNleft.
        { (* CIndex (kernelStructureEntriesNb - 1) < kernelStructureEntriesNb - (currentidx+1) *)
          exfalso. apply PeanoNat.Nat.ltb_lt in HltNbKernNleft. unfold CIndex in HltNbKernNleft.
          destruct (le_dec (kernelStructureEntriesNb - 1) maxIdx); try(lia).
          cbn -[kernelStructureEntriesNb] in HltNbKernNleft. lia.
        }
        (* CIndex (kernelStructureEntriesNb - 1) >= n *)
        apply PeanoNat.Nat.ltb_ge in HltNbKernNleft.
        assert(HsuccRec: (kernelStructureEntriesNb - currentidx)
                          = S (kernelStructureEntriesNb - (currentidx + 1))) by lia.
        rewrite HsuccRec in HcallRec.
        assert(Hrec: filterOptionPaddr (getKSEntriesInStructAux (S (kernelStructureEntriesNb - (currentidx + 1)))
                                  currentkernelstructure s (CIndex (kernelStructureEntriesNb - 1)))
                      = filterOptionPaddr (getKSEntriesInStructAux (kernelStructureEntriesNb - (currentidx + 1))
                                  currentkernelstructure s (CIndex (kernelStructureEntriesNb - 1)) ++
                              getKSEntriesInStructAux 1 currentkernelstructure s
                                  (CIndex ((CIndex (kernelStructureEntriesNb - 1))
                                            - (kernelStructureEntriesNb - (currentidx + 1)))))).
        {
          assert(HkernelEntries: kernelEntriesAreValid s) by (unfold consistency1 in *; intuition).
          assert(Hnull: nullAddrExists s) by (unfold consistency1 in *; intuition).
          unfold nullAddrExists in Hnull.
          assert(HeqNull: {| p := 0; Hp := ADT.CPaddr_obligation_2 |} = nullAddr).
          {
            unfold nullAddr. unfold CPaddr. destruct (le_dec 0 maxAddr); try(lia). f_equal.
            apply proof_irrelevance.
          }
          apply getKSEntriesInStructAuxRec; try(lia).
          - assert(HtrivIdx: CIndex (kernelStructureEntriesNb - 1) <= CIndex (kernelStructureEntriesNb - 1))
                  by lia.
            specialize(HkernelEntries currentkernelstructure (CIndex (kernelStructureEntriesNb - 1)) HKS
                  HtrivIdx). unfold CPaddr in HkernelEntries.
            destruct (le_dec (currentkernelstructure + CIndex (kernelStructureEntriesNb - 1)) maxAddr);
                  try(lia). rewrite HeqNull in HkernelEntries. unfold isBE in HkernelEntries.
            unfold isPADDR in Hnull. destruct (lookup nullAddr (memory s) beqAddr); try(exfalso; congruence).
            destruct v; exfalso; congruence.
          - intros idx Hi HidxValid. specialize(HkernelEntries currentkernelstructure idx HKS HidxValid).
            unfold CPaddr in HkernelEntries.
            destruct (le_dec (currentkernelstructure + idx) maxAddr); try(lia).
            assert(HeqEntry:
                      {|
                        p := currentkernelstructure + idx;
                        Hp := ADT.CPaddr_obligation_1 (currentkernelstructure + idx) l1
                      |} = {| p := currentkernelstructure + idx; Hp := Hi |}).
            { f_equal. apply proof_irrelevance. }
            rewrite HeqEntry in HkernelEntries. assumption.
        }
        rewrite Hrec in HcallRec. rewrite filterOptionPaddrSplit in HcallRec.
        rewrite getAllPaddrAuxSplit in HcallRec. apply in_app_or in HcallRec.
        destruct HcallRec as [HcallRec | HstartInFirst]; try(left; assumption).
        assert(Hsimpl: CIndex (CIndex (kernelStructureEntriesNb - 1) - (kernelStructureEntriesNb -
                                                                        (currentidx + 1)))
                      = currentidx).
        {
          unfold CIndex. destruct (le_dec (kernelStructureEntriesNb - 1) maxIdx); try(lia).
          cbn -[kernelStructureEntriesNb].
          destruct (le_dec (kernelStructureEntriesNb - 1 - (kernelStructureEntriesNb - (currentidx + 1))) maxIdx);
              try(lia). destruct currentidx. cbn -[kernelStructureEntriesNb].
          assert(Heq: kernelStructureEntriesNb - 1 - (kernelStructureEntriesNb - (i + 1)) = i).
          {
            rewrite PeanoNat.Nat.sub_add_distr. apply PeanoNat.Nat.add_sub_eq_l.
            assert(i < kernelStructureEntriesNb) by intuition. lia.
          }
          assert(Hres: forall Hi1 Hi2, {| i := kernelStructureEntriesNb-1-(kernelStructureEntriesNb-(i+1));
                                          Hi := Hi1 |}
                                      = {| i := i; Hi := Hi2 |}).
          {
            rewrite Heq. intros. f_equal. apply proof_irrelevance.
          }
          apply Hres.
        }
        rewrite Hsimpl in HstartInFirst. simpl in HstartInFirst. unfold Paddr.addPaddrIdx in HstartInFirst.
        unfold CPaddr in Hentry. unfold blkoffset in Hentry. unfold CIndex in Hentry.
        destruct (le_dec 0 maxIdx); try(lia). simpl in Hentry. rewrite <-plus_n_O in Hentry.
        assert(currentkernelstructure + currentidx <= maxAddr).
        {
          destruct (le_dec (currentkernelstructure + currentidx) maxAddr); try(lia). exfalso.
          rewrite Hentry in HBE. assert(Hnull: nullAddrExists s) by (unfold consistency1 in *; intuition).
          unfold nullAddrExists in Hnull.
          assert(HeqNull: {| p := 0; Hp := ADT.CPaddr_obligation_2 |} = nullAddr).
          {
            unfold nullAddr. unfold CPaddr. destruct (le_dec 0 maxAddr); try(lia). f_equal.
            apply proof_irrelevance.
          }
          rewrite HeqNull in HBE. unfold isBE in HBE. unfold isPADDR in Hnull.
          destruct (lookup nullAddr (memory s) beqAddr); try(congruence). destruct v; congruence.
        }
        destruct (le_dec (currentkernelstructure + currentidx) maxAddr); try(lia).
        assert(Hentryaddr: forall Hi, entryaddr = {| p := currentkernelstructure + currentidx;
                                                     Hp := Hi |}).
        { rewrite Hentry. intro. f_equal. apply proof_irrelevance. }
        rewrite <-Hentryaddr in HstartInFirst. unfold isBE in HBE.
        destruct (lookup entryaddr (memory s) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence).
        assert(HstartInFirstBis: In startaddr (getAllPaddrAux [entryaddr] s)).
        {
          destruct (indexEq currentidx zero); try(intuition; congruence).
          destruct (StateLib.Index.pred currentidx); intuition.
        }
        simpl in HstartInFirstBis. destruct Hblock as [blockstart [blockend (Hstart & Hend & Hbounds)]].
        right. exists entryaddr. exists blockstart. exists blockend. unfold bentryStartAddr in *.
        unfold bentryEndAddr in *. unfold bentryPFlag in *.
        destruct (lookup entryaddr (memory s) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence). subst blockstart. subst blockend. split. reflexivity. split.
        reflexivity. split. rewrite app_nil_r in HstartInFirstBis. assumption. apply andb_false_iff in H.
        destruct H as [HnotPres | HnotBounds].
        - subst ispresent. right. assumption.
        - subst matchcomp. left. assumption.
			}
		* (* case_eq isnotlastidx = false *)
			intros.
			{ (** ret *)
				eapply weaken. apply ret.
				intros s Hprops. simpl. intuition. unfold StateLib.Index.ltb in H2. apply eq_sym in H2.
        apply PeanoNat.Nat.ltb_ge in H2. subst maxentriesnb. unfold StateLib.Index.succ in H4.
        destruct (lt_dec currentidx maxIdx); try(exfalso; congruence). injection H4 as Hnextidx.
        rewrite <-Hnextidx in H2. unfold CIndex in H2.
        assert(maxIdx > kernelStructureEntriesNb) by (apply maxIdxBiggerThanNbOfKernels).
        destruct (le_dec kernelStructureEntriesNb maxIdx); try(lia). simpl in H2.
        assert(Hcurr: kernelStructureEntriesNb -1 = currentidx) by lia.
        rewrite <-Hcurr in *. simpl in H13. change 7 with (kernelStructureEntriesNb - 1) in *.
        unfold Paddr.addPaddrIdx in H13. unfold CIndex in H13.
        destruct (le_dec (kernelStructureEntriesNb - 1) maxIdx); try(lia). cbn -[kernelStructureEntriesNb] in H13.
        unfold blkoffset in H3. rewrite <-plus_n_O in H3. unfold CPaddr in H3.
        destruct (le_dec (currentkernelstructure + (kernelStructureEntriesNb - 1)) maxAddr);
              try(intuition; congruence).
        assert(Hentryaddr: forall Hi, entryaddr = {| p := currentkernelstructure + (kernelStructureEntriesNb - 1);
                                                     Hp := Hi |}).
        { rewrite H3. intro. f_equal. apply proof_irrelevance. }
        rewrite <-Hentryaddr in H13. unfold isBE in H10.
        destruct (lookup entryaddr (memory s) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence).
        destruct (PeanoNat.Nat.eqb (kernelStructureEntriesNb - 1) 0) eqn:HkernelNbMOneNotZero.
        { apply beq_nat_true in HkernelNbMOneNotZero. exfalso. simpl in HkernelNbMOneNotZero. lia. }
        unfold StateLib.Index.pred in H13. apply beq_nat_false in HkernelNbMOneNotZero.
        cbn -[kernelStructureEntriesNb] in *. destruct (gt_dec (kernelStructureEntriesNb - 1) 0); try(lia).
        cbn in H13. left. split. reflexivity. destruct H6 as [blockstart [blockend (Hstart & Hend & Hbounds)]].
        exists entryaddr. exists blockstart. exists blockend. unfold bentryStartAddr in *.
        unfold bentryEndAddr in *. unfold bentryPFlag in *.
        destruct (lookup entryaddr (memory s) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence). subst blockstart. subst blockend. split. reflexivity. split.
        reflexivity. split. rewrite app_nil_r in H13. assumption. apply andb_false_iff in H.
        destruct H as [HnotPres | HnotBounds].
        - subst ispresent. right. assumption.
        - subst matchcomp. left. assumption.
			}
Qed.*)

(*TODO use noDupUsedPaddrList in a function above this one to get the NoDup prop*)
Lemma findExactBlockInKSAux n (currentkernelstructure idblock endblock kernel : paddr) (P : state -> Prop) :
{{  fun s : state => P s /\ consistency1 s
										/\ isKS currentkernelstructure s
                    /\ (exists kernList,
                         isKS kernel s
                         /\ isListOfKernelsAux kernList kernel s
                         /\ currentkernelstructure = last kernList kernel
                         /\ (forall kernListBis, isListOfKernelsAux kernListBis kernel s
                                                  -> length kernListBis < maxNbPrepare)
                         /\ (In idblock (getAllPaddrAux (filterPresent (filterOptionPaddr (getKSEntriesAux n
                                      currentkernelstructure s)) s) s)
                          \/ ((exists block blockstart blockend,
                                    bentryStartAddr block blockstart s
                                    /\ bentryEndAddr block blockend s
                                    /\ bentryPFlag block true s
                                    /\ In idblock (getAllPaddrBlock blockstart blockend)
                                    /\ In block (filterOptionPaddr (getKSEntriesAux maxNbPrepare
                                                  kernel s))
                                    /\ (beqAddr blockstart idblock && beqAddr blockend endblock = false
                                          (*\/ bentryPFlag block false s*)))
                              /\ ~In idblock (getAllPaddrAux (filterPresent (filterOptionPaddr (getKSEntriesAux
                                        n currentkernelstructure s)) s) s))))
                    /\ NoDup (getAllPaddrAux (filterPresent (filterOptionPaddr (getKSEntriesAux n
                                currentkernelstructure s)) s) s)
                    /\ (forall kernList, isListOfKernelsAux kernList kernel s -> NoDup (kernel::kernList))
}}
Internal.findExactBlockInKSAux n currentkernelstructure idblock endblock
{{fun (blockaddr : paddr) (s : state) => P s /\ consistency1 s /\
  exists kernList block blockstart blockend,
    bentryStartAddr block blockstart s
    /\ bentryEndAddr block blockend s
    /\ bentryPFlag block true s
    /\ isKS kernel s
    /\ isListOfKernelsAux kernList kernel s
    /\ currentkernelstructure = last kernList kernel
		/\ In block (filterOptionPaddr (getKSEntriesAux maxNbPrepare kernel s))
    /\ (blockaddr = nullAddr /\ In idblock (getAllPaddrBlock blockstart blockend)
        /\ (beqAddr blockstart idblock && beqAddr blockend endblock = false (*\/ bentryPFlag block false s*))
      \/ (block = blockaddr /\ beqAddr blockstart idblock = true /\ beqAddr blockend endblock = true ))
}}.
Proof.
(* revert mandatory to generalize the induction hypothesis *)
revert currentkernelstructure idblock endblock P. induction n.
- (* n = 0 *)
	intros. cbn -[maxNbPrepare].
	(* MALInternal.getNullAddr *)
	eapply weaken. unfold MALInternal.getNullAddr.
	eapply WP.ret. intros s Hprops. cbn -[maxNbPrepare]. destruct Hprops as (HPs & Hconsist & HKS & HpropsOr & _).
  destruct HpropsOr as [kernList (HkernIsKS & HkernList & HcurrIsLast & _ & HpropsOr)].
  destruct HpropsOr as [Hcontra | ([block [blockstart [blockend (Hstart & Hend & Hpresent & HaddrIn &
        HblockIn & Hproblem)]]] & _)]; try(exfalso; congruence). split. assumption.
  split. assumption. exists kernList. exists block. exists blockstart. exists blockend. split.
  assumption. split. assumption. split. assumption. split. assumption. split. assumption. split. assumption.
  split; try(left; intuition). assumption.
- (* n = S n*)
	unfold Internal.findExactBlockInKSAux.
	intros.
	eapply bindRev.
	{ (** MALInternal.Index.zero *)
		eapply weaken. apply Index.zero.
		intros. simpl. apply H.
	}
	intro zero.
	eapply bindRev.
	{ (** Internal.findBlockInKSInStructAux *)
		eapply weaken. apply findExactBlockInKSInStructAux.
		intros s Hprops. split. apply Hprops.
    destruct Hprops as ((HPs & Hconsist & HKS & HpropsOr & HnoDup & _) & Hzero).
    assert(HzeroIsNull: i zero = 0).
    {
      subst zero. unfold CIndex. destruct (le_dec 0 maxIdx); try(lia). simpl. reflexivity.
    }
    rewrite HzeroIsNull. rewrite PeanoNat.Nat.sub_0_r. split. assumption. split. assumption.
    assert(kernelStructureEntriesNb > 0) by (apply KSEntriesNbNotZero).
    assert(maxIdx > kernelStructureEntriesNb) by (apply maxIdxBiggerThanNbOfKernels). split. lia. split.
    unfold N. rewrite maxIdxEqualMaxAddr in *. lia.
    destruct HpropsOr as [kernList (HkernIsKS & HkernList & HcurrIsLast & HkernListsProp & HpropsOr)].
    destruct HpropsOr as [HcallRec | HblockFoundWrong] (*; try(left; right; destruct HblockFoundWrong as [block
            [blockstart [blockend HblockFoundWrong]]]; exists block; exists blockstart; exists blockend;
            intuition)*).
    { (*In idblock (getAllPaddrAux (filterOptionPaddr (getKSEntriesAux (S n) currentkernelstructure s)) s)*)
      assert(HeqLists: filterOptionPaddr (getKSEntriesInStructAux (maxIdx + 1) currentkernelstructure s
                              (CIndex (kernelStructureEntriesNb - 1)))
                        = filterOptionPaddr (getKSEntriesInStructAux kernelStructureEntriesNb
                             currentkernelstructure s (CIndex (kernelStructureEntriesNb - 1)))).
      {
        assert(HkernelEntries: kernelEntriesAreValid s) by (unfold consistency1 in *; intuition).
        assert(Hnull: nullAddrExists s) by (unfold consistency1 in *; intuition). unfold nullAddrExists in Hnull.
        assert(HeqNull: {| p := 0; Hp := ADT.CPaddr_obligation_2 |} = nullAddr).
        {
          unfold nullAddr. unfold CPaddr. destruct (le_dec 0 maxAddr); try(lia). f_equal. apply proof_irrelevance.
        }
        apply getKSEntriesInStructAuxEqFuelSuffGen.
        - assert(Htriv: CIndex (kernelStructureEntriesNb - 1) <= CIndex (kernelStructureEntriesNb - 1)) by lia.
          specialize(HkernelEntries currentkernelstructure (CIndex (kernelStructureEntriesNb - 1)) HKS Htriv).
          unfold CPaddr in HkernelEntries.
          destruct (le_dec (currentkernelstructure + CIndex (kernelStructureEntriesNb - 1)) maxAddr);
              try(assumption).
          rewrite HeqNull in HkernelEntries. exfalso. unfold isBE in HkernelEntries. unfold isPADDR in Hnull.
          destruct (lookup nullAddr (memory s) beqAddr); try(congruence). destruct v; congruence.
        - lia.
        - unfold CIndex. destruct (le_dec (kernelStructureEntriesNb - 1) maxIdx); try(lia).
          cbn -[kernelStructureEntriesNb]. lia.
        - intros idx Hi HidxValid. specialize(HkernelEntries currentkernelstructure idx HKS HidxValid).
          unfold CPaddr in HkernelEntries. destruct (le_dec (currentkernelstructure + idx) maxAddr);
              try(exfalso; congruence).
          assert(Heq: {|
                        p := currentkernelstructure + idx;
                        Hp := ADT.CPaddr_obligation_1 (currentkernelstructure + idx) l
                      |} = {| p := currentkernelstructure + idx; Hp := Hi |}).
          {
            f_equal. apply proof_irrelevance.
          }
          rewrite Heq in HkernelEntries. assumption.
      }
      rewrite <-HeqLists. set(Q := In idblock (getAllPaddrAux (filterPresent (filterOptionPaddr
                              (getKSEntriesInStructAux (maxIdx + 1) currentkernelstructure s (CIndex 
                                (kernelStructureEntriesNb - 1)))) s) s)).
      assert(Hor: Q \/ ~Q) by (apply Classical_Prop.classic).
      destruct Hor as [HQ | HnotQ].
      - left. left. assumption.
      - right. assumption.
    }
    { (*HblockFoundWrong*)
      destruct HblockFoundWrong as ([block [blockstart [blockend (Hstart & Hend & Hpresent & HaddrIn & HblockIn &
          Hbounds)]]] & HblockNotInRec). cbn -[kernelStructureEntriesNb] in HblockNotInRec. right.
      assert(HnextKernValid: nextKernelIsValid s) by (unfold consistency1 in *; intuition).
      specialize(HnextKernValid currentkernelstructure HKS).
      destruct HnextKernValid as (HnextValidAddr & [nextAddr (HlookupNextAddr & HnextAddr)]).
      unfold Paddr.addPaddrIdx in HblockNotInRec.
      destruct (le_dec (currentkernelstructure + nextoffset) maxAddr); try(lia).
      rewrite HlookupNextAddr in HblockNotInRec. destruct HnextAddr as [HnextIsKS | HnextIsNull].
      - unfold isKS in HnextIsKS. destruct (lookup nextAddr (memory s) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence). rewrite filterOptionPaddrSplit in HblockNotInRec.
        rewrite filterPresentSplit in HblockNotInRec.
        rewrite getAllPaddrAuxSplit in HblockNotInRec. apply Lib.in_app_or_neg in HblockNotInRec.
        destruct HblockNotInRec. assumption.
      - assert(Hnull: nullAddrExists s) by (unfold consistency1 in *; intuition). unfold nullAddrExists in Hnull.
        unfold isPADDR in Hnull. subst nextAddr.
        destruct (lookup nullAddr (memory s) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence).
        assert(HeqNull: nullAddr = {| p := 0; Hp := ADT.CPaddr_obligation_1 0 (PeanoNat.Nat.le_0_l maxAddr) |}).
        {
          unfold nullAddr. unfold CPaddr. destruct (le_dec 0 maxAddr); try(lia). f_equal.
          apply proof_irrelevance.
        }
        rewrite DTL.beqAddrTrue in HeqNull. rewrite HeqNull in HblockNotInRec. assumption.
    }
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
			intros s Hprops. cbn -[getKSEntriesAux]. destruct Hprops as ((((((HPs & Hconsist & HKS & HpropsOrPrev) & _)
          & _ & HpropsOrFound) & HbeqBlockNull) & HnextKern) & HbeqNextNull). split. assumption. split.
      assumption. rewrite <-DTL.beqAddrTrue in *. subst foundblock. subst nextkernelstructure.
      assert(Hnull: nullAddrExists s) by (unfold consistency1 in *; intuition). unfold nullAddrExists in Hnull.
      destruct HpropsOrFound as [HpropsOrFound | Hcontra]; try(destruct Hcontra as [entry (HlookupNull & _)];
          unfold isPADDR in Hnull; rewrite HlookupNull in Hnull; exfalso; congruence).
      destruct HpropsOrFound as (_ & HpropsOrFound).
      destruct HpropsOrPrev as (HpropsOrPrev & HnoDupRemains & HnoDupKernList).
      destruct HpropsOrPrev as [kernList (HkernIsKS & HkernList & HcurrIsLast & HkernListsProp &
              HpropsOrPrev)].
      destruct HpropsOrPrev as [HaddrInKernRec | HfoundWrong]; try(destruct HfoundWrong as ([block [blockstart
              [blockend HfoundWrong]]] & HidNotInRemains); exists kernList;
            exists block; exists blockstart; exists blockend; intuition).
      destruct HnextKern as [offset ((Hoffset & HnextAddr) & HnextKS)].
      assert(HnextKernValid: nextKernelIsValid s) by (unfold consistency1 in *; intuition).
      destruct HpropsOrFound as [HfoundWrong | HaddrNotInKern]; try(destruct HfoundWrong as [block [blockstart
              [blockend HfoundWrong]]]; exists kernList; exists block; exists blockstart;
            exists blockend).
      + assert(In block (filterOptionPaddr (getKSEntriesAux maxNbPrepare kernel s))).
        {
          apply blockInGetKSEntriesAuxIncl with currentkernelstructure kernList; try(assumption).
          unfold consistency1 in *; intuition. intuition.
        }
        intuition.
      + assert(HeqLists: forall m, filterOptionPaddr (getKSEntriesAux (S m) currentkernelstructure s)
                          = filterOptionPaddr (getKSEntriesInStructAux (maxIdx + 1) currentkernelstructure s
                               (CIndex (kernelStructureEntriesNb - 1)))).
        {
          intro. specialize(HnextKernValid currentkernelstructure HKS). destruct HnextKernValid as (HleNext &
              [nextAddr (HlookupNext & HnextType)]). cbn -[kernelStructureEntriesNb].
          unfold nextKSentry in HnextKS. subst offset. unfold Paddr.addPaddrIdx. unfold CPaddr in HnextKS.
          destruct (le_dec (currentkernelstructure + nextoffset) maxAddr); try(lia). rewrite HlookupNext.
          rewrite HlookupNext in HnextKS. subst nextAddr. unfold isPADDR in Hnull.
          destruct (lookup nullAddr (memory s) beqAddr); try(exfalso; congruence).
          destruct v; try(exfalso; congruence).
          assert(HeqNull: nullAddr = {| p := 0; Hp := ADT.CPaddr_obligation_1 0 (PeanoNat.Nat.le_0_l maxAddr) |}).
          {
            unfold nullAddr. unfold CPaddr. destruct (le_dec 0 maxAddr); try(lia). f_equal.
            apply proof_irrelevance.
          }
          rewrite DTL.beqAddrTrue in HeqNull. rewrite HeqNull. reflexivity.
        }
        rewrite HeqLists in HaddrInKernRec. exfalso; congruence.
		}
		* (* case_eq nextKSisnull = false *)
			intros.
			{ (** induction hypothesis *)
				fold findExactBlockInKSAux. eapply strengthen. eapply weaken.
				+ eapply IHn.
				+ intros s Hprops. cbn -[maxNbPrepare]. split. apply Hprops.
          destruct Hprops as ((((((HPs & Hconsist & HKS & HpropsOrPrev & HnoDupRemains & HnoDupKernlist) & _) & _
                & HpropsOrFound) & HbeqBlockNull) & HnextKern) & HbeqNextNull). split. assumption.
          assert(HKSCopy: isKS currentkernelstructure s) by assumption.
				  assert(isKS nextkernelstructure s).
				  {
					  apply isKSLookupEq in HKS. destruct HKS as [x (HKS&Hblockidx)].
					  destruct HnextKern as [offset ((Hoffset & HnextAddr) & HnextValue)].
					  assert(HnextKSIsKS : NextKSIsKS s) by (unfold consistency1 in * ; intuition).
					  unfold NextKSIsKS in *. subst offset.
					  rewrite <- beqAddrFalse in *.
					  apply HnextKSIsKS with 	(addr:=currentkernelstructure)
											  (nextKSaddr:=CPaddr (currentkernelstructure + nextoffset))
											  (nextKS:=nextkernelstructure) ;
					  intuition.
				  }
          split. assumption. destruct HpropsOrPrev as [kernList (HkernIsKS & HkernList & HcurrIsLast &
                  Hlength & HpropsOrPrev)].
          destruct HnextKern as [offset ((Hoffset & HnextAddr) & HnextKS)].
          assert(HnextKernValid: nextKernelIsValid s) by (unfold consistency1 in *; intuition).
          assert(HeqLists: filterOptionPaddr (getKSEntriesAux (S n) currentkernelstructure s) =
                              filterOptionPaddr (getKSEntriesInStructAux (maxIdx + 1) currentkernelstructure s
                                    (CIndex (kernelStructureEntriesNb - 1)))
                              ++ (filterOptionPaddr (getKSEntriesAux n nextkernelstructure s))).
          {
            specialize(HnextKernValid currentkernelstructure HKS). destruct HnextKernValid as (HleNext &
                [nextAddr (HlookupNext & HnextType)]). cbn -[kernelStructureEntriesNb].
            unfold nextKSentry in HnextKS. subst offset. unfold Paddr.addPaddrIdx. unfold CPaddr in HnextKS.
            destruct (le_dec (currentkernelstructure + nextoffset) maxAddr); try(lia). rewrite HlookupNext.
            rewrite HlookupNext in HnextKS. subst nextAddr. rewrite <-beqAddrFalse in HbeqNextNull.
            destruct HnextType as [HnextIsKS | Hcontra]; try(exfalso; congruence). unfold isKS in HnextIsKS.
            destruct (lookup nextkernelstructure (memory s) beqAddr); try(exfalso; congruence).
            destruct v; try(exfalso; congruence). rewrite filterOptionPaddrSplit. reflexivity.
          }
          rewrite HeqLists in HnoDupRemains. rewrite filterPresentSplit in HnoDupRemains.
          rewrite getAllPaddrAuxSplit in HnoDupRemains. apply Lib.NoDupSplitInclIff in HnoDupRemains.
          destruct HnoDupRemains as ((_ & HnoDupRemainsRec) & Hdisjoint). split; try(split; assumption).
          exists (kernList++[nextkernelstructure]). split. assumption. split.
          {
            rewrite <-beqAddrFalse in HbeqNextNull. apply not_eq_sym in HbeqNextNull.
            apply isListOfKernelsAuxRec with currentkernelstructure; try(assumption).
            - unfold nextKSentry in HnextKS. rewrite Hoffset in HnextKS.
              destruct (lookup (CPaddr (currentkernelstructure+nextoffset)) (memory s) beqAddr);
                  try(exfalso; congruence). destruct v; try(exfalso; congruence). subst p. reflexivity.
            - assert(HnextValid: nextKernelIsValid s) by (unfold consistency1 in *; intuition).
              specialize(HnextValid currentkernelstructure HKS). destruct HnextValid. assumption.
          }
          split. apply eq_sym. apply last_last. split. assumption. rewrite HeqLists in *.
          rewrite filterPresentSplit in HpropsOrPrev.
          assert(HnegImpl: forall l,
                    ~In idblock (getAllPaddrAux (l ++
                                filterPresent (filterOptionPaddr (getKSEntriesAux n nextkernelstructure s)) s) s)
                    -> ~In idblock (getAllPaddrAux (filterPresent (filterOptionPaddr (getKSEntriesAux n
                                      nextkernelstructure s)) s) s)).
          {
            intros l HidNotIn. rewrite getAllPaddrAuxSplit in HidNotIn. apply Lib.in_app_or_neg in HidNotIn.
            destruct HidNotIn. assumption.
          }
          rewrite <-DTL.beqAddrTrue in HbeqBlockNull. rewrite <-beqAddrFalse in HbeqNextNull. subst foundblock.
          assert(Hnull: nullAddrExists s) by (unfold consistency1 in *; intuition).
          unfold nullAddrExists in Hnull.
          destruct HpropsOrFound as [HpropsOrFound | Hcontra]; try(destruct Hcontra as [entry (HlookupNull & _)];
              unfold isPADDR in Hnull; rewrite HlookupNull in Hnull; exfalso; congruence).
          destruct HpropsOrFound as (_ & HpropsOrFound).
				  destruct HpropsOrPrev as [HaddrInKernRec | HfoundWrong]; try(right; destruct HfoundWrong as ([block
                [blockstart [blockend HfoundWrong]]] & HnotInRemains); split; try(apply HnegImpl with
                (filterPresent (filterOptionPaddr (getKSEntriesInStructAux (maxIdx + 1) currentkernelstructure s
                (CIndex (kernelStructureEntriesNb - 1)))) s); intuition); exists block; exists blockstart;
                exists blockend; intuition).
          rewrite getAllPaddrAuxSplit in HaddrInKernRec. apply in_app_or in HaddrInKernRec.
          destruct HpropsOrFound as [HfoundWrong | HaddrNotInKern].
          {
            right.
            destruct HfoundWrong as [block [blockstart [blockend (Hstart & Hend & Hpresent & HidIn & HblockIn &
                  Hbounds)]]].
            assert(HidInWithBlock: In idblock (getAllPaddrAux (filterPresent (filterOptionPaddr
                      (getKSEntriesInStructAux (maxIdx + 1) currentkernelstructure s (CIndex
                        (kernelStructureEntriesNb - 1)))) s) s)).
            {
              apply blockIsMappedAddrInPaddrList with block. unfold bentryPFlag in Hpresent.
              destruct (lookup block (memory s) beqAddr) eqn:HlookupBlock; try(exfalso; congruence).
              destruct v; try(exfalso; congruence). apply eq_sym in Hpresent.
              apply presentIsInFilterPresent with b; try(assumption). simpl. unfold bentryStartAddr in Hstart.
              unfold bentryEndAddr in Hend.
              destruct (lookup block (memory s) beqAddr); try(exfalso; congruence).
              destruct v; try(exfalso; congruence). rewrite app_nil_r. rewrite <-Hstart. rewrite <-Hend.
              assumption.
            }
            specialize(Hdisjoint idblock HidInWithBlock). split; try(assumption). exists block.
            exists blockstart. exists blockend. split. assumption. split. assumption. split. assumption.
            split. assumption. split; try(assumption).
            apply blockInGetKSEntriesAuxIncl with currentkernelstructure kernList;
                  try(assumption). unfold consistency1 in *; intuition.
          }
          destruct HaddrInKernRec as [Hcontra | HaddrInKernRec]; try(exfalso; congruence). left.
          assumption.
			  + intros s blockaddr Hprops. destruct Hprops as (((((((HPs & Hconsist & HKS & HpropsOrPrev) & _) & _ &
                HpropsOrFound) & HbeqBlockNull) & HnextKern) & HbeqNextNull) & _ & Hout). split. assumption.
          split. assumption. destruct Hout as [kernList [block [blockstart [blockend (Hstart & Hend & Hpresent &
              HkernelIsKS & HkernList & HnextIsLast & HblockIn & HpropsOr)]]]].
          destruct HpropsOrPrev as ([kernListBis (HkernBisIsKS & HkernListBis & HcurrIsLast &
                HpropsOrPrev)] & HnoDup & HnoDupKernList).
          exists kernListBis. exists block. exists blockstart. exists blockend. intuition.
          (*assert(HkernListsEq: kernList = kernListBis ++ [nextkernelstructure]).
          {
            destruct HnextKern as [offset ((Hoffset & HnextAddr) & HnextKS)]. subst offset.
            assert(HnextValid: nextKernelIsValid s) by (unfold consistency1 in *; intuition).
            specialize(HnextValid currentkernelstructure HKS). rewrite <-beqAddrFalse in HbeqNextNull.
            destruct HnextValid as (Hle & [nextAddr (HlookupNext & HnextType)]).
            apply kernListsEqNext with kernel s currentkernelstructure; try(assumption).
            apply not_eq_sym. assumption.
          }*)
		}
	+ (* case_eq foundblockisnull = false *)
		intros.
		{ (** ret *)
			eapply weaken. apply ret.
			intros s Hprops. cbn -[maxNbPrepare]. destruct Hprops as ((((HPs & Hconsist & HKS & HpropsOrPrev) & _) & _
            & HpropsOrFound) & HbeqBlockNull). rewrite <-beqAddrFalse in HbeqBlockNull.
      destruct HpropsOrFound as [Hcontra | Hfoundblock]; try(destruct Hcontra; exfalso; congruence).
      split. assumption. split. assumption. destruct Hfoundblock as [bentry (HlookupBlock & HPFlag & Hfinalidx &
            [blockstart [blockend (Hstart & Hend & HblockIn & HblockBounds)]])].
      destruct HpropsOrPrev as (HpropsOrPrev & HnoDupRemains & HnoDupKernList).
      destruct HpropsOrPrev as [kernList (HkernelIsKS & HkernList & HcurrIsLast & Hlength & HpropsOrPrev)].
      exists kernList. exists foundblock. exists blockstart. exists blockend.
      assert(In foundblock (filterOptionPaddr (getKSEntriesAux maxNbPrepare kernel s))).
      {
        apply InFilterPresentInList in HblockIn.
        apply blockInGetKSEntriesAuxIncl with currentkernelstructure kernList; try(assumption);
              unfold consistency1 in *; intuition.
      }
      intuition.
	}
Qed.

Lemma findExactBlockInKS (idPD blockEntryAddr blockEndAddr: paddr) (P : state -> Prop) :
{{ fun s => P s /\ consistency1 s /\ noDupUsedPaddrList s /\ isPDT idPD s
            /\ In blockEntryAddr (getAllPaddrAux (filterPresent (filterOptionPaddr (getKSEntries idPD s)) s) s)
}}
Internal.findExactBlockInKS idPD blockEntryAddr blockEndAddr
{{fun (blockaddr : paddr) (s : state) => P s /\ consistency1 s /\
      exists block blockstart blockend,
        bentryStartAddr block blockstart s
        /\ bentryEndAddr block blockend s
        /\ bentryPFlag block true s
		    /\ In block (getMappedBlocks idPD s)
        /\ (blockaddr = nullAddr /\ In blockEntryAddr (getAllPaddrBlock blockstart blockend)
            /\ (beqAddr blockstart blockEntryAddr && beqAddr blockend blockEndAddr = false
                (*\/ bentryPFlag block false s*))
          \/ (block = blockaddr /\ beqAddr blockstart blockEntryAddr = true
              /\ beqAddr blockend blockEndAddr = true /\ bentryPFlag block true s ))

			(*(blockaddr = nullAddr
			\/ (exists entry, lookup blockaddr s.(memory) beqAddr = Some (BE entry)
					/\ bentryPFlag blockaddr true s
          /\ exists blockstart blockend : paddr,
                bentryStartAddr blockaddr blockstart s
                /\ bentryEndAddr blockaddr blockend s
                /\ beqAddr blockstart blockEntryAddr = true
                /\ beqAddr blockend blockEndAddr = true))*)
}}.
Proof.
unfold Internal.findExactBlockInKS.
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
		intros s Hprops. simpl. intuition. rewrite <-DTL.beqAddrTrue in *. subst kernelstructurestart.
    unfold pdentryStructurePointer in *. unfold getKSEntries in *. exfalso.
    destruct (lookup idPD (memory s) beqAddr); try(congruence). destruct v; try(congruence).
    rewrite DTL.beqAddrTrue in H3. rewrite beqAddrSym in H3. rewrite H3 in *. simpl in *. congruence.
	}
+ (* case_eq kernelstructureisnull = false *)
	intro Hkernelstructureisnull.
	{ (** Internal.findExactBlockInKSAux *)
		eapply strengthen. eapply weaken.
		apply findExactBlockInKSAux.
		- intros s Hprops. cbn -[maxNbPrepare]. split. apply Hprops.
      destruct Hprops as (((_ & Hconsist & HnoDupUsed & HidIsPDT & HblockIn) & Hstruct) & HbeqNullKern).
      split. assumption. unfold pdentryStructurePointer in Hstruct. unfold getKSEntries in HblockIn.
      destruct (lookup idPD (memory s) beqAddr) eqn:HlookupPart; try(exfalso; congruence).
      destruct v; try(exfalso; congruence). rewrite beqAddrSym in HbeqNullKern. rewrite Hstruct in HbeqNullKern.
      rewrite HbeqNullKern in HblockIn. rewrite <-beqAddrFalse in HbeqNullKern.
      assert(HkernIsKS: StructurePointerIsKS s) by (unfold consistency1 in *; intuition).
      specialize(HkernIsKS idPD p HlookupPart HbeqNullKern). rewrite <-Hstruct in *. split. assumption.
      instantiate(1:= kernelstructurestart). split.
      + exists []. split. assumption. split. simpl. trivial. split. simpl. reflexivity.
        split; try(left; assumption).
        assert(HmaxNbPrep: maxNbPrepareIsMaxNbKernels s) by (unfold consistency1 in *; intuition).
        specialize(HmaxNbPrep idPD). intros kernList HkernList.
        assert(HkernListExt: isListOfKernels (kernelstructurestart::kernList) idPD s).
        { simpl. exists p. rewrite <-Hstruct. intuition. }
        specialize(HmaxNbPrep (kernelstructurestart::kernList) HkernListExt). simpl in HmaxNbPrep. lia.
      + split.
        * specialize(HnoDupUsed idPD HidIsPDT). unfold getUsedPaddr in HnoDupUsed.
          apply Lib.NoDupSplit in HnoDupUsed. destruct HnoDupUsed as (_ & HnoDupMapped).
          unfold getMappedPaddr in HnoDupMapped. unfold getMappedBlocks in HnoDupMapped.
          unfold getKSEntries in HnoDupMapped. rewrite HlookupPart in HnoDupMapped.
          rewrite <-Hstruct in HnoDupMapped. rewrite beqAddrFalse in HbeqNullKern.
          rewrite HbeqNullKern in HnoDupMapped. assumption.
        * assert(HnoDupKernlist: noDupListOfKerns s) by (unfold consistency1 in *; intuition).
          specialize(HnoDupKernlist idPD). intros kernList Hkernlist.
          assert(HkernListExt: isListOfKernels (kernelstructurestart::kernList) idPD s).
          { simpl. exists p. rewrite <-Hstruct. intuition. }
          specialize(HnoDupKernlist (kernelstructurestart::kernList) HkernListExt). assumption.

		- intros s blockaddr Hprops.
      destruct Hprops as ((((HP & _ & HnoDupUsed & HPDT & HblockIn) & Hstruct) & HbeqNullKern) & Hconsist &
            HblockFound). destruct HblockFound as [kernList [block [blockstart [blockend HblockFound]]]].
      split. assumption. split. assumption. exists block. exists blockstart. exists blockend.
      assert(In block (getMappedBlocks idPD s)).
      {
        unfold getMappedBlocks. unfold getKSEntries. unfold pdentryStructurePointer in Hstruct.
        destruct (lookup idPD (memory s) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence). rewrite <-Hstruct. rewrite beqAddrSym. rewrite HbeqNullKern.
        destruct HblockFound as (_ & _ & HPFlag & HblockFound). unfold bentryPFlag in HPFlag.
        destruct (lookup block (memory s) beqAddr) eqn:HlookupBlock; try(exfalso; congruence).
        destruct v; try(exfalso; congruence). apply presentIsInFilterPresent with b; intuition.
      }
      intuition.
      (*right. split. assumption. subst block. split. assumption. split; try(split; assumption).
      unfold getMappedBlocks. unfold bentryPFlag in *.
      destruct (lookup blockaddr (memory s) beqAddr) eqn:HlookupBlock; try(exfalso; congruence).
      destruct v; try(exfalso; congruence).
      apply presentIsInFilterPresent with b; try(assumption); try(apply eq_sym; assumption).
      unfold pdentryStructurePointer in Hstruct. unfold getKSEntries.
      destruct (lookup idPD (memory s) beqAddr) eqn:HlookupPart; try(exfalso; congruence).
      destruct v; try(exfalso; congruence). rewrite Hstruct in HbeqNullKern. rewrite beqAddrSym in HbeqNullKern.
      rewrite HbeqNullKern. rewrite <-Hstruct. assumption.*)
	}
Qed.