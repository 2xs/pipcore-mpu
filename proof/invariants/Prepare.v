(*******************************************************************************)
(*  © Université de Lille, The Pip Development Team (2015-2023)                *)
(*  Copyright (C) 2020-2023 Orange                                             *)
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
    This file contains the invariant of [prepare].
    We prove that this PIP service preserves the isolation property *)
Require Import Model.ADT Core.Services.
Require Import Proof.Isolation Proof.Hoare Proof.Consistency Proof.WeakestPreconditions
Proof.StateLib Proof.DependentTypeLemmas.
Require Import Proof.invariants.Invariants getGlobalIdPDCurrentOrChild sizeOfBlock.
Require Import Compare_dec Bool.

Require Import Model.Monad Model.MALInternal Model.Lib (* for visibility *).

Module WP := WeakestPreconditions.

Lemma prepare (idPD : paddr)
							(projectedSlotsNb : index)
							(idRequisitionedBlock : paddr) :
{{fun s => partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s }}
Services.prepare idPD projectedSlotsNb idRequisitionedBlock
{{fun _ s  => partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s }}.
Proof.
unfold Services.prepare.
eapply bindRev.
{ (** getCurPartition **)
	eapply weaken. apply getCurPartition.
	intros. simpl. split. apply H. intuition.
}
intro currentPart.
{ (** Internal.getGlobalIdPDCurrentOrChild **)
	eapply weaken. apply getGlobalIdPDCurrentOrChild.
	intros. simpl. split. apply H. intuition.
	subst currentPart.
	apply currentPartIsPDT ;
	unfold consistency in * ; unfold consistency1 in * ;
	intuition.
}
intro globalIdPD.
eapply bindRev.
{ (** compareAddrToNull **)
	eapply weaken. apply Invariants.compareAddrToNull.
	intros. simpl. apply H.
}
intro addrIsNull.
case_eq addrIsNull.
- (* case_eq addrIsNull = true *)
	intros.
	{ (** ret *)
	eapply weaken. apply WP.ret.
  simpl. intros. intuition.
	}
- (* case_eq addrIsNull = false *)
	intros.
	eapply bindRev.
	{ (** MAL.readPDNbPrepare *)
		eapply weaken. apply readPDNbPrepare.
		intros. simpl. split. apply H0. intuition.
		apply H5. intros. apply beqAddrFalse in H2. congruence.
	}
	intro nbPrepare.
	eapply bindRev.
	{ (** MALInternal.getMaxNbPrepare *)
		eapply weaken. apply Invariants.getMaxNbPrepare.
		intros. simpl. apply H0.
	}
	intro maxnbprepare.
	eapply bindRev.
	{ (** leb *)
		eapply weaken. apply Invariants.Index.leb.
		intros. simpl. apply H0.
	}
	intro isMaxPrepare.
	case_eq isMaxPrepare.
	+ (* case_eq isMaxPrepare = true*)
		intros.
		{ (** ret *)
			intros. eapply WP.weaken. apply WP.ret.
			intros. simpl. intuition.
		}
	+ (* case_eq isMaxPrepare = false *)
		intros.
		eapply bindRev.
		{ (** MAL.readPDNbFreeSlots *)
			eapply weaken. apply readPDNbFreeSlots.
			intros. simpl. split. apply H1. intuition.
			apply H8. intros.
			(* globallIdPD is false, since we are in the branch addrIsNull = false *)
			apply beqAddrFalse in H5. congruence.
		}
		intro currentFreeSlotsNb.
		eapply bindRev.
		{ (** leb *)
			eapply weaken. apply Invariants.Index.leb.
			intros. simpl. apply H1.
		}
		intro isEnoughFreeSlots.
		eapply bindRev.
		{ (** MALInternal.Index.zero *)
			eapply weaken. apply Invariants.Index.zero.
			intros. simpl. apply H1.
		}
		intro zero.
		eapply bindRev.
		{ (** ltb *)
			eapply weaken. apply Invariants.Index.ltb.
			intros. simpl. apply H1.
		}
		intro isForcedPrepare.
		case_eq (isEnoughFreeSlots && negb isForcedPrepare).
		* (* case_eq isEnoughFreeSlots && negb isForcedPrepare = true*)
			intros.
			{ (** ret *)
				intros. eapply WP.weaken. apply WP.ret.
				intros. simpl. intuition.
			}
		* (* case_eq isEnoughFreeSlots && negb isForcedPrepare = false *)
			intros.
			eapply bindRev.
			{ (** getKernelStructureEntriesNb *)
				eapply weaken. apply Invariants.getKernelStructureEntriesNb.
				intros. simpl. apply H2.
			}
			intro kernelentriesnb.
			eapply bindRev.
			{ (** ltb *)
				eapply weaken. apply Invariants.Index.ltb.
				intros. simpl. apply H2.
			}
			intro isOutsideBound.
			case_eq (negb isForcedPrepare && isOutsideBound).
			-- (* case_eq (negb isForcedPrepare && isOutsideBound) = true*)
				intros.
				{ (** ret *)
					intros. eapply WP.weaken. apply WP.ret.
					intros. simpl. intuition.
				}
			-- (* case_eq (negb isForcedPrepare && isOutsideBound) = false *)
				intros.
				eapply bindRev.
				{ (** Internal.findBlockInKSWithAddr *)
					eapply weaken. apply findBlockInKSWithAddr.findBlockInKSWithAddr.
					intros. simpl. split. apply H3. intuition.
				}
				intro requisitionedBlockInCurrPartAddr.
				eapply bindRev.
				{ (** compareAddrToNull **)
					eapply weaken. apply Invariants.compareAddrToNull.
					intros. simpl. apply H3.
				}
				intro addrIsNull0.
				case_eq addrIsNull0.
				++ (* case_eq addrIsNull0 = true *)
						intros.
						{ (** ret *)
						eapply weaken. apply WP.ret.
						simpl. intros. intuition.
						}
				++ (* case_eq addrIsNull0 = false *)
						intros.
						eapply bindRev.
						{ (** MAL.checkBlockInRAM **)
							eapply weaken. apply Invariants.checkBlockInRAM.
							intros. simpl. split. apply H4. intuition.
							(* TODO: next two subgoals to factor and to use also in the next
												instructions *)
							- (* we know this case is impossible because we are in the branch
									where requisitionedBlockInCurrPartAddr is not NULL *)
									apply beqAddrFalse in H6. congruence.
							- destruct H23. intuition. subst.
								unfold isBE. rewrite H23 ; trivial.
						}
						intro isInRAM.
						case_eq (negb isInRAM).
						** (* case_eq (negb isInRAM = true*)
							intros.
							{ (** ret *)
								intros. eapply WP.weaken. apply WP.ret.
								intros. simpl. intuition.
							}
						** (* case_eq (negb isInRAM = false *)
								intros.
								eapply bindRev.
								{ (** sizeOfBlock *)
									eapply weaken. apply sizeOfBlock.
									intros. simpl. split. apply H5. intuition.
									- (* we know this case is impossible because we are in the branch
										where requisitionedBlockInCurrPartAddr is not NULL *)
										apply beqAddrFalse in H8. congruence.
									- destruct H25. intuition. subst.
								unfold isBE. rewrite H25 ; trivial.
								}
								intro blockSize.
								eapply bindRev.
								{ (** getKernelStructureTotalLength *)
									eapply weaken. apply Invariants.getKernelStructureTotalLength.
									intros. simpl. apply H5.
								}
								intro kStructureTotalLength.
								eapply bindRev.
								{ (** Index.ltb *)
									eapply weaken. apply Invariants.Index.ltb.
									intros. simpl. apply H5.
								}
								intro isBlockTooSmall.
								case_eq isBlockTooSmall.
								--- (* case_eq isBlockTooSmall = true *)
										intros.
										{ (** ret *)
										eapply weaken. apply WP.ret.
										simpl. intros. intuition.
										}
								--- (* case_eq isBlockTooSmall = false *)
										intros.
										eapply bindRev.
										{ (** MAL.readBlockAccessibleFromBlockEntryAddr *)
											eapply weaken. apply readBlockAccessibleFromBlockEntryAddr.
											intros. simpl. split. apply H6. intuition.
											- (* we know this case is impossible because we are in the branch
												where requisitionedBlockInCurrPartAddr is not NULL *)
											apply beqAddrFalse in H12. congruence.
											- destruct H29. intuition. subst.
										unfold isBE. rewrite H29 ; trivial.
										}
										intro addrIsAccessible.
										case_eq (negb addrIsAccessible).
										+++ (* case_eq negb addrIsAccessible = true *)
												intros.
												{ (** ret *)
												eapply weaken. apply WP.ret.
												simpl. intros. intuition.
												}
										+++ (* case_eq negb addrIsAccessible = false *)
												intros.
												eapply bindRev.
												{ (** MAL.readBlockPresentFromBlockEntryAddr *)
													eapply weaken. apply readBlockPresentFromBlockEntryAddr.
													intros. simpl. split. apply H7. intuition.
													- (* we know this case is impossible because we are in the branch
														where requisitionedBlockInCurrPartAddr is not NULL *)
														apply beqAddrFalse in H14. congruence.
													- destruct H31. intuition. subst.
														unfold isBE. rewrite H31 ; trivial.
												}
												intro addrIsPresent.
												case_eq (negb addrIsPresent).
												*** (* case_eq negb addrIsPresent = true *)
														intros.
														{ (** ret *)
														eapply weaken. apply WP.ret.
														simpl. intros. intuition.
														}
												*** (* case_eq negb addrIsPresent = false *)
														intros.
														eapply bindRev.
														{ (** MAL.readBlockStartFromBlockEntryAddr *)
															eapply weaken. apply readBlockStartFromBlockEntryAddr.
															intros. simpl. split. apply H8. intuition.
															- (* we know this case is impossible because we are in the branch
																where requisitionedBlockInCurrPartAddr is not NULL *)
																apply beqAddrFalse in H16. congruence.
															- destruct H33. intuition. subst.
																unfold isBE. rewrite H33 ; trivial.
														}
														intro requisitionedBlockStart.
														eapply bindRev.
														{ (** MAL.readBlockEndFromBlockEntryAddr *)
															eapply weaken. apply readBlockEndFromBlockEntryAddr.
															intros. simpl. split. apply H8. intuition.
															- (* we know this case is impossible because we are in the branch
																where requisitionedBlockInCurrPartAddr is not NULL *)
																apply beqAddrFalse in H17. congruence.
															- destruct H34. intuition. subst.
														unfold isBE. rewrite H34 ; trivial.
														}
														intro requisitionedBlockEnd.
