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

(** * Summary
    This file contains the invariant of [findBlock].
    We prove that this PIP service preserves the isolation property *)

Require Import Model.ADT Core.Services.
Require Import Proof.Isolation Proof.Hoare Proof.Consistency Proof.WeakestPreconditions
Proof.StateLib Proof.DependentTypeLemmas.
Require Import Invariants getGlobalIdPDCurrentOrChild findBlockInKSWithAddr.
Require Import Compare_dec Bool.

Require Import Model.Monad Model.MALInternal Model.Lib (* for visibility *).

Module WP := WeakestPreconditions.

Lemma mergeMemoryBlocks (idBlockToMerge1 idBlockToMerge2 : paddr) (MPURegionNb : index) :
{{fun s => partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s }}
Services.mergeMemoryBlocks idBlockToMerge1 idBlockToMerge2 MPURegionNb
{{fun _ s  => partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s }}.
Proof.
unfold Services.mergeMemoryBlocks.
eapply bindRev.
{ (** getCurPartition **)
	eapply weaken. apply getCurPartition.
	intros. simpl. split. apply H. intuition.
}
intro currentPart.
eapply bindRev.
{ (** Internal.findBlockInKSWithAddr *)
	eapply weaken. apply findBlockInKSWithAddr.findBlockInKSWithAddr.
	intros. simpl. split. apply H. intuition.
}
intro block1InCurrPartAddr.
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
		{ (** Internal.findBlockInKSWithAddr *)
			eapply weaken. apply findBlockInKSWithAddr.findBlockInKSWithAddr.
			intros. simpl. split. apply H0. intuition.
		}
		intro block2InCurrPartAddr.
		eapply bindRev.
		{ (** compareAddrToNull **)
			eapply weaken. apply Invariants.compareAddrToNull.
			intros. simpl. apply H0.
		}
		intro addrIsNull0.
		case_eq addrIsNull0.
		+ (* case_eq addrIsNull0 = true *)
				intros.
				{ (** ret *)
				eapply weaken. apply WP.ret.
				simpl. intros. intuition.
				}
		+ (* case_eq addrIsNull0 = false *)
				intros.
				eapply bindRev.
				{ (** MAL.readBlockAccessibleFromBlockEntryAddr *)
					eapply weaken. apply readBlockAccessibleFromBlockEntryAddr.
					intros. simpl. split. apply H1.
					repeat rewrite <- beqAddrFalse in *. intuition.
					apply isBELookupEq. destruct H6. exists x. intuition.
				}
				intro isBlock1Accessible.
				eapply bindRev.
				{ (** MAL.readBlockAccessibleFromBlockEntryAddr *)
					eapply weaken. apply readBlockAccessibleFromBlockEntryAddr.
					intros. simpl. split. apply H1.
					repeat rewrite <- beqAddrFalse in *. intuition.
					apply isBELookupEq. destruct H13. exists x. intuition.
				}
				intro isBlock2Accessible.
				case_eq (negb (isBlock1Accessible && isBlock2Accessible)).
				* (* case_eq (negb (isBlock1Accessible && isBlock2Accessible)) = true *)
						intros.
						{ (** ret *)
						eapply weaken. apply WP.ret.
						simpl. intros. intuition.
						}
				* (* case_eq (negb (isBlock1Accessible && isBlock2Accessible)) = false *)
						intros.
						eapply bindRev.
						{ (** MAL.readSh1PDChildFromBlockEntryAddr *)
							eapply weaken. apply readSh1PDChildFromBlockEntryAddr.
							intros. simpl. split. apply H2.
							repeat rewrite <- beqAddrFalse in *. intuition.
							destruct H9. exists x. intuition.
						}
						intro block1PDChildAddr.
						eapply bindRev.
						{ (** compareAddrToNull **)
							eapply weaken. apply Invariants.compareAddrToNull.
							intros. simpl. apply H2.
						}
						intro block1PDChildAddrIsNull.
						eapply bindRev.
						{ (** MAL.readSh1PDChildFromBlockEntryAddr *)
							eapply weaken. apply readSh1PDChildFromBlockEntryAddr.
							intros. simpl. split. apply H2.
							repeat rewrite <- beqAddrFalse in *. intuition.
							destruct H17. exists x. intuition.
						}
						intro block2GlobalIdPDChild.
						eapply bindRev.
						{ (** compareAddrToNull **)
							eapply weaken. apply Invariants.compareAddrToNull.
							intros. simpl. apply H2.
						}
						intro block2GlobalIdPDChildIsNull.
						case_eq ((negb block1PDChildAddrIsNull || negb block2GlobalIdPDChildIsNull)).
						-- (* case_eq ((negb block1PDChildAddrIsNull || negb block2GlobalIdPDChildIsNull)) = true *)
								intros.
								{ (** ret *)
								eapply weaken. apply WP.ret.
								simpl. intros. intuition.
								}
						-- (* case_eq ((negb block1PDChildAddrIsNull || negb block2GlobalIdPDChildIsNull)) = false *)
								intros.
								eapply bindRev.
								{ (** MAL.readSCNextFromBlockEntryAddr **)
									eapply weaken. apply readSCNextFromBlockEntryAddr.
									intros. simpl. split. apply H3.
									repeat rewrite <- beqAddrFalse in *. intuition.
									destruct H14. exists x. intuition.
								}
								intro block1Next.
								eapply bindRev.
								{ (** getBeqAddr **)
									eapply weaken. apply Invariants.getBeqAddr.
									intros. simpl. apply H3.
								}
								intro isBlock2Next.
								case_eq (negb isBlock2Next).
								++ (* case_eq (negb isBlock2Next) = true *)
										intros.
										{ (** ret *)
										eapply weaken. apply WP.ret.
										simpl. intros. intuition.
										}
								++ (* case_eq (negb isBlock2Next = false *)
										intros.
										eapply bindRev.
										{ (** MAL.readSCNextFromBlockEntryAddr **)
											eapply weaken. apply readSCNextFromBlockEntryAddr.
											intros. simpl. split. apply H4.
											repeat rewrite <- beqAddrFalse in *. intuition.
											destruct H23. exists x. intuition.
										}
										intro block2Next.


