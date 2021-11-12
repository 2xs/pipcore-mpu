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
    This file contains the invariant of [createPartition].
    We prove that this PIP service preserves the isolation property *)

Require Import Model.ADT Core.Services.
Require Import Proof.Isolation Proof.Hoare Proof.Consistency Proof.WeakestPreconditions
Proof.StateLib Proof.DependentTypeLemmas.
Require Import Invariants getGlobalIdPDCurrentOrChild sizeOfBlock.
Require Import Compare_dec.

Require Import Model.Monad Model.MALInternal Model.Lib (* for visibility *).

Module WP := WeakestPreconditions.

Lemma createPartition (idBlock: paddr) :
{{fun s => partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s }}
Services.createPartition idBlock
{{fun _ s  => partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s }}.
Proof.
unfold Services.createPartition.
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
intro blockInCurrentPartitionAddr.
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
		{ (** MAL.readBlockAccessibleFromBlockEntryAddr **)
			eapply weaken. apply readBlockAccessibleFromBlockEntryAddr.
			intros. simpl. split. apply H0.
			intuition.
			(* TODO: next two subgoals to factor and to use also in the next
					instructions *)
			- (* we know this case is impossible because we are in the branch
			where blockInCurrentPartitionAddr is not NULL *)
			apply beqAddrFalse in H2. congruence.
			- destruct H8. intuition. subst.
			unfold isBE. rewrite H8 ; trivial.
		}
		intro addrIsAccessible.
		case_eq (negb addrIsAccessible).
		+ (* case_eq negb addrIsAccessible = true *)
				intros.
				{ (** ret *)
				eapply weaken. apply WP.ret.
				simpl. intros. intuition.
				}
		+ (* case_eq negb addrIsAccessible = false *)
				intros.
				eapply bindRev.
				{ (** MAL.checkBlockInRAM **)
					eapply weaken. apply Invariants.checkBlockInRAM.
					intros. simpl. split. apply H1.
					intuition.
					- (* we know this case is impossible because we are in the branch
							where blockInCurrentPartitionAddr is not NULL *)
							apply beqAddrFalse in H4. congruence.
					- destruct H10. intuition. subst.
						unfold isBE. rewrite H10 ; trivial.
				}
				intro isInRAM.
				case_eq (negb isInRAM).
				* (* case_eq (negb isInRAM = true*)
					intros.
					{ (** ret *)
						intros. eapply WP.weaken. apply WP.ret.
						intros. simpl. intuition.
					}
				* (* case_eq (negb isInRAM = false *)
						intros.
						eapply bindRev.
						{ (** sizeOfBlock *)
							eapply weaken. apply sizeOfBlock.
							intros. simpl. split. apply H2.
							intuition.
							- (* we know this case is impossible because we are in the branch
								where blockInCurrentPartitionAddr is not NULL *)
								apply beqAddrFalse in H6. congruence.
							- destruct H12. intuition. subst.
								unfold isBE. rewrite H12 ; trivial.
						}
						intro blockSize.
						eapply bindRev.
						{ (** getMinBlockSize *)
							eapply weaken. apply Invariants.getMinBlockSize.
							intros. simpl. apply H2.
						}
						intro minBlockSize.
						eapply bindRev.
						{ (** ltb *)
							eapply weaken. apply Invariants.Index.ltb.
							intros. simpl. apply H2.
						}
						intro isBlockTooSmall1.
						case_eq isBlockTooSmall1.
						-- (* case_eq isBlockTooSmall1 = true*)
							intros.
							{ (** ret *)
								intros. eapply WP.weaken. apply WP.ret.
								intros. simpl. intuition.
							}
						-- (* case_eq isBlockTooSmall1 = false *)
							intros.
							eapply bindRev.
							{ (** getPDStructureTotalLength *)
								eapply weaken. apply Invariants.getPDStructureTotalLength.
								intros. simpl. apply H3.
							}
							intro PDStructureTotalLength.
							eapply bindRev.
							{ (** ltb *)
								eapply weaken. apply Invariants.Index.ltb.
								intros. simpl. apply H3.
							}
							intro isBlockTooSmall2.
							case_eq isBlockTooSmall2.
							++ (* case_eq isBlockTooSmall2 = true*)
								intros.
								{ (** ret *)
									intros. eapply WP.weaken. apply WP.ret.
									intros. simpl. intuition.
								}
							++ (* case_eq isBlockTooSmall2 = false *)
								intros.
								eapply bindRev.
								{ (** MAL.readSh1PDChildFromBlockEntryAddr *)
									eapply weaken. apply readSh1PDChildFromBlockEntryAddr.
									intros. simpl. split. apply H4.
									intuition.
									- (* we know this case is impossible because we are in the branch
										where blockInCurrentPartitionAddr is not NULL *)
										apply beqAddrFalse in H13. congruence.
									- destruct H19. exists x. intuition.
								}
								intro PDChildAddr.
								eapply bindRev.
								{ (** compareAddrToNull **)
									eapply weaken. apply Invariants.compareAddrToNull.
									intros. simpl. apply H4.
								}
								intro PDChildAddrIsNull.
								case_eq (negb PDChildAddrIsNull).
								** (* case_eq negb PDChildAddrIsNull = true *)
										intros.
										{ (** ret *)
										eapply weaken. apply WP.ret.
										simpl. intros. intuition.
										}
								** (* case_eq negb PDChildAddrIsNull = false *)
										intros.
										eapply bindRev.
										{ (** MAL.readBlockStartFromBlockEntryAddr *)
											eapply weaken. apply readBlockStartFromBlockEntryAddr.
											intros. simpl. split. apply H5.
											intuition.
											- (* we know this case is impossible because we are in the branch
												where blockInCurrentPartitionAddr is not NULL *)
												apply beqAddrFalse in H16. congruence.
											- destruct H22. intuition. subst.
												unfold isBE. rewrite H22 ; trivial.
										}
										intro newPDBlockStartAddr.
										eapply bindRev.
										{ (** MAL.readBlockEndFromBlockEntryAddr *)
											eapply weaken. apply readBlockEndFromBlockEntryAddr.
											intros. simpl. split. apply H5.
											intuition.
											- (* we know this case is impossible because we are in the branch
												where blockInCurrentPartitionAddr is not NULL *)
												apply beqAddrFalse in H17. congruence.
											- destruct H23. intuition. subst.
												unfold isBE. rewrite H23 ; trivial.
										}
										intro newPDBlockEndAddr.
Qed.
