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
    This file contains required lemmas to help in proving some properties
    on our dependent types defined into [Model.ADT] *)
Require Import Model.ADT Model.MALInternal Model.Lib Model.Monad.

Require Import Proof.StateLib Proof.Consistency.

Require Import Coq.Logic.ProofIrrelevance Arith Lia Bool List.
Import List.ListNotations.

(** ** This file has not been cleaned up from Pip (MMU) legacy in case
      some left over lemmas could be adapted **)

(* DUP *)
Lemma isPDTLookupEq (pd : paddr) s :
isPDT pd s -> exists entry : PDTable,
  lookup pd (memory s) beqAddr = Some (PDT entry).
Proof.
intros.
unfold isPDT in H.
destruct (lookup pd (memory s) beqAddr); try now contradict H.
destruct v; try now contradict H.
eexists;repeat split;trivial.
Qed.

(* DUP *)
Lemma isBELookupEq (blockentryaddr : paddr) s :
isBE blockentryaddr s <-> exists entry : BlockEntry,
  lookup blockentryaddr (memory s) beqAddr = Some (BE entry).
Proof.
intros. split.
- intros.
unfold isBE in H.
destruct (lookup blockentryaddr (memory s) beqAddr); try now contradict H.
destruct v; try now contradict H.
eexists;repeat split;trivial.
- intros. unfold isBE. destruct H. rewrite H ; trivial.
Qed.

(* DUP *)
Lemma isSHELookupEq (sh1entryaddr : paddr) s :
isSHE sh1entryaddr s <-> exists entry : Sh1Entry,
  lookup sh1entryaddr (memory s) beqAddr = Some (SHE entry).
Proof.
intros. split.
- intros. unfold isSHE in H.
	destruct (lookup sh1entryaddr (memory s) beqAddr); try now contradict H.
	destruct v; try now contradict H.
	eexists;repeat split;trivial.
- intros. unfold isSHE. destruct H. rewrite H ; trivial.
Qed.

(* DUP *)
Lemma isSCELookupEq (scentryaddr : paddr) s :
isSCE scentryaddr s <-> exists entry : SCEntry,
  lookup scentryaddr (memory s) beqAddr = Some (SCE entry).
Proof.
intros. split.
- intros. unfold isSCE in H.
destruct (lookup scentryaddr (memory s) beqAddr); try now contradict H.
destruct v; try now contradict H.
eexists;repeat split;trivial.
- intros. unfold isSCE. destruct H. rewrite H ; trivial.
Qed.

(* DUP *)
Lemma isKSLookupEq (addr : paddr) s :
isKS addr s -> exists entry : BlockEntry,
  lookup addr (memory s) beqAddr = Some (BE entry)
	/\ entry.(blockindex) = zero.
Proof.
intros.
unfold isKS in H.
destruct (lookup addr (memory s) beqAddr); try now contradict H.
destruct v; try now contradict H.
eexists;repeat split;trivial.
Qed.

(* DUP *)
Lemma isPADDRLookupEq (addr : paddr) s :
isPADDR addr s -> exists addr' : paddr,
  lookup addr (memory s) beqAddr = Some (PADDR addr').
Proof.
intros.
unfold isPADDR in H.
destruct (lookup addr (memory s) beqAddr); try now contradict H.
destruct v; try now contradict H.
eexists;repeat split;trivial.
Qed.

(* DUP*)
Lemma lookupBEntryAccessibleFlag entryaddr s :
forall entry , lookup entryaddr (memory s) beqAddr = Some (BE entry) ->
bentryAFlag entryaddr (accessible entry) s.
Proof.
intros.
unfold bentryAFlag.
rewrite H;trivial.
Qed.

(* DUP*)
Lemma lookupBEntryPresentFlag entryaddr s :
forall entry , lookup entryaddr (memory s) beqAddr = Some (BE entry) ->
bentryPFlag entryaddr (present entry) s.
Proof.
intros.
unfold bentryPFlag.
rewrite H;trivial.
Qed.

(* DUP*)
Lemma lookupBEntryReadFlag entryaddr s :
forall entry , lookup entryaddr (memory s) beqAddr = Some (BE entry) ->
bentryRFlag entryaddr (read entry) s.
Proof.
intros.
unfold bentryRFlag.
rewrite H;trivial.
Qed.

(* DUP*)
Lemma lookupBEntryWriteFlag entryaddr s :
forall entry , lookup entryaddr (memory s) beqAddr = Some (BE entry) ->
bentryWFlag entryaddr (write entry) s.
Proof.
intros.
unfold bentryWFlag.
rewrite H;trivial.
Qed.

(* DUP *)
Lemma lookupBEntryExecFlag entryaddr s :
forall entry , lookup entryaddr (memory s) beqAddr = Some (BE entry) ->
bentryXFlag entryaddr (exec entry) s.
Proof.
intros.
unfold bentryXFlag.
rewrite H;trivial.
Qed.

Lemma lookupBEntryBlockIndex entryaddr s :
forall entry , lookup entryaddr (memory s) beqAddr = Some (BE entry) ->
bentryBlockIndex entryaddr (blockindex entry) s.
Proof.
intros.
unfold bentryBlockIndex.
rewrite H;trivial.
Qed.

(*DUP*)
Lemma lookupBEntryStartAddr entryaddr s :
forall entry , lookup entryaddr (memory s) beqAddr = Some (BE entry) ->
bentryStartAddr entryaddr (startAddr (blockrange entry)) s.
Proof.
intros.
unfold bentryStartAddr.
rewrite H;trivial.
Qed.

(*DUP*)
Lemma lookupBEntryEndAddr entryaddr s :
forall entry , lookup entryaddr (memory s) beqAddr = Some (BE entry) ->
bentryEndAddr entryaddr (endAddr (blockrange entry)) s.
Proof.
intros.
unfold bentryEndAddr.
rewrite H;trivial.
Qed.

(* DUP *)
Lemma lookupSh1EntryPDflag paddr s :
forall entry , lookup paddr (memory s) beqAddr = Some (SHE entry) ->
sh1entryPDflag paddr (PDflag entry) s.
Proof.
intros.
unfold sh1entryPDflag.
rewrite H;trivial.
Qed.

Lemma lookupSh1EntryPDchild paddr s :
forall entry , lookup paddr (memory s) beqAddr = Some (SHE entry) ->
sh1entryPDchild paddr (PDchild entry) s.
Proof.
intros.
unfold sh1entryPDchild.
rewrite H;trivial.
Qed.

Lemma lookupSh1EntryInChildLocation paddr s :
forall entry , lookup paddr (memory s) beqAddr = Some (SHE entry) ->
consistency s ->
sh1entryInChildLocation paddr (inChildLocation entry) s.
Proof.
intros.
unfold sh1entryInChildLocation.
rewrite H;trivial.
intuition.
unfold consistency in *.
unfold consistency1 in *.
unfold sh1InChildLocationIsBE in *. intuition.
eauto. (* specialize (H10 paddr entry H H1). trivial. *)
Qed.

Lemma lookupSCEntryOrigin paddr s :
forall entry , lookup paddr (memory s) beqAddr = Some (SCE entry) ->
scentryOrigin paddr (origin entry) s.
Proof.
intros.
unfold scentryOrigin.
rewrite H;trivial.
Qed.

Lemma lookupSCEntryNext paddr s :
forall entry , lookup paddr (memory s) beqAddr = Some (SCE entry) ->
scentryNext paddr (next entry) s.
Proof.
intros.
unfold scentryNext.
rewrite H;trivial.
Qed.

(*DUP*)
Lemma lookupPDEntryFirstFreeSlot entryaddr s :
forall entry , lookup entryaddr (memory s) beqAddr = Some (PDT entry) ->
pdentryFirstFreeSlot entryaddr (firstfreeslot entry) s.
Proof.
intros.
unfold pdentryFirstFreeSlot.
rewrite H;trivial.
Qed.


(*DUP*)
Lemma lookupPDEntryNbFreeSlots entryaddr s :
forall entry , lookup entryaddr (memory s) beqAddr = Some (PDT entry) ->
pdentryNbFreeSlots entryaddr (nbfreeslots entry) s.
Proof.
intros.
unfold pdentryNbFreeSlots.
rewrite H;trivial.
Qed.

(*DUP*)
Lemma lookupPDEntryStructurePointer entryaddr s :
forall entry , lookup entryaddr (memory s) beqAddr = Some (PDT entry) ->
(*consistency s ->*)
pdentryStructurePointer entryaddr (structure entry) s.
Proof.
intros.
unfold pdentryStructurePointer.
rewrite H;trivial.
(*intuition.
unfold consistency in *. unfold StructurePointerIsBE in *. intuition.
specialize (H11 entryaddr entry H). trivial.*)
Qed.

(*DUP*)
Lemma lookupPDEntryNbPrepare entryaddr s :
forall entry , lookup entryaddr (memory s) beqAddr = Some (PDT entry) ->
pdentryNbPrepare entryaddr (nbprepare entry) s.
Proof.
intros.
unfold pdentryNbPrepare.
rewrite H;trivial.
Qed.

(*DUP*)
Lemma lookupPDEntryMPU entryaddr s :
forall entry , lookup entryaddr (memory s) beqAddr = Some (PDT entry) ->
pdentryMPU entryaddr (MPU entry) s.
Proof.
intros.
unfold pdentryMPU.
rewrite H;trivial.
Qed.

(*DUP*)
Lemma lookupPDEntryVidt entryaddr s :
forall entry , lookup entryaddr (memory s) beqAddr = Some (PDT entry) ->
pdentryVidt entryaddr (vidtAddr entry) s.
Proof.
intros.
unfold pdentryVidt.
rewrite H;trivial.
Qed.

(* DUP*)
Lemma lookupSh1EntryAddr entryaddr s :
forall entry , lookup entryaddr (memory s) beqAddr = Some (BE entry) ->
sh1entryAddr entryaddr (CPaddr (entryaddr + sh1offset)) s.
Proof.
intros.
unfold sh1entryAddr.
rewrite H;trivial.
Qed.


(* DUP*)
Lemma lookupSCEntryAddr entryaddr s :
forall entry , lookup entryaddr (memory s) beqAddr = Some (BE entry) ->
scentryAddr entryaddr (CPaddr (entryaddr + scoffset)) s.
Proof.
intros.
unfold scentryAddr.
rewrite H;trivial.
Qed.

(*DUP*)
Lemma lookupPDMPU entryaddr s :
forall entry , lookup entryaddr (memory s) beqAddr = Some (PDT entry) ->
pdentryMPU entryaddr (MPU entry) s.
Proof.
intros.
unfold pdentryMPU.
rewrite H;trivial.
Qed.

(*
(** ADT : level **)
Lemma levelEqBEqNatTrue :
forall l l' : level, StateLib.Level.eqb l l' = true -> l = l' .
 Proof.
 intros l l' H.
 unfold StateLib.Level.eqb in H.
 apply beq_nat_true in H.
 destruct l.
 destruct l'. simpl in *.
 subst.
 assert (Hl = Hl0).
 apply proof_irrelevance. subst. intuition.
Qed.

Lemma levelEqBEqNatFalse :
forall l ,
StateLib.Level.eqb l fstLevel = false -> l > fstLevel.
Proof.
intros.
unfold StateLib.Level.eqb in H.
apply beq_nat_false in H.
unfold fstLevel in *.
unfold CLevel in *.
case_eq (lt_dec 0 nbLevel).
intros.
rewrite H0 in *.
simpl in *. lia.
intros.
assert (0 < nbLevel).
apply nbLevelNotZero.
contradict H1.
intuition.
Qed.

Lemma levelEqBEqNatFalse0 :
forall l ,
StateLib.Level.eqb l fstLevel = false -> l > 0.
Proof.
intros.
unfold StateLib.Level.eqb in H.
apply beq_nat_false in H.
unfold fstLevel in H.
unfold CLevel in H.
case_eq (lt_dec 0 nbLevel).
intros.
rewrite H0 in H.
simpl in *. lia.
intros.
assert (0 < nbLevel).
apply nbLevelNotZero.
contradict H1.
intuition.
Qed.

Lemma levelEqBEqNatTrue0 :
forall l ,
StateLib.Level.eqb l fstLevel = true -> l <= 0.
Proof.
intros.
unfold StateLib.Level.eqb in H.
apply beq_nat_true in H.
unfold fstLevel in H.
unfold CLevel in H.
case_eq (lt_dec 0 nbLevel).
intros.
rewrite H0 in H.
simpl in *. lia.
intros.
assert (0 < nbLevel).
apply nbLevelNotZero.
contradict H1.
intuition.
Qed.

Lemma levelPredNone nbL:
StateLib.Level.eqb nbL fstLevel = false ->
StateLib.Level.pred nbL <> None.
Proof.
intros.
unfold Level.pred.
case_eq(gt_dec nbL 0); intros.
unfold not; intros.
inversion H1.
apply levelEqBEqNatFalse0 in H.
lia.
Qed.

Lemma levelPredLt nbL l :
StateLib.Level.eqb nbL fstLevel = false ->
StateLib.Level.pred nbL = Some l ->
l < nbL.
Proof.
intros.
unfold Level.pred in *.
case_eq(gt_dec nbL 0); intros.
rewrite H1 in *.
inversion H0.
simpl in *.
lia.
apply levelEqBEqNatFalse0 in H.
lia.
Qed.

Lemma CLevel0_r :  forall l : level,l - CLevel 0 = l.
Proof.
unfold CLevel.
case_eq (lt_dec 0 nbLevel).
intros.
simpl. lia.
intros.
assert (0 < nbLevel).
apply nbLevelNotZero. lia.
Qed.

Lemma CLevelIdentity : forall l : level, CLevel (l - CLevel 0) = l.
Proof.
intros l.
rewrite CLevel0_r. destruct l.
simpl.
unfold CLevel.
case_eq(lt_dec l nbLevel).
intros. simpl.
assert ( Hl = ADT.CLevel_obligation_1 l l0).
apply proof_irrelevance.
subst. reflexivity.
intros.
contradict H.
lia.
Qed.

Lemma CLevelIdentity1 : forall l : level, CLevel l  = l.
Proof.
intros l.
unfold CLevel.
case_eq(lt_dec l nbLevel).
intros. simpl.
destruct l.
simpl.
f_equal.
apply proof_irrelevance.
subst.
intros.
destruct l.
simpl in *.
lia.
Qed.

Lemma CLevelIdentityLe :
forall a , a < nbLevel ->  a <= CLevel a.
Proof.
intros.
unfold CLevel.
case_eq (lt_dec a nbLevel); intros.
simpl; lia.
now contradict H.
Qed.

Lemma levelPredMinus1: forall l l' , StateLib.Level.eqb l fstLevel = false -> StateLib.Level.pred l = Some l' -> l' = CLevel (l - 1).
Proof.
intros.
unfold StateLib.Level.pred  in *.
assert (l > 0).
{ apply levelEqBEqNatFalse0.
  assumption. }
case_eq (gt_dec l 0).
* intros.
  rewrite H2 in H0.
  inversion H0.
  unfold CLevel.
  case_eq (lt_dec (l - 1) nbLevel).
  intros. subst.
  assert (ADT.CLevel_obligation_1 (l - 1) l0  = StateLib.Level.pred_obligation_1 l g ).
  apply proof_irrelevance.
  rewrite H4. reflexivity.
  intros.
  destruct l.
  subst.
  simpl in *.
  contradict H3.
  lia.
* intros.
  contradict H1.
  assumption.
Qed.

Lemma levelEqNat :
forall a b , a < nbLevel -> b < nbLevel -> CLevel a = CLevel b -> a = b.
Proof.
intros a b Ha Hb Hab.
 unfold CLevel in *.
 case_eq (lt_dec a nbLevel );intros g Ha'.
 + rewrite Ha' in Hab.
   case_eq (lt_dec b nbLevel);intros p Hb'.
   - rewrite Hb' in Hab.
     inversion Hab. intuition.
   - lia.
 + lia.
Qed.

Lemma level_gt :
forall x x0, x - x0 < nbLevel ->  CLevel (x - x0) > 0 -> x > x0.
Proof.
intros.
unfold CLevel in *.
case_eq (lt_dec (x - x0) nbLevel ).
intros. rewrite H1 in H0.
simpl in *. lia.
intros. contradict H1. lia.
Qed.

Lemma getNbLevelLe :
forall nbL,
Some nbL = StateLib.getNbLevel ->
nbL <= CLevel (nbLevel - 1).
Proof.
intros.
unfold getNbLevel in *.
destruct (gt_dec nbLevel 0).
inversion H.
unfold CLevel.
case_eq (lt_dec (nbLevel - 1) nbLevel); intros.
simpl.
lia.
lia.
assert (0 < nbLevel) by apply nbLevelNotZero.
lia.
Qed.

Lemma getNbLevelEq :
forall nbL,
Some nbL = StateLib.getNbLevel ->
nbL = CLevel (nbLevel - 1).
Proof.
intros.
unfold getNbLevel in *.
destruct (gt_dec nbLevel 0).
inversion H.
destruct nbL.
simpl in *.

unfold CLevel.
case_eq (lt_dec (nbLevel - 1) nbLevel); intros.
inversion H.
subst.
f_equal.
apply proof_irrelevance.
assert (0 < nbLevel) by apply nbLevelNotZero.
lia.
now contradict H.
Qed.

Lemma getNbLevelEqOption :
 StateLib.getNbLevel= Some (CLevel (nbLevel - 1)).
Proof.
unfold getNbLevel in *.
destruct (gt_dec nbLevel 0);simpl.
f_equal.
unfold CLevel.
case_eq (lt_dec (nbLevel - 1) nbLevel); simpl in *;intros.
f_equal.
apply proof_irrelevance.
lia.
assert (0 < nbLevel) by apply nbLevelNotZero.
lia.
Qed.

Lemma nbLevelEq :
nbLevel - 1 = CLevel (nbLevel - 1).
Proof.
unfold CLevel.
case_eq(lt_dec (nbLevel - 1) nbLevel); intros.
simpl;trivial.
assert(0<nbLevel) by apply nbLevelNotZero.
lia.
Qed.

Lemma fstLevelLe :
forall l: level ,
fstLevel <= l.
Proof.
unfold fstLevel.
unfold CLevel.
intros.
case_eq( lt_dec 0 nbLevel);intros.
simpl;lia.
assert(0 <nbLevel) by apply nbLevelNotZero.
lia.
Qed.

Lemma getNbLevelLt nbL:
StateLib.getNbLevel = Some nbL -> nbL < nbLevel.
Proof.
intros.
unfold  StateLib.getNbLevel in *.
destruct (gt_dec nbLevel 0).
inversion H.
simpl;trivial.
lia.
now contradict H.
Qed.

Lemma notFstLevel (level1 : level) :
 0 < level1 ->
StateLib.Level.eqb level1 fstLevel = false.
Proof.
unfold Level.eqb.
intros.
apply NPeano.Nat.eqb_neq.
unfold fstLevel.
unfold CLevel.
case_eq (lt_dec 0 nbLevel);intros.
simpl.
lia.
assert(0<nbLevel) by apply nbLevelNotZero.
lia.
Qed.

Lemma ClevelMinus0Eq (nbL: level) stop :
stop <= nbL ->
nbL = CLevel (nbL - stop) ->
stop = 0.
Proof.
intros.
destruct nbL;simpl.
unfold CLevel in *.
simpl in *.
case_eq(lt_dec (l - stop) nbLevel );intros;rewrite H1 in *.
inversion H0.
subst.
clear H0 H1.
lia.
lia.
Qed.

Lemma ClevelMinus0Le (nbL: level) stop :
stop <= nbL ->
nbL <= CLevel (nbL - stop) ->
stop = 0.
Proof.
intros.
destruct nbL;simpl.
unfold CLevel in *.
simpl in *.
case_eq(lt_dec (l - stop) nbLevel );intros;rewrite H1 in *.
simpl in *.
lia.
inversion H0.
subst.
clear H0 H1.
lia.
lia.
Qed.

(**** ADT : page **)
Lemma isDefaultPageFalse : forall p,   (defaultPage =? pa p) = false -> pa p <> defaultPage .
Proof.
intros.
apply beq_nat_false in H.
unfold not. intros.
contradict H. symmetry.
unfold defaultPage in *.
unfold CPage in *.
case_eq (lt_dec 0 nbPage).
intros.
rewrite H in H0.
rewrite H0. trivial.
intros.
rewrite H in H0. rewrite H0. intuition.
Qed.

Lemma isDefaultPageTrue : forall p,   (defaultPage =? pa p) = true -> pa p = defaultPage .
Proof.
intros.
apply beq_nat_true in H. symmetry.
unfold defaultPage in *.
unfold CPage in *.
case_eq (lt_dec 0 nbPage).
intros.
rewrite H0 in H.
symmetry.
simpl in *.
destruct p.
simpl in *.
subst.
destruct pa.
simpl in *.
subst.
assert (Hp = ADT.CPage_obligation_1 0 l ).
apply proof_irrelevance.
subst.
intuition.
intros.
rewrite H0 in H.
subst.
simpl in *.
destruct p.
simpl in *.
subst.
destruct pa.
simpl in *.
subst.
destruct page_d.
simpl in *.
assert (Hp = Hp0).
apply proof_irrelevance.
subst.
intuition.
Qed.

Lemma pageDecOrNot :
forall p1 p2 : page, p1 = p2 \/ p1<>p2.
Proof.
destruct p1;simpl in *;subst;destruct p2;simpl in *;subst.
assert (Heq :p=p0 \/ p<> p0) by lia.
destruct Heq as [Heq|Heq].
subst.
left;f_equal;apply proof_irrelevance.
right. unfold not;intros.
inversion H.
subst.
now contradict Heq.
Qed.

Lemma listPageDecOrNot :
forall x (l: list page), List.In x l \/
              ~List.In x l.
Proof.
induction l;trivial.
right;intuition.
simpl.
assert(a=x \/ a<> x) by apply pageDecOrNot.
destruct H.
left;left;trivial.
destruct IHl.
left;right;trivial.
right.
apply Logic.Classical_Prop.and_not_or. intuition.
Qed. 
*)   

(** ADT : index **)
Lemma indexEqFalse : 
forall a b : nat , a <= maxIdx -> b <= maxIdx -> a <> b -> CIndex a <> CIndex b.
Proof.
intros.
unfold CIndex.
case_eq (le_dec a maxIdx).
+ intros.
  case_eq (le_dec b maxIdx).
  - intros.
    unfold not in *.
    intros.
    apply H1.
    inversion H4.
    intuition.
  - intros. contradict H0. assumption.
+ intros. contradict H. intuition.
Qed.

Lemma indexltbTrue :
forall i1 i2 : index ,
StateLib.Index.ltb i1 i2 = true -> i1 < i2.
Proof. intros. unfold Index.ltb in H. 
apply NPeano.Nat.ltb_lt in H.
assumption.
Qed.

Lemma indexltbFalse :
forall i1 i2 : index ,
StateLib.Index.ltb i1 i2 = false -> i1 >= i2.
Proof.
intros.
unfold Index.ltb in *. 
apply not_lt.
apply NPeano.Nat.ltb_nlt in H.
lia.
Qed.

(*
Lemma indexBoundEq : 
forall i : index , i>= CIndex (tableSize - 1) -> i =  CIndex (tableSize - 1). 
Proof.
intros.
unfold CIndex in *.
destruct (lt_dec (tableSize - 1) tableSize).
simpl in *.
destruct i.
simpl in *.
subst.
assert(i = tableSize - 1). lia.
subst.
assert (Hi = ADT.CIndex_obligation_1 (tableSize - 1) l ).
apply proof_irrelevance.
subst. trivial.
contradict n.
assert (0 < tableSize).
assert (tableSize > tableSizeLowerBound).
apply tableSizeBigEnough.
unfold  tableSizeLowerBound in * . lia. lia.
Qed.
*)


Lemma indexDiffLtb :
forall i1 i2 : index, i2 < i1 \/ i1 < i2 <-> i2 <> i1.
Proof.
intros.
split;destruct i1, i2;
simpl in *.
 unfold not;
intros;
inversion H0; lia.
intros.
apply nat_total_order.
unfold not in *; intros; subst.
apply H; f_equal.
apply proof_irrelevance.
Qed.

(*
Lemma indexMaxEqFalseLt : 
forall idx : index, idx <> CIndex (tableSize - 1) -> idx < tableSize - 1.
Proof.
intros.
unfold CIndex in *.
case_eq (le_dec maxIdx maxIdx).
intros .
rewrite H0 in *.
destruct idx.
simpl in *.
apply not_ge.
unfold not.
intros.
contradict H.
assert (i = maxIdx).
lia.
subst.
f_equal.
apply proof_irrelevance.
intros.
assert(maxIdxLowerBound < maxIdx) by apply maxIdxBigEnough.
lia.
Qed.

Lemma SuccOddEven :
forall oneI twoI : index,
oneI < tableSize -1 ->
StateLib.Index.succ oneI = Some twoI ->
Nat.Odd oneI ->
Nat.Even twoI.
Proof.
intros.
unfold StateLib.Index.succ in *.
case_eq (lt_dec (oneI + 1) tableSize);intros; rewrite H2 in *;simpl in *.
inversion H0.
simpl in *.
revert H1.
clear.
intros.
destruct oneI.
simpl in *.
rewrite <- Nat.Even_succ in H1.
unfold Nat.Even in *.
destruct H1 as (m & Hm).
exists m.
lia.
now contradict H0.
Qed.

Lemma SuccEvenOdd :
forall oneI twoI : index,
oneI < tableSize -1 ->
StateLib.Index.succ oneI = Some twoI ->
Nat.Even oneI ->
Nat.Odd twoI.
Proof.
intros.
unfold StateLib.Index.succ in *.
case_eq (lt_dec (oneI + 1) tableSize);intros; rewrite H2 in *;simpl in *.
inversion H0.
simpl in *.
revert H1.
clear.
intros.
destruct oneI.
simpl in *.
rewrite <- Nat.Odd_succ in H1.
unfold Nat.Odd in *.
destruct H1 as (m & Hm).
exists m.
lia.
now contradict H0.
Qed.

Lemma indexMaxEqFalseLt1 :
forall idx : index, idx <> CIndex (tableSize - 1) -> idx < CIndex (tableSize - 1).
Proof.
intros.
unfold CIndex in *.
case_eq (lt_dec (tableSize - 1) tableSize).
intros .
rewrite H0 in *.
destruct idx.
simpl in *.
apply not_ge.
unfold not.
intros.
contradict H.
assert (i = tableSize - 1).
lia.
subst.
f_equal.
apply proof_irrelevance.
intros.
assert(tableSizeLowerBound < tableSize) by apply tableSizeBigEnough.
lia.
Qed.
*)

Lemma noteqIndex a b:
a < maxIdx +1 -> b < maxIdx +1 -> a<>b ->  
CIndex a <> CIndex b.
Proof.
intros.
apply indexEqFalse;
assert (maxIdx > maxIdxLowerBound).
apply maxIdxBigEnough.
unfold maxIdxLowerBound in *.
lia.  apply maxIdxBigEnough.
unfold maxIdxLowerBound in *.
lia. apply maxIdxBigEnough. lia.
Qed.

Lemma CIndex0lt :
CIndex 0 < maxIdx.
Proof.
unfold CIndex.
assert (maxIdx > maxIdxLowerBound).
apply maxIdxBigEnough.
unfold maxIdxLowerBound in *.
case_eq(lt_dec 0 maxIdx);intros;simpl;try lia.
Qed.

(*
Lemma CIndex1lt oneI:
StateLib.Index.succ (CIndex 0) = Some oneI->
oneI < tableSize - 1.
Proof.
unfold StateLib.Index.succ.
assert (tableSize > tableSizeLowerBound).
apply tableSizeBigEnough.
unfold tableSizeLowerBound in *.
case_eq(lt_dec (CIndex 0 + 1) tableSize);intros;simpl in *;try lia.
inversion H1.
simpl.
unfold CIndex.
case_eq(lt_dec 0 tableSize);intros;simpl;try lia.
now contradict H1.
Qed.
*)

Lemma CIndex0ltKSEntriesNb zeroI:
zeroI = CIndex 0 -> zeroI < kernelStructureEntriesNb.
Proof.
intros.
rewrite H. unfold CIndex. destruct (lt_dec 0 maxIdx).
simpl. apply KSEntriesNbNotZero.
contradict n. apply maxIdxNotZero.
Qed.

Lemma CIndex0ltMaxIdx zeroI:
zeroI = CIndex 0 ->
zeroI < maxIdx - 1.
Proof.
intros.
rewrite <- KSEntriesNbLessThanMaxIdx.
apply CIndex0ltKSEntriesNb.
assumption.
Qed.

Lemma indexEqId :
forall i : index, CIndex i = i.
Proof.
intros.
unfold CIndex.
destruct i.
simpl.
case_eq(le_dec i maxIdx); intros.
assert(ADT.CIndex_obligation_1 i l = Hi) by apply proof_irrelevance.
subst. reflexivity.
now contradict Hi.
Qed.


Lemma KSIsBE s :
forall addr : paddr,
isKS addr s ->
isBE addr s.
Proof.
intuition.
unfold isKS in *.
unfold isBE.
destruct (lookup addr (Monad.memory s) beqAddr) ; try(exfalso ; congruence).
destruct v ; try(exfalso ; congruence).
trivial.
Qed.

Lemma FreeSlotIsBE s :
forall addr : paddr,
isFreeSlot addr s ->
isBE addr s.
Proof.
intuition.
unfold isFreeSlot in *.
unfold isBE.
destruct (lookup addr (Monad.memory s) beqAddr) ; try(exfalso ; congruence).
destruct v ; try(exfalso ; congruence).
trivial.
Qed.

Lemma IdxLtMaxIdx (idx : index) :
idx <= maxIdx.
Proof.
destruct idx. simpl.
intuition.
Qed.

Lemma MaxIdxNextEq :
maxIdx + 1 = S maxIdx.
Proof.
lia.
Qed.

Lemma filterOptionPaddrSplit l1 l2 :
filterOptionPaddr (l1 ++ l2) = filterOptionPaddr l1 ++ filterOptionPaddr l2.
Proof.
induction l1.
- intuition.
- simpl. destruct a ; intuition.
	simpl. f_equal. intuition.
Qed.

Lemma NotInListNotInFilterPresent a l s:
~In a l -> ~In a (filterPresent l s).
Proof.
intro HNotInList.
induction l.
- intuition.
- simpl in *.
	destruct (lookup a0 (memory s) beqAddr) ; intuition.
	destruct v ; intuition.
	destruct (present b) ; intuition.
	simpl in *. intuition.
Qed.

Lemma NotInListNotInFilterPresentContra a l s:
In a (filterPresent l s) -> In a l.
Proof.
intro HBlockInList.
induction l.
- intuition.
- simpl in *.
	destruct (lookup a0 (memory s) beqAddr) ; intuition.
	destruct v ; intuition.
	destruct (present b) ; intuition.
	simpl in *. intuition.
Qed.

Lemma NotInListNotInFilterAccessible a l s:
~In a l -> ~In a (filterAccessible l s).
Proof.
intro HNotInList.
induction l.
- intuition.
- simpl in *.
	destruct (lookup a0 (memory s) beqAddr) ; intuition.
	destruct v ; intuition.
	destruct (accessible b) ; intuition.
	simpl in *. intuition.
Qed.

Lemma NotInListNotInFilter a l s:
~In a l -> ~In a (filter (childFilter s) l).
Proof.
intro HNotInList.
induction l.
- intuition.
- simpl in *.
	destruct (lookup a0 (memory s) beqAddr) ; intuition.
	destruct (childFilter s a0) ; intuition.
	simpl in *. intuition.
	destruct (childFilter s a0) ; intuition.
	simpl in *. intuition.
Qed.


Lemma InFilterAccessibleInList a l s:
In a (filterAccessible l s) -> In a l.
Proof.
intro HInFilterAccessible.
induction l.
- intuition.
- simpl in *.
	destruct (lookup a0 (memory s) beqAddr) ; intuition.
	destruct v ; intuition.
	destruct (accessible b) ; intuition.
	simpl in *. intuition.
Qed.

Lemma InFilterPresentInList a l s:
In a (filterPresent l s) -> In a l.
Proof.
intro HInFilterPresent.
induction l.
- intuition.
- simpl in *.
	destruct (lookup a0 (memory s) beqAddr) ; intuition.
	destruct v ; intuition.
	destruct (present b) ; intuition.
	simpl in *. intuition.
Qed.


Lemma NoDupListNoDupFilterPresent l s :
NoDup l -> NoDup (filterPresent l s).
Proof.
intro HNoDup.
induction l.
- intuition.
- simpl in *. apply NoDup_cons_iff in HNoDup.
	destruct (lookup a (memory s) beqAddr) ; intuition.
	destruct v ; intuition.
	destruct (present b) ; intuition.
	apply NoDup_cons_iff.
	simpl in *. intuition.
	eapply NotInListNotInFilterPresent with a l s in H.
	congruence.
Qed.

Lemma NotInPaddrListNotInPaddrFilterAccessible a l s:
~ In a (getAllPaddrAux l s) -> ~ In a (getAllPaddrAux (filterAccessible l s) s).
Proof.
intro HNotInList.
induction l.
- intuition.
- simpl in *.
	destruct (lookup a0 (memory s) beqAddr) eqn:Hlookupas ; intuition.
	destruct v ; intuition.
	destruct (accessible b) ; intuition.
	simpl in *. intuition.
	rewrite Hlookupas in *.
	apply in_app_or in H.
	simpl in *. intuition.
Qed.

Lemma NotInPaddrListNotInPaddrFilterAccessibleContra a l s:
In a (getAllPaddrAux (filterAccessible l s) s) ->
In a (getAllPaddrAux l s).
Proof.
intro HBlockInList.
induction l.
- intuition.
- simpl in *.
	destruct (lookup a0 (memory s) beqAddr) eqn:Hlookupas ; intuition.
	destruct v ; intuition.
	destruct (accessible b) ; intuition.
	simpl in *. rewrite Hlookupas in *.
	apply in_app_or in HBlockInList.
	apply in_app_iff. intuition.
Qed.

Lemma NoDupPaddrListNoDupPaddrFilterAccessible l s :
NoDup (getAllPaddrAux l s) -> NoDup (getAllPaddrAux (filterAccessible l s) s).
Proof.
intro HNoDup.
induction l.
- intuition.
- simpl in *.
	destruct (lookup a (memory s) beqAddr) eqn:Hlookupas ; intuition.
	destruct v ; intuition.
	destruct (accessible b) ; intuition.
	simpl. rewrite Hlookupas in *.
	apply Lib.NoDupSplitInclIff in HNoDup.
	apply Lib.NoDupSplitInclIff.
	simpl in *. intuition.
	unfold Lib.disjoint in*.
	intros addr HaddrIn. specialize (H0 addr HaddrIn).
	eapply NotInPaddrListNotInPaddrFilterAccessible with addr l s in H0.
	congruence.
	apply Lib.NoDupSplit in HNoDup. intuition.
Qed.

Lemma addrInBlockisBE a block s :
In a (getAllPaddrAux [block] s) ->
isBE block s.
Proof.
intro HaddrIn.
simpl in *.
unfold isBE.
destruct (lookup block (memory s) beqAddr) ; intuition.
destruct v ; intuition.
Qed.


Lemma addrNotInAllPaddrBlock offset1 offset2 startaddr left :
offset1 < offset2 ->
~In (CPaddr (offset1 + startaddr))
  (getAllPaddrBlockAux offset2 startaddr left).
Proof.
revert offset1 offset2.
induction left.
- intuition.
- intros. simpl in *.
	destruct (le_dec (S (offset1 + startaddr)) maxAddr) ; intuition.
	destruct (le_dec (offset2 + startaddr) maxAddr) ; intuition.
	simpl in *.
	intuition.
	inversion H1.
	contradict H2.
	unfold CPaddr.
	destruct (le_dec (offset1 + startaddr) maxAddr) ; intuition.
	inversion H0.
	apply Nat.add_cancel_r in H3.
	apply NPeano.Nat.lt_neq in H. congruence.
	specialize (IHleft offset1 (S offset2)) ; intuition.
	destruct (le_dec (offset2 + startaddr) maxAddr) ; intuition.
	simpl in *.
	intuition.
	contradict H1.
	unfold CPaddr.
	destruct (le_dec (offset1 + startaddr) maxAddr) ; intuition.
	inversion H0.
	apply Nat.add_cancel_r in H2.
	apply NPeano.Nat.lt_neq in H. congruence.
	inversion H0. apply plus_is_O in H2.
 	intuition. subst offset2.
	apply Nat.nlt_0_r in H. congruence.
	contradict H1.
	unfold CPaddr.
	destruct (le_dec (offset1 + startaddr) maxAddr) ; intuition.
	eapply IHleft. instantiate (1:= S offset2). instantiate (1:= S offset1).
	intuition. intuition.
	unfold CPaddr.
	destruct (le_dec (S offset1 + startaddr) maxAddr) ; intuition.
	simpl.
	contradict H0.
	specialize (IHleft offset1 (S offset2)) ; intuition.
	apply Nat.lt_lt_succ_r in H.
	intuition. unfold CPaddr in *.
	destruct (le_dec (offset1 + startaddr) maxAddr ) ; intuition.
	assert(l0 = l1). apply proof_irrelevance.
	subst l0. intuition.
	specialize (IHleft 0 (S offset2)) ; intuition.
	assert( 0 < S offset2) by apply NPeano.Nat.lt_0_succ.
	intuition.
	unfold CPaddr in *.
	destruct (le_dec (0 + startaddr) maxAddr ) ; intuition.
	contradict H0.
	clear.
	revert offset2.
	induction left.
	--- intuition.
	--- intro offset2. simpl.
			destruct (le_dec (S (offset2 + startaddr)) maxAddr) ; intuition.
			simpl in *.
			intuition.
			---- inversion H0.
			---- specialize (IHleft (S offset2)). intuition.
Qed.

Lemma NoDupPaddrBlockAux offset startaddr left :
NoDup (getAllPaddrBlockAux offset startaddr left).
Proof.
revert offset startaddr.
induction left.
- intros. simpl. apply NoDup_nil.
- intros. simpl in *.
	destruct (le_dec (offset + startaddr) maxAddr); try (apply NoDup_nil).
	apply NoDup_cons_iff.
	split.
	--
			revert offset l.
			intros.
			specialize (addrNotInAllPaddrBlock offset (S offset) startaddr left).
			(*assert(forall offset startaddr left, ~In (CPaddr (offset + startaddr))
  (getAllPaddrBlockAux (S offset) startaddr left)) by admit.
			intros. specialize (H offset startaddr left).*)
			unfold CPaddr in *.
			destruct (le_dec (offset + startaddr) maxAddr) ; intuition.
			unfold ADT.CPaddr_obligation_1 in *.
			assert({| p := offset + startaddr; Hp := l |} = {| p := offset + startaddr; Hp := l0 |}).
			f_equal.
			eapply proof_irrelevance.
			rewrite H1 in *.
			intuition.
	-- intuition.
Qed.


Lemma NoDupPaddrBlock startaddr endaddr :
NoDup (getAllPaddrBlock startaddr endaddr).
Proof.
unfold getAllPaddrBlock.
revert startaddr endaddr.
intros.
apply (NoDupPaddrBlockAux 0 startaddr (endaddr-startaddr)).
Qed.

Lemma blockIsMappedAddrInPaddrList block addr l s :
In block l ->
In addr (getAllPaddrAux [block] s) ->
In addr (getAllPaddrAux l s).
Proof.
intros.
induction l.
- intuition.
- simpl. simpl in H.
	intuition.
	+ subst a. simpl in *.
		destruct (lookup block (memory s) beqAddr ) ; intuition.
		destruct v ; intuition.
		apply in_or_app. left. rewrite app_nil_r in *. intuition.
	+ destruct (lookup a (memory s) beqAddr ) ; intuition.
		destruct v ; intuition.
Qed.

Lemma DisjointPaddrInPart partition block1 block2 addr s :
noDupUsedPaddrList s ->
isPDT partition s ->
In block1 (getMappedBlocks partition s) ->
In block2 (getMappedBlocks partition s) ->
block1 <> block2 ->
In addr (getAllPaddrAux [block1] s) ->
~ In addr (getAllPaddrAux [block2] s).
Proof.
intros HNoDupPaddr HPDTs Hblock1 Hblock2 Hblock1block2NotEq HaddrIn.
simpl in *.
unfold noDupUsedPaddrList in *.
specialize (HNoDupPaddr partition HPDTs).
unfold getUsedPaddr in *.
apply Lib.NoDupSplit in HNoDupPaddr.
intuition.
unfold getMappedPaddr in *.
induction ((getMappedBlocks partition s)).
- intuition.
- simpl in *.
	intuition.
	+	subst a. subst block1. congruence.
	+	subst a.
		specialize (blockIsMappedAddrInPaddrList block2 addr l s H3).
		simpl in *. intuition.
		destruct (lookup block1 (memory s) beqAddr) ; intuition.
		destruct v ; intuition.
		destruct (lookup block2 (memory s) beqAddr) ; intuition.
		destruct v ; intuition.
		apply Lib.NoDupSplitInclIff in H1.
		intuition.
		rewrite app_nil_r in *.
		specialize (H5 addr HaddrIn).
		congruence.
	+ subst a.
		specialize (blockIsMappedAddrInPaddrList block1 addr l s H2).
		simpl in *. intuition.
		destruct (lookup block1 (memory s) beqAddr) ; intuition.
		destruct v ; intuition.
		destruct (lookup block2 (memory s) beqAddr) ; intuition.
		destruct v ; intuition.
		apply Lib.NoDupSplitInclIff in H1.
		intuition.
		rewrite app_nil_r in *.
		specialize (H6 addr H).
		congruence.
	+ destruct (lookup a (memory s) beqAddr) ; intuition.
		destruct v ; intuition.
		apply Lib.NoDupSplit in H1.
		intuition.
Qed.

Lemma uniqueParent child parent parent' s:
isChild s ->
isParent s ->
In parent (getPartitions multiplexer s) ->
In parent' (getPartitions multiplexer s) ->
In child (getPartitions multiplexer s) ->
In child (getChildren parent s) ->
In child (getChildren parent' s) ->
parent = parent'.
Proof.
intros HisChild HisParent Hparent Hparent' Hchild Hchildparent Hchildparent'.
unfold isChild in *.
unfold isParent in *.
pose proof (isChild1 := HisChild child parent Hchild).
pose proof (isChild2 := HisChild child parent' Hchild).
pose proof (isParent1 := HisParent child parent Hparent Hchildparent).
pose proof (isParent2 := HisParent child parent' Hparent' Hchildparent').
unfold pdentryParent in *.
destruct (lookup child (memory s) beqAddr)  ; intuition.
destruct v ; intuition.
subst parent. subst parent'. intuition.
Qed.

Lemma indexEqbTrue : 
forall idx1 idx2 : index, true = StateLib.Index.eqb idx1 idx2 -> 
idx1 = idx2.
Proof.
unfold StateLib.Index.eqb in *.
intros.
symmetry in H.
apply beq_nat_true in H.
destruct idx1; destruct idx2.
simpl in *.
subst.
f_equal.
apply proof_irrelevance.
Qed.


Lemma indexLtZero :
forall idx : index, idx < CIndex 0 -> False.
Proof.
intros.
unfold CIndex in *.
case_eq (le_dec 0 maxIdx); intros; rewrite H0 in *.
destruct idx. simpl in *.
lia.
assert (maxIdxLowerBound < maxIdx) by apply maxIdxBigEnough.
lia.
Qed.
(*
Lemma indexSEqbZeroOdd : 
forall curidx idxsucc, 
true = StateLib.Index.eqb curidx (CIndex 0) -> 
StateLib.Index.succ curidx = Some idxsucc -> 
Nat.Odd idxsucc.
Proof.
intros.
apply indexEqbTrue in H.
subst.
unfold Index.succ in *.
case_eq (lt_dec (CIndex 0 + 1) tableSize); intros; rewrite H in *.
inversion H0.
destruct idxsucc.
inversion H2.
subst.
unfold Nat.Odd.
eexists 0.
simpl.
unfold CIndex.
case_eq (lt_dec 0 tableSize); intros.
simpl. trivial.
assert (tableSizeLowerBound < tableSize) by apply tableSizeBigEnough.
lia.
now contradict H0.
Qed.

Lemma indexSuccNot0:
forall FFI nextFFI,
StateLib.Index.succ FFI = Some nextFFI ->
(CIndex 0) <> nextFFI .
Proof.
intros.
unfold Index.succ in *.
case_eq(lt_dec (FFI + 1) tableSize);intros; rewrite H0 in *.
inversion H.
simpl in *.
unfold CIndex.
case_eq( lt_dec 0 tableSize);intros.
contradict H2.
inversion H2.
unfold not;intros.
subst.
lia.
pose proof tableSizeBigEnough.
lia.
now contradict H.
Qed.

Lemma indexZeroNotOdd :
forall idx idxsucc : index,
idx < idxsucc ->
StateLib.Index.succ (CIndex 0) = Some idxsucc ->
~ Nat.Odd idx.
Proof.
intros.
unfold Index.succ in *.
case_eq (lt_dec (CIndex 0 + 1) tableSize); intros; rewrite H1 in *.
inversion H0.
destruct idxsucc.
inversion H3.
subst.
clear H0 H3.
simpl in *.
unfold CIndex in H.
case_eq (lt_dec 0 tableSize); intros.
simpl. rewrite H0 in *.
simpl in *.
unfold not.
intros.
unfold Nat.Odd in *.
destruct H2.
rewrite H2 in *.
lia.
assert (tableSizeLowerBound < tableSize) by apply tableSizeBigEnough.
lia.
now contradict H0.
Qed.

 Lemma indexSEqbZeroLt :
forall  idxsucc idx : index,
StateLib.Index.succ (CIndex 0)  = Some idxsucc ->
idx < idxsucc ->
idx = CIndex 0.
Proof.
intros.
unfold Index.succ in *.
case_eq (lt_dec (CIndex 0 + 1) tableSize); intros; rewrite H1 in *.
inversion H.
destruct idxsucc.
inversion H3.
subst.
clear H H3 H1  l.
simpl in *.
unfold CIndex in *.
case_eq (lt_dec 0 tableSize); intros; rewrite H in *.
simpl in *.
destruct idx.
simpl in *.
destruct i.
f_equal.
apply proof_irrelevance.
lia.
assert (tableSizeLowerBound < tableSize) by apply tableSizeBigEnough.
lia.
now contradict H0.
Qed.

Lemma indexSuccGt :
forall idx curidx iIndex : index,
StateLib.Index.succ curidx = Some iIndex ->
idx < curidx ->
idx <> iIndex.
Proof.
intros.
unfold Index.succ in *.
case_eq (lt_dec(curidx + 1) tableSize); intros; rewrite H1 in *.
simpl in *.
destruct idx.
simpl in *.
destruct iIndex.
inversion H.
unfold not; intros.
inversion H2.
subst.
lia.
now contradict H.
Qed.
Lemma Succ0is1 oneI:
StateLib.Index.succ (CIndex 0) = Some oneI ->
oneI = CIndex 1.
Proof.
intros.
unfold StateLib.Index.succ in *.

assert(CIndex 0 + 1 = 1).
{
unfold CIndex.
case_eq (lt_dec 0 tableSize );intros.
simpl;trivial.
assert (tableSize > tableSizeLowerBound).
apply tableSizeBigEnough.
unfold tableSizeLowerBound in *.
lia. }
 unfold MALInternal.Index.succ_obligation_1 in *.
rewrite H0 in *.
case_eq(lt_dec 1 tableSize);intros;simpl in *;
rewrite H1 in *;try lia.
inversion H.
subst.
unfold CIndex.
rewrite H1.
f_equal.
now contradict H1.
Qed.

Lemma indexSuccEqFalse:
forall  curidx iIndex : index,
StateLib.Index.succ curidx = Some iIndex ->
 curidx <> iIndex.
Proof.
intros.
unfold Index.succ in *.
case_eq (lt_dec(curidx + 1) tableSize); intros; rewrite H0 in *.
simpl in *.
destruct iIndex.
inversion H.
subst.
clear H.
unfold not; intros.
destruct curidx.
simpl in *.
inversion H.
lia.
now contradict H.
Qed.

Lemma indexSuccSuccOddOr (curidx iIndex nextidx idx : index):
StateLib.Index.succ curidx = Some iIndex ->
StateLib.Index.succ iIndex = Some nextidx ->
Nat.Odd curidx ->
Nat.Odd idx ->
idx < nextidx ->
idx = curidx \/ idx < curidx.
Proof.
intros.
unfold StateLib.Index.succ in *.
      destruct (lt_dec (curidx + 1) tableSize); try now contradict H.
      inversion H; clear H.
      destruct (lt_dec (iIndex + 1) tableSize); try now contradict H0.
      inversion H0; clear H0.
      destruct nextidx.
      inversion H4; clear H4.
      destruct iIndex.
      simpl in *.
      subst.
      inversion H5; clear H5.
      destruct curidx.
      simpl in *.
      destruct idx.
      simpl in *.
      rewrite <- H0 in H3.
      clear H0 Hi l0 l Hi0 .
      assert (i1 = i \/ i1 < i).
      unfold Nat.Odd in *.
      destruct H1 ; destruct H2.

      lia.
      destruct H.
      left.
      subst.
      f_equal.
      apply proof_irrelevance.
      right; trivial.
Qed.

Lemma indexSuccSuccEvenOr (curidx iIndex nextidx idx : index):
StateLib.Index.succ curidx = Some iIndex ->
StateLib.Index.succ iIndex = Some nextidx ->
Nat.Even curidx ->
Nat.Even idx ->
idx < nextidx ->
idx = curidx \/ idx < curidx.
Proof.
intros.
unfold StateLib.Index.succ in *.
      destruct (lt_dec (curidx + 1) tableSize); try now contradict H.
      inversion H; clear H.
      destruct (lt_dec (iIndex + 1) tableSize); try now contradict H0.
      inversion H0; clear H0.
      destruct nextidx.
      inversion H4; clear H4.
      destruct iIndex.
      simpl in *.
      subst.
      inversion H5; clear H5.
      destruct curidx.
      simpl in *.
      destruct idx.
      simpl in *.
      rewrite <- H0 in H3.
      clear H0 Hi l0 l Hi0 .
      assert (i1 = i \/ i1 < i).
      destruct H1 ; destruct H2.
      lia.
      destruct H.
      left.
      subst.
      f_equal.
      apply proof_irrelevance.
      right; trivial.
Qed.

Lemma indexSuccSuccEvenOddLt (curidx iIndex nextidx idx : index):
StateLib.Index.succ curidx = Some iIndex ->
StateLib.Index.succ iIndex = Some nextidx ->
Nat.Even idx ->
Nat.Odd curidx ->
idx < nextidx ->
idx < iIndex ->
idx < curidx.
Proof.
intros.
unfold StateLib.Index.succ in *.
      destruct (lt_dec (curidx + 1) tableSize); try now contradict H.
      inversion H; clear H.
      destruct (lt_dec (iIndex + 1) tableSize); try now contradict H0.
      inversion H0; clear H0.
      destruct nextidx.
      inversion H5; clear H5.
      destruct iIndex.
      simpl in *.
      subst.
      inversion H6; clear H6.
      destruct curidx.
      simpl in *.
      destruct idx.
      simpl in *.
      destruct H1; destruct H2.
      subst.

      lia.
Qed.
Lemma indexSuccSuccOddEvenLt (curidx iIndex nextidx idx : index):
StateLib.Index.succ curidx = Some iIndex ->
StateLib.Index.succ iIndex = Some nextidx ->
Nat.Odd idx ->
Nat.Even curidx ->
idx < nextidx ->
idx < iIndex ->
idx < curidx.
Proof.
intros.
unfold StateLib.Index.succ in *.
destruct (lt_dec (curidx + 1) tableSize); try now contradict H.
inversion H; clear H.
destruct (lt_dec (iIndex + 1) tableSize); try now contradict H0.
inversion H0; clear H0.
destruct nextidx.
inversion H5; clear H5.
destruct iIndex.
simpl in *.
subst.
inversion H6; clear H6.
destruct curidx.
simpl in *.
destruct idx.
simpl in *.
destruct H1; destruct H2.
subst.
lia.
Qed.

Lemma succLet (Scuridx SScuridx idx:index):

StateLib.Index.succ Scuridx = Some SScuridx ->
idx < SScuridx ->
idx = Scuridx \/ idx < Scuridx.
Proof.
intros.
unfold Index.succ in *.
case_eq(lt_dec (Scuridx + 1) tableSize);intros;rewrite H1 in *.
inversion H.
destruct SScuridx;simpl in *.
clear H.
inversion H3.
subst.
replace (Scuridx + 1) with (S Scuridx) in *by lia.
apply lt_n_Sm_le in H0.
apply or_comm.
clear H1 H3.
intros.
destruct Scuridx;simpl in *;destruct idx;simpl in *.
rewrite Nat.le_lteq in H0.
destruct H0.
left;trivial.
right.
subst.
f_equal.
apply proof_irrelevance.
now contradict H0.
Qed.



Lemma indexNotEqSuccNotEq (idx1 idx2 : index):
idx1 < tableSize -1 ->
idx2 < tableSize -1 ->
idx1 <> idx2 ->
StateLib.Index.succ idx2 <> StateLib.Index.succ idx1.
Proof.
intros.
unfold Index.succ.
case_eq (lt_dec (idx2 + 1) tableSize); intros; try lia.
case_eq (lt_dec (idx1 + 1) tableSize); intros; try lia.
destruct idx1; destruct idx2; simpl in *.
unfold not; intros Hfalse.
inversion Hfalse.
assert (i0 = i) by lia.
subst.
contradict H1.
f_equal.
apply proof_irrelevance.
Qed.

Lemma tableSizeMinus0:
forall idx: index,  idx = CIndex (tableSize - 1) -> idx>0.
Proof.
intros.
unfold CIndex in *.
assert(tableSize > tableSizeLowerBound) by apply tableSizeBigEnough.
unfold tableSizeLowerBound in *.
case_eq(lt_dec (tableSize - 1) tableSize);intros Hcase Hcasedec;rewrite Hcasedec in *;
simpl in *.
destruct idx;simpl in *.
inversion H;subst.
lia.
lia.
Qed.

Lemma tableSizeMinus2:
CIndex (tableSize - 1) - 1 = tableSize - 2.
Proof.
unfold CIndex.
case_eq(lt_dec (tableSize - 1) tableSize);intros;simpl in *;try lia.
assert(tableSize> tableSizeLowerBound).
apply tableSizeBigEnough.
lia.
Qed.

Lemma TableSizeMinus2:
forall idx, idx < CIndex (tableSize - 2) -> idx < CIndex (tableSize - 1).
Proof.
intros.
unfold CIndex in *.
assert(tableSize > tableSizeLowerBound) by apply tableSizeBigEnough.
unfold tableSizeLowerBound in *.
case_eq( lt_dec (tableSize - 2) tableSize);intros Hi Hii ; rewrite Hii in *;simpl in *; try lia.
case_eq (lt_dec (tableSize - 1) tableSize);intros;simpl; lia.
Qed.

Lemma predMaxIndex :
forall i,  StateLib.Index.pred (CIndex (tableSize - 1)) = Some i ->
i = CIndex (tableSize - 2).
Proof.
intros.
unfold StateLib.Index.pred in *.
case_eq( gt_dec (CIndex (tableSize - 1)) 0);intros;rewrite H0 in *;try now contradict H.
inversion H.
clear H H2.
assert(tableSize> tableSizeLowerBound).
apply tableSizeBigEnough.
rewrite <- tableSizeMinus2.
unfold CIndex at 3.
case_eq(lt_dec (CIndex (tableSize - 1) - 1) tableSize);simpl;intros;try lia.
f_equal.
apply proof_irrelevance.
clear H0 H1.
contradict n.
unfold CIndex in *.
case_eq(lt_dec (tableSize - 1) tableSize);intros;simpl in *;
rewrite H0 in *.
simpl in *.
lia.
lia.
Qed.
(** ADT : vaddr **)
Lemma lengthVAddrNotZero (va : vaddr) : fstLevel < (length va -1).
Proof.
 unfold fstLevel.  destruct va.
 simpl. rewrite Hva. unfold CLevel. case_eq (lt_dec 0 nbLevel).
 simpl. intros. lia.
 intros. destruct level_d. simpl. lia.
 Qed.

Lemma CLevelMinusEq0 :
forall (a : level) b , CLevel (a -  b) = CLevel 0 ->   a = CLevel b \/ a < b.
Proof.
intros.
unfold CLevel in *.
case_eq (lt_dec (a - b) nbLevel );
intros lab Hab; rewrite Hab in *.
case_eq(lt_dec 0 nbLevel);
intros l0 H0;
rewrite H0 in*.
inversion H.
case_eq (lt_dec b nbLevel);
intros lb Hb.
simpl in *.
apply NPeano.Nat.sub_0_le in H2.
apply le_lt_or_eq in H2.
destruct H2.
right; assumption.
left.
destruct a.
simpl in *.
subst.
assert (Hl =  ADT.CLevel_obligation_1 b lb ) by
apply proof_irrelevance.
subst. reflexivity.
right; destruct a; simpl in *; lia.
assert (0 < nbLevel) by apply nbLevelNotZero.
now contradict H1.
destruct a. simpl in *.
lia.
Qed.


(** beqPairs **)
Lemma beqPairsTrue :
forall table1 idx1 table2 idx2 , table1 = table2 /\ idx1 = idx2 <->
beqPairs (table1, idx1) (table2, idx2) beqPage beqIndex = true.
Proof.
intros.
unfold beqPairs.
cbn.
unfold beqPage , beqIndex .
split.
* case_eq (table1 =? table2) ; case_eq(idx1 =? idx2);intuition.
  apply beq_nat_false in H.
  destruct idx1 , idx2. simpl in *. inversion H3. lia.
  apply beq_nat_false in H0.
  destruct table1, table2. simpl in *.
  inversion H2. lia.
  destruct ((false && false)%bool). trivial.
  apply beq_nat_false in H0.
  destruct table1, table2. simpl in *.
  inversion H2. lia.
* intros.
  case_eq (table1 =? table2) ; case_eq(idx1 =? idx2);intuition.
  apply beq_nat_true in H1; trivial.
  destruct table1, table2; simpl in *; subst; f_equal; apply proof_irrelevance.
  destruct idx1 , idx2; simpl in *.
  apply beq_nat_true in H0; subst; f_equal; apply proof_irrelevance.
  apply beq_nat_true in H1; trivial.
  destruct table1, table2; simpl in *; subst; f_equal; apply proof_irrelevance.
  rewrite H0 in H.
  rewrite H1 in H.
  case_eq ((true && false)%bool); intros.
  apply Bool.andb_true_iff in H2.
  now contradict H2.
  rewrite H2 in H; now contradict H.
  rewrite H0 in H.
  rewrite H1 in H.
  case_eq ((false && true)%bool); intros.
  apply Bool.andb_true_iff in H2.
  now contradict H2.
  rewrite H2 in H; now contradict H.
  apply beq_nat_true in H0.
  destruct idx1 , idx2; simpl in *;subst; f_equal; apply proof_irrelevance.
  rewrite H0 in H.
  rewrite H1 in H.
  case_eq ((false && false)%bool); intros.
  apply Bool.andb_true_iff in H2.
  now contradict H2.
  rewrite H2 in H; now contradict H.
  rewrite H0 in H.
  rewrite H1 in H.
  case_eq ((false && false)%bool); intros.
  apply Bool.andb_true_iff in H2.
  now contradict H2.
  rewrite H2 in H; now contradict H.
Qed.

Lemma beqPairsFalse :
forall table1 idx1 table2 idx2 ,
table1 <> table2 \/ idx1 <> idx2 <->
beqPairs (table1, idx1) (table2, idx2) beqPage beqIndex = false.
Proof.
intros.
unfold beqPairs.
cbn.
unfold beqPage , beqIndex .
intuition.
case_eq (table1 =? table2) ; case_eq(idx1 =? idx2);intuition.
contradict H0.
apply beq_nat_true in H1.
destruct table1, table2. simpl in *. subst.
assert (Hp = Hp0).
apply proof_irrelevance. subst. trivial.
assert((idx1 =? idx2) = false).
apply Nat.eqb_neq. unfold not.
intros.
destruct idx1; destruct idx2.
simpl in *.
subst.
apply H0.
f_equal.
apply proof_irrelevance.
rewrite H.
case_eq ((table1 =? table2) && false).
intros.
apply andb_true_iff in H1.
intuition.
trivial.
case_eq (table1 =? table2) ; case_eq(idx1 =? idx2);intuition.
+ rewrite H1 in H.
  rewrite H0 in H.
  intuition.
+ apply beq_nat_false in H0.
  right.
  intros.
  destruct idx1; destruct idx2.
  simpl in *.
  inversion H2.
  subst.
  now contradict H0.
+ apply beq_nat_false in H1.
  left.
  intros.
  destruct table1; destruct table2.
  simpl in *.
  inversion H2.
  subst.
  now contradict H1.
+ apply beq_nat_false in H1.
  left.
  intros.
  destruct table1; destruct table2.
  simpl in *.
  inversion H2.
  subst.
  now contradict H1.
Qed.*)

Lemma beqAddrTrue :
forall addr1 addr2 ,
addr1 = addr2 <->
beqAddr addr1 addr2 = true.
Proof.
intros.
unfold beqAddr.
intuition.
case_eq ((addr1 =? addr2)).
intuition.
intros.
apply beq_nat_false in H0.
congruence.
apply beq_nat_true in H.
destruct addr1, addr2. simpl in *. subst.
assert (Hp = Hp0).
apply proof_irrelevance. subst. trivial.
Qed.

Lemma beqAddrFalse :
forall addr1 addr2 ,
addr1 <> addr2 <->
beqAddr addr1 addr2 = false.
Proof.
intros.
unfold beqAddr.
intuition.
case_eq ((addr1 =? addr2)).
intuition.
contradict H.
apply beq_nat_true in H0.
destruct addr1, addr2. simpl in *. subst.
assert (Hp = Hp0).
apply proof_irrelevance. subst. trivial.
intros. reflexivity.
case_eq (addr1 =? addr2) ; intuition.
+ rewrite H0 in H.
	rewrite H0 in H1.
	congruence.
+	rewrite H0 in H1.
	contradict H1.
	rewrite NPeano.Nat.eqb_refl.
	unfold not.
	congruence.
Qed.

Lemma beqAddrSym :
forall addr1 addr2 ,
beqAddr addr1 addr2 = beqAddr addr2 addr1.
Proof.
intros. unfold beqAddr.
case_eq ((addr1 =? addr2)). intuition.
apply beq_nat_true in H. rewrite H. apply eq_sym. apply Nat.eqb_refl.
intros. apply eq_sym.
apply Nat.eqb_neq. apply Nat.eqb_neq in H. unfold not in *.
intros. intuition.
Qed.

Lemma paddrEqId :
forall p : paddr, CPaddr p = p.
Proof.
intros.
unfold CPaddr.
destruct p.
simpl.
case_eq(le_dec p maxAddr); intros.
assert(ADT.CPaddr_obligation_1 p l = Hp) by apply proof_irrelevance.
subst. reflexivity.
now contradict Hp.
Qed.

Lemma PaddrSym :
forall addr1 addr2 : paddr,
addr1 = addr2 -> addr2 = addr1.
Proof.
intuition.
Qed.

Lemma PaddrNatTrue :
forall addr1 addr2 : paddr,
beqAddr addr1 addr2 = true <->
PeanoNat.Nat.eqb (p addr1) (p addr2) = true.
Proof.
intuition.
Qed.

Lemma PaddrNatFalse :
forall addr1 addr2 : paddr,
beqAddr addr1 addr2 = false <->
PeanoNat.Nat.eqb (p addr1) (p addr2) = false.
Proof.
intuition.
Qed.

Lemma CPaddrInjection3 addr1 :
forall value1 s,
lookup addr1 (memory s) beqAddr = value1 ->
addr1 <= maxAddr.
Proof.
intros.
destruct addr1. simpl in *. intuition.
Qed.


Lemma CPaddrInjection (addr1 addr2 : paddr):
CPaddr addr1 = CPaddr addr2 -> addr1 = addr2.
Proof.
intros.
rewrite paddrEqId in H. rewrite paddrEqId in H. intuition.
Qed.

Lemma CPaddrInjectionNat (addr1nat addr2nat : nat) :
addr1nat = addr2nat ->
CPaddr addr1nat = CPaddr addr2nat.
Proof.
intros. rewrite H in *. reflexivity.
Qed.

Lemma CPaddrInjection4 (addr1 : paddr):
forall value1 s,
lookup addr1 (memory s) beqAddr = value1 ->
exists x, x = CPaddr addr1.
Proof.
intros.
eexists. intuition.
Qed.

Lemma CPaddrInjection7 (addr1 addr2: paddr) :
CPaddr addr1 <> CPaddr addr2 ->
(p addr1) <> (p addr2).
Proof.
intros. intuition.
Qed.

Lemma CPaddrInjection6 (addr1 addr2: paddr) :
CPaddr addr1 = CPaddr addr2 ->
addr1 = addr2.
Proof.
intuition.
apply CPaddrInjection. intuition.
Qed.

Lemma CIndexInjection (addr1 addr2 : index):
CIndex addr1 = CIndex addr2 -> addr1 = addr2.
Proof.
intros.
rewrite indexEqId in H. rewrite indexEqId in H. intuition.
Qed.


Lemma CIndexInjectionNat (addr1nat addr2nat : nat) :
addr1nat = addr2nat ->
CIndex addr1nat = CIndex addr2nat.
Proof.
intros. rewrite H in *. reflexivity.
Qed.

Lemma CIndexNextZeroEq p:
p <= maxIdx -> (* also p < maxIdx*)
CIndex p = CIndex 0 ->
p = 0.
Proof.
intros. intuition.
induction p.
- intuition.
- unfold CIndex in *.
	destruct (le_dec 0 maxIdx) ; intuition.
	destruct (le_dec (S p) maxIdx) ; try (simpl in * ; congruence).
Qed.

Lemma CIndexNextZeroNotEq p:
p < maxIdx ->
CIndex (S p) <> CIndex 0.
Proof.
intuition.
apply CIndexNextZeroEq in H0.
apply PeanoNat.Nat.neq_succ_0 in H0. intuition. lia.
Qed.

Lemma CIndexLt p max :
p <= maxIdx ->
CIndex p < max ->
p < max.
Proof.
intuition.
induction p.
- intuition.
- unfold CIndex in *.
	destruct (le_dec (S p) maxIdx) ; try (simpl in * ; congruence).
Qed.


Require Import List Classical_Prop.
Lemma listIndexDecOrNot :
forall p1 p2 : list index, p1 = p2 \/ p1<>p2.
Proof.
induction p1;intros.
induction p2;intros.
left;trivial.
simpl.
right;intuition.
now contradict H.
now contradict H.
induction p2;simpl;intros.
right;intuition.
now contradict H.
destruct IHp2.
rewrite H.
right.
clear.
induction p2;simpl.
intuition.
now contradict H.
unfold not;intros. contradict IHp2.
inversion H.
subst.
trivial.
apply NNPP.
unfold not at  1.
intros.
apply not_or_and in H0.
destruct H0.
now contradict H1.
Qed.

(* DUP *)
Lemma beqIdxTrue : 
forall addr1 addr2 , 
addr1 = addr2 <-> 
beqIdx addr1 addr2 = true.
Proof.
intros.
unfold beqIdx.
intuition.
case_eq ((addr1 =? addr2)).
intuition.
intros.
apply beq_nat_false in H0.
congruence.
apply beq_nat_true in H.
destruct addr1, addr2. simpl in *. subst.
assert (Hi = Hi0).
apply proof_irrelevance. subst. trivial.
Qed.

(* DUP *)
Lemma beqIdxFalse : 
forall addr1 addr2 , 
addr1 <> addr2 <-> 
beqIdx addr1 addr2 = false.
Proof.
intros.
unfold beqIdx.
intuition.
case_eq ((addr1 =? addr2)).
intuition.
contradict H.
apply beq_nat_true in H0.
destruct addr1, addr2. simpl in *. subst.
assert (Hi = Hi0).
apply proof_irrelevance. subst. trivial.
intros. reflexivity.
case_eq (addr1 =? addr2) ; intuition.
+ rewrite H0 in H.
	rewrite H0 in H1.
	congruence.
+	rewrite H0 in H1.
	contradict H1.
	rewrite NPeano.Nat.eqb_refl.
	unfold not.
	congruence.
Qed.

(*
Lemma vaddrDecOrNot :
forall p1 p2 : vaddr, p1 = p2 \/ p1<>p2.
Proof.
destruct p1;destruct p2;simpl in *.
assert(Hor : va = va0 \/ va<>va0).
apply listIndexDecOrNot.
destruct Hor as [Hor | Hor].
subst.
left;simpl.
f_equal.
apply proof_irrelevance.
right.
simpl.
unfold not;intros Hirr.
inversion Hirr.
subst;now contradict Hor.
Qed.

Lemma idxPRsucNotEqidxPPR : PRidx < tableSize - 1 ->
exists succidx1 : index, Index.succ PRidx = Some succidx1 /\ (succidx1 = PPRidx -> False).
Proof.
unfold Index.succ.
case_eq (lt_dec (PRidx + 1) tableSize); intros.
eexists.
split.
instantiate (1:= CIndex (PRidx + 1)).
f_equal.
unfold CIndex .
case_eq (lt_dec(PRidx + 1) tableSize); intros.
f_equal.
apply proof_irrelevance.
abstract lia.
unfold CIndex.
case_eq(lt_dec (PRidx + 1) tableSize ); intros.

assert(Hi : {| i := PRidx + 1; Hi := ADT.CIndex_obligation_1 (PRidx + 1) l0 |} = PPRidx)
by trivial.
contradict Hi.
subst.
unfold PRidx. unfold PPRidx.
unfold CIndex at 3.
case_eq (lt_dec 10 tableSize); intros.
unfold not; intros Hii.
inversion Hii as (Hi2).
unfold CIndex in Hi2.
case_eq(lt_dec 0 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
simpl in *.
inversion Hii.
abstract lia.
abstract lia.
assert (tableSize > tableSizeLowerBound).
apply tableSizeBigEnough.
unfold tableSizeLowerBound in *.
abstract lia.
assert (tableSize > tableSizeLowerBound).
apply tableSizeBigEnough.
unfold tableSizeLowerBound in *.
abstract lia.
abstract lia.
Qed.
     Lemma idxPPRsuccNotEqidxPR : PPRidx < tableSize - 1 ->
    exists succidx2 : index, Index.succ PPRidx = Some succidx2 /\ (succidx2 = PRidx -> False).
    Proof.
    unfold Index.succ.
    case_eq (lt_dec (PPRidx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (PPRidx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(PPRidx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    abstract lia.
    unfold CIndex.
    case_eq(lt_dec (PPRidx + 1) tableSize ); intros.
    assert(Hi : {| i := PPRidx + 1; Hi := ADT.CIndex_obligation_1 (PPRidx + 1) l0 |} = PRidx)
    by trivial.
    contradict Hi.
    subst.
    unfold PPRidx. unfold PRidx.
    unfold CIndex at 3.
    case_eq (lt_dec 0 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 10 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *.
    inversion Hii.
    abstract lia.
    abstract lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract lia.
    abstract lia.
    Qed.
Lemma idxPRidxPPRNotEq : PRidx <> PPRidx.
    Proof.
      unfold PRidx. unfold PPRidx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      abstract lia.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      abstract lia.
      apply tableSizeBigEnough.
      abstract lia. Qed.

    Lemma idxPPRsuccNotEqidxPD : PPRidx < tableSize - 1 ->
    exists succidx2 : index, StateLib.Index.succ PPRidx = Some succidx2 /\ (succidx2 = PDidx -> False).
    Proof.
    unfold StateLib.Index.succ.
    case_eq (lt_dec (PPRidx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (PPRidx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(PPRidx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    abstract lia.
    unfold CIndex.
    case_eq(lt_dec (PPRidx + 1) tableSize ); intros.

    assert(Hi : {| i := PPRidx + 1; Hi := ADT.CIndex_obligation_1 (PPRidx + 1) l0 |} = PDidx)
    by trivial.
    contradict Hi.
    subst.
    unfold PPRidx. unfold PDidx.
    unfold CIndex at 3.
    case_eq (lt_dec 2 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 10 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *.
    inversion Hii.
    abstract lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract lia.
    abstract lia.
    abstract lia.
    Qed.

Lemma idxPPRidxPDNotEq : PPRidx <> PDidx.
    Proof.
      unfold PPRidx. unfold PDidx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      abstract lia.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      abstract lia. apply tableSizeBigEnough. abstract lia. Qed.
    Lemma idxPDsucNotEqidxPPR :  PDidx < tableSize - 1 ->
    exists succidx1 : index, StateLib.Index.succ PDidx = Some succidx1 /\ (succidx1 = PPRidx -> False).
    Proof.
    unfold StateLib.Index.succ.
    case_eq (lt_dec (PDidx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (PDidx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(PDidx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    abstract lia.
    unfold CIndex.
    case_eq(lt_dec (PDidx + 1) tableSize ); intros.

    assert(Hi : {| i := PDidx + 1; Hi := ADT.CIndex_obligation_1 (PDidx + 1) l0 |} = PPRidx)
    by trivial.
    contradict Hi.
    subst.
    unfold PDidx. unfold PPRidx.
    unfold CIndex at 3.
    case_eq (lt_dec 10 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 2 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *.
    inversion Hii.
    abstract lia.
    abstract lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract lia.
    abstract lia.
    Qed.

 Lemma idxPDidxPPRNotEq : PDidx <> PPRidx.
    Proof.
      unfold PRidx. unfold sh3idx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      abstract lia.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      abstract lia.
      apply tableSizeBigEnough.
      abstract lia. Qed.

 Lemma idxPPRidxSh1NotEq : PPRidx <> sh1idx.
    Proof.
      unfold PPRidx. unfold sh1idx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      abstract lia.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      abstract lia. apply tableSizeBigEnough. abstract lia. Qed.

    Lemma idxPPRsuccNotEqidxSh1 : PPRidx < tableSize - 1 ->
    exists succidx2 : index, StateLib.Index.succ PPRidx = Some succidx2 /\ (succidx2 = sh1idx -> False).
    Proof.
    unfold StateLib.Index.succ.
    case_eq (lt_dec (PPRidx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (PPRidx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(PPRidx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    abstract lia.
    unfold CIndex.
    case_eq(lt_dec (PPRidx + 1) tableSize ); intros.

    assert(Hi : {| i := PPRidx + 1; Hi := ADT.CIndex_obligation_1 (PPRidx + 1) l0 |} = sh1idx)
    by trivial.
    contradict Hi.
    subst.
    unfold PPRidx. unfold sh1idx.
    unfold CIndex at 3.
    case_eq (lt_dec 4 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 10 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *.
    inversion Hii.
    abstract lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract lia.
    abstract lia.
    abstract lia.
    Qed.

    Lemma idxSh1succNotEqidxPPR : sh1idx < tableSize - 1 ->
    exists succidx1 : index, StateLib.Index.succ sh1idx = Some succidx1 /\ (succidx1 = PPRidx -> False).
    Proof.
    unfold StateLib.Index.succ.
    case_eq (lt_dec (sh1idx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (sh1idx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(sh1idx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    abstract lia.
    unfold CIndex.
    case_eq(lt_dec (sh1idx + 1) tableSize ); intros.

    assert(Hi : {| i := sh1idx + 1; Hi := ADT.CIndex_obligation_1 (sh1idx + 1) l0 |} = PPRidx)
    by trivial.
    contradict Hi.
    subst.
    unfold sh1idx. unfold PPRidx.
    unfold CIndex at 3.
    case_eq (lt_dec 10 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 4 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *.
    inversion Hii.
    abstract lia.
    abstract lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract lia.
    abstract lia.
    Qed.

Lemma idxSh1idxPPRnotEq : sh1idx <> PPRidx.
    Proof.
      unfold sh1idx. unfold PPRidx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      abstract lia.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      abstract lia.
      apply tableSizeBigEnough.
      abstract lia. Qed.

    Lemma idxPPRsuccNotEqidxSh2 : PPRidx < tableSize - 1 ->
    exists succidx2 : index, StateLib.Index.succ PPRidx = Some succidx2 /\ (succidx2 = sh2idx -> False).
    Proof.
    unfold StateLib.Index.succ.
    case_eq (lt_dec (PPRidx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (PPRidx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(PPRidx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    abstract lia.
    unfold CIndex.
    case_eq(lt_dec (PPRidx + 1) tableSize ); intros.
    assert(Hi : {| i := PPRidx + 1; Hi := ADT.CIndex_obligation_1 (PPRidx + 1) l0 |} = sh2idx)
    by trivial.
    contradict Hi.
    subst.
    unfold PPRidx. unfold sh2idx.
    unfold CIndex at 3.
    case_eq (lt_dec 6 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 10 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *.
    inversion Hii.
    abstract lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract lia.
    abstract lia.
    abstract lia.
    Qed.

Lemma idxPPRidxSh2NotEq : PPRidx <> sh2idx. Proof.
      unfold PPRidx. unfold sh2idx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      abstract lia.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      abstract lia.
      apply tableSizeBigEnough.
      abstract lia. Qed.
    Lemma idxSh2succNotEqidxPPR : sh2idx < tableSize - 1 ->
    exists succidx1 : index, StateLib.Index.succ sh2idx = Some succidx1 /\ (succidx1 = PPRidx -> False).
    Proof.
    unfold StateLib.Index.succ.
    case_eq (lt_dec (sh2idx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (sh2idx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(sh2idx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    abstract lia.
    unfold CIndex.
    case_eq(lt_dec (sh2idx + 1) tableSize ); intros.
    assert(Hi : {| i := sh2idx + 1; Hi := ADT.CIndex_obligation_1 (sh2idx + 1) l0 |} = PPRidx)
    by trivial.
    contradict Hi.
    subst.
    unfold sh2idx. unfold PPRidx.
    unfold CIndex at 3.
    case_eq (lt_dec 10 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 6 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *.
    inversion Hii.
    abstract lia.
    abstract lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract lia.
    abstract lia.
    Qed.

Lemma idxSh2idxPPRnotEq : sh2idx <> PPRidx.
    Proof.
      unfold sh1idx. unfold sh3idx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      abstract lia.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      abstract lia.
      apply tableSizeBigEnough.
      abstract lia. Qed.

    Lemma idxPPRsuccNotEqidxSh3 : PPRidx < tableSize - 1 ->
    exists succidx2 : index, StateLib.Index.succ PPRidx = Some succidx2 /\ (succidx2 = sh3idx -> False).
    Proof.
    unfold StateLib.Index.succ.
    case_eq (lt_dec (PPRidx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (PPRidx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(PPRidx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    abstract lia.
    unfold CIndex.
    case_eq(lt_dec (PPRidx + 1) tableSize ); intros.

     assert(Hi : {| i := PPRidx + 1; Hi := ADT.CIndex_obligation_1 (PPRidx + 1) l0 |} = sh3idx)
    by trivial.
    contradict Hi.
    subst.
    unfold PPRidx. unfold sh3idx.
    unfold CIndex at 3.
    case_eq (lt_dec 8 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 10 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *.
    inversion Hii.
    abstract lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract lia.
    abstract lia.
    abstract lia.
    Qed.

    Lemma idxSh3succNotEqPPRidx : sh3idx < tableSize - 1 ->
    exists succidx1 : index, StateLib.Index.succ sh3idx = Some succidx1 /\ (succidx1 = PPRidx -> False).
    Proof.
    unfold StateLib.Index.succ.
    case_eq (lt_dec (sh3idx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (sh3idx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(sh3idx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    abstract lia.
    unfold CIndex.
    case_eq(lt_dec (sh3idx + 1) tableSize ); intros.
     assert(Hi : {| i := sh3idx + 1; Hi := ADT.CIndex_obligation_1 (sh3idx + 1) l0 |} = PPRidx)
    by trivial.
    contradict Hi.
    subst.
    unfold sh3idx. unfold PPRidx.
    unfold CIndex at 3.
    case_eq (lt_dec 10 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 8 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *.
    inversion Hii.
    abstract lia.
    abstract lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract lia.
    abstract lia.
    Qed.

 Lemma idxPPRidxSh3NotEq : PPRidx <> sh3idx.
    Proof.
      unfold PPRidx. unfold sh3idx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      abstract lia.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      abstract lia.
       apply tableSizeBigEnough. abstract lia. Qed.

    Lemma idxSh3succNotEqPRidx : sh3idx < tableSize - 1 ->
    exists succidx2 : index, StateLib.Index.succ sh3idx = Some succidx2 /\ (succidx2 = PRidx -> False).
    Proof.
    unfold StateLib.Index.succ.
    case_eq (lt_dec (sh3idx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (sh3idx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(sh3idx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    abstract lia.
    unfold CIndex.
    case_eq(lt_dec (sh3idx + 1) tableSize ); intros.

     assert(Hi : {| i := sh3idx + 1; Hi := ADT.CIndex_obligation_1 (sh3idx + 1) l0 |} = PRidx)
    by trivial.
    contradict Hi.
    subst.
    unfold sh3idx. unfold PRidx.
    unfold CIndex at 3.
    case_eq (lt_dec 0 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 8 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *.
    inversion Hii.
    abstract lia.
    abstract lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract lia.
    abstract lia.
    Qed.

    Lemma idxPRsuccNotEqidxSh3 : PRidx < tableSize - 1 -> exists succidx1 : index, StateLib.Index.succ PRidx = Some succidx1 /\ (succidx1 = sh3idx -> False).
    Proof.
    unfold StateLib.Index.succ.
    case_eq (lt_dec (PRidx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (PRidx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(PRidx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    abstract lia.
    unfold CIndex.
    case_eq(lt_dec (PRidx + 1) tableSize ); intros.
    assert(Hi : {| i := PRidx + 1; Hi := ADT.CIndex_obligation_1 (PRidx + 1) l0 |} = sh3idx)
    by trivial.
    contradict Hi.
    subst.
    unfold sh3idx. unfold PRidx.
    unfold CIndex at 3.
    case_eq (lt_dec 8 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 0 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *.
    inversion Hii.
    abstract lia.
    abstract lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract lia.
    abstract lia.
    Qed.

    Lemma  idxPRidxSh3NotEq : PRidx <> sh3idx.
    Proof.
    (* *)
      unfold PRidx. unfold sh3idx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      abstract lia.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      abstract lia. apply tableSizeBigEnough. abstract lia. Qed.

    Lemma idxSh3succNotEqidxPDidx : sh3idx < tableSize - 1 ->
    exists succidx2 : index, StateLib.Index.succ sh3idx = Some succidx2 /\ (succidx2 = PDidx -> False).
    Proof.
    unfold StateLib.Index.succ.
    case_eq (lt_dec (sh3idx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (sh3idx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(sh3idx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    abstract lia.
    unfold CIndex.
    case_eq(lt_dec (sh3idx + 1) tableSize ); intros.
     assert(Hi : {| i := sh3idx + 1; Hi := ADT.CIndex_obligation_1 (sh3idx + 1) l0 |} = PDidx)
    by trivial.
    contradict Hi.
    subst.
    unfold PDidx. unfold sh3idx.
    unfold CIndex at 3.
    case_eq (lt_dec 2 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 8 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *.
    inversion Hii.
    abstract lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract lia.
    abstract lia.
    abstract lia.
    Qed.


    Lemma idxPDsucNotEqidxSh3 : PDidx < tableSize - 1 ->
    exists succidx1 : index, StateLib.Index.succ PDidx = Some succidx1 /\ (succidx1 = sh3idx -> False).
    Proof.
    unfold StateLib.Index.succ.
    case_eq (lt_dec (PDidx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (PDidx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(PDidx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    abstract lia.
    unfold CIndex.
    case_eq(lt_dec (PDidx + 1) tableSize ); intros.

     assert(Hi : {| i := PDidx + 1; Hi := ADT.CIndex_obligation_1 (PDidx + 1) l0 |} = sh3idx)
    by trivial.
    contradict Hi.
    subst.
    unfold sh3idx. unfold PDidx.
    unfold CIndex at 3.
    case_eq (lt_dec 8 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 2 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *.
    inversion Hii.
    abstract lia.
    abstract lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract lia.
    abstract lia.
    Qed.

    Lemma idxPDidxSh3notEq : PDidx <> sh3idx.
    Proof.
(*
 *)      unfold PDidx. unfold sh3idx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      abstract lia.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      abstract lia. apply tableSizeBigEnough. abstract lia.
      Qed.

    Lemma idxSh3succNotEqidxSh1 :
    sh3idx < tableSize - 1 ->
     exists succidx2 : index, StateLib.Index.succ sh3idx = Some succidx2 /\ (succidx2 = sh1idx -> False).
     Proof.
    unfold StateLib.Index.succ.
    case_eq (lt_dec (sh3idx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (sh3idx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(sh3idx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    lia.
    unfold CIndex.
    case_eq(lt_dec (sh3idx + 1) tableSize ); intros.

     assert(Hi : {| i := sh3idx + 1; Hi := ADT.CIndex_obligation_1 (sh3idx + 1) l0 |} = sh1idx)
    by trivial.
    contradict Hi.
    subst.
    unfold sh3idx. unfold sh1idx.
    unfold CIndex at 3.
    case_eq (lt_dec 4 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 8 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *.
    inversion Hii.
    lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    lia.
    lia.
    lia.
    Qed.
    Lemma sh1idxSh3idxNotEq : sh1idx < tableSize - 1 ->
    exists succidx1 : index, StateLib.Index.succ sh1idx = Some succidx1 /\ (succidx1 = sh3idx -> False).
    Proof.
    unfold StateLib.Index.succ.
    case_eq (lt_dec (sh1idx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (sh1idx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(sh1idx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    lia.
    unfold CIndex.
    case_eq(lt_dec (sh1idx + 1) tableSize ); intros.

     assert(Hi : {| i := sh1idx + 1; Hi := ADT.CIndex_obligation_1 (sh1idx + 1) l0 |} = sh3idx)
    by trivial.
    contradict Hi.
    subst.
    unfold sh1idx. unfold sh3idx.
    unfold CIndex at 3.
    case_eq (lt_dec 8 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 4 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *.
    inversion Hii.
    lia.
    lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    lia.
    lia.
    Qed.
    Lemma idxSh1idxSh3notEq :  sh1idx <> sh3idx.
     Proof.
      unfold sh1idx. unfold sh3idx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      lia.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      lia. apply tableSizeBigEnough. lia.
      Qed.

    Lemma idxSh3succNotEqidxSh2 : sh3idx < tableSize - 1 ->
    exists succidx2 : index, StateLib.Index.succ sh3idx = Some succidx2 /\ (succidx2 = sh2idx -> False).
    Proof.
    unfold StateLib.Index.succ.
    case_eq (lt_dec (sh3idx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (sh3idx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(sh3idx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    lia.
    unfold CIndex.
    case_eq(lt_dec (sh3idx + 1) tableSize ); intros.
    assert(Hi : {| i := sh3idx + 1; Hi := ADT.CIndex_obligation_1 (sh3idx + 1) l0 |} = sh2idx)
    by trivial.
    contradict Hi.
    subst.
    unfold sh3idx. unfold sh2idx.
    unfold CIndex at 3.
    case_eq (lt_dec 6 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 8 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *.
    inversion Hii.
    lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    lia.
    lia.
    lia.
    Qed.

    Lemma idxSh2succNotEqidxSh3 : sh2idx < tableSize - 1 ->
    exists succidx1 : index, StateLib.Index.succ sh2idx = Some succidx1 /\ (succidx1 = sh3idx -> False).
    Proof.
    unfold StateLib.Index.succ.
    case_eq (lt_dec (sh2idx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (sh2idx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(sh2idx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    lia.
    unfold CIndex.
    case_eq(lt_dec (sh2idx + 1) tableSize ); intros.
     assert(Hi : {| i := sh2idx + 1; Hi := ADT.CIndex_obligation_1 (sh2idx + 1) l0 |} = sh3idx)
    by trivial.
    contradict Hi.
    subst.
    unfold sh3idx. unfold sh2idx.
    unfold CIndex at 3.
    case_eq (lt_dec 8 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 6 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *.
    inversion Hii.
    lia.
    lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    lia.
    lia.
    Qed.

    Lemma idxSh2idxSh3notEq : sh2idx <> sh3idx .
    Proof.
      unfold sh2idx. unfold sh3idx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      lia.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      lia. apply tableSizeBigEnough. lia.
     Qed.

   Lemma  idxSh2succNotEqidxPR : sh2idx < tableSize - 1 ->
   exists succidx2 : index, StateLib.Index.succ sh2idx = Some succidx2 /\ (succidx2 = PRidx -> False).
   Proof.
    unfold StateLib.Index.succ.
    case_eq (lt_dec (sh2idx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (sh2idx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(sh2idx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    lia.
    unfold CIndex.
    case_eq(lt_dec (sh2idx + 1) tableSize ); intros.

     assert(Hi : {| i := sh2idx + 1; Hi := ADT.CIndex_obligation_1 (sh2idx + 1) l0 |} = PRidx)
    by trivial.
    contradict Hi.
    subst.
    unfold sh2idx. unfold PRidx.
    unfold CIndex at 3.
    case_eq (lt_dec 0 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 6 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *.
    inversion Hii.
    lia.
    lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    lia.
    lia.
    Qed.

        Lemma idxPRsuccNotEqidxSh2 : PRidx < tableSize - 1 ->
    exists succidx1 : index, StateLib.Index.succ PRidx = Some succidx1 /\ (succidx1 = sh2idx -> False).
    Proof.
    unfold StateLib.Index.succ.
    case_eq (lt_dec (PRidx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (PRidx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(PRidx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    lia.
    unfold CIndex.
    case_eq(lt_dec (PRidx + 1) tableSize ); intros.

     assert(Hi : {| i := PRidx + 1; Hi := ADT.CIndex_obligation_1 (PRidx + 1) l0 |} = sh2idx)
    by trivial.
    contradict Hi.
    subst.
    unfold sh2idx. unfold PRidx.
    unfold CIndex at 3.
    case_eq (lt_dec 6 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 0 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *.
    inversion Hii.
    lia.
    lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    lia.
    lia.
    Qed.
        Lemma idxPRidxSh2NotEq : PRidx <> sh2idx.
    Proof.
      unfold PRidx. unfold sh2idx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      lia.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      lia. apply tableSizeBigEnough. lia.
      Qed.

          Lemma idxSh2succNotEqidxPD : sh2idx < tableSize - 1 ->
     exists succidx2 : index, StateLib.Index.succ sh2idx = Some succidx2 /\ (succidx2 = PDidx -> False).
     Proof.
    unfold StateLib.Index.succ.
    case_eq (lt_dec (sh2idx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (sh2idx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(sh2idx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    lia.
    unfold CIndex.
    case_eq(lt_dec (sh2idx + 1) tableSize ); intros.
    assert(Hi : {| i := sh2idx + 1; Hi := ADT.CIndex_obligation_1 (sh2idx + 1) l0 |} = PDidx)
    by trivial.
    contradict Hi.
    subst.
    unfold sh2idx. unfold PDidx.
    unfold CIndex at 3.
    case_eq (lt_dec 2 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 6 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *.
    inversion Hii.
    lia.

    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    lia.
    lia.

    lia.
    Qed.

        Lemma idxPDsucNotEqidxSh2 :
    PDidx < tableSize - 1 ->
    exists succidx1 : index, StateLib.Index.succ PDidx = Some succidx1 /\ (succidx1 = sh2idx -> False).
    Proof.
    unfold StateLib.Index.succ.
    case_eq (lt_dec (PDidx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (PDidx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(PDidx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    lia.
    unfold CIndex.
    case_eq(lt_dec (PDidx + 1) tableSize ); intros.


    assert(Hi : {| i := PDidx + 1; Hi := ADT.CIndex_obligation_1 (PDidx + 1) l0 |} = sh2idx)
    by trivial.
    contradict Hi.
    subst.
    unfold sh2idx. unfold PDidx.
    unfold CIndex at 3.
    case_eq (lt_dec 6 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 2 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *.
    inversion Hii.
    lia.
    lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    lia.
    lia.
    Qed.


    Lemma idxPDidxSh2notEq : PDidx <> sh2idx .
    Proof.
      unfold PDidx. unfold sh2idx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      lia.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      lia. apply tableSizeBigEnough. lia. Qed.

          Lemma idxSh2succNotEqidxSh1 :
    sh2idx < tableSize - 1 ->
    exists succidx2 : index, StateLib.Index.succ sh2idx = Some succidx2 /\ (succidx2 = sh1idx -> False).
    Proof.
    unfold StateLib.Index.succ.
    case_eq (lt_dec (sh2idx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (sh2idx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(sh2idx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    lia.
    unfold CIndex.
    case_eq(lt_dec (sh2idx + 1) tableSize ); intros.
      assert(Hi : {| i := sh2idx + 1; Hi := ADT.CIndex_obligation_1 (sh2idx + 1) l0 |} = sh1idx)
    by trivial.
    contradict Hi.
    subst.
    unfold sh1idx. unfold sh2idx.
    unfold CIndex at 3.
    case_eq (lt_dec 4 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 6 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *.
    inversion Hii.
    lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    lia.
    lia.
    lia.
    Qed.


      Lemma idxSh1succNotEqidxSh2 :
    sh1idx < tableSize - 1 ->
    exists succidx1 : index, StateLib.Index.succ sh1idx = Some succidx1 /\ (succidx1 = sh2idx -> False).
    Proof.
    unfold StateLib.Index.succ.
    case_eq (lt_dec (sh1idx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (sh1idx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(sh1idx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    lia.
    unfold CIndex.
    case_eq(lt_dec (sh1idx + 1) tableSize ); intros.

     assert(Hi : {| i := sh1idx + 1; Hi := ADT.CIndex_obligation_1 (sh1idx + 1) l0 |} = sh2idx)
    by trivial.
    contradict Hi.
    subst.
    unfold sh1idx. unfold sh2idx.
    unfold CIndex at 3.
    case_eq (lt_dec 6 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 4 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *.
    inversion Hii.
    lia.
    lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    lia.
    lia.
    Qed.



    Lemma idxSh1succNotEqidxPR :
    sh1idx < tableSize - 1 ->
    exists succidx2 : index, StateLib.Index.succ sh1idx = Some succidx2 /\ (succidx2 = PRidx -> False).
    Proof.
    unfold StateLib.Index.succ.
    case_eq (lt_dec (sh1idx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (sh1idx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(sh1idx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    lia.
    unfold CIndex.
    case_eq(lt_dec (sh1idx + 1) tableSize ); intros.
    assert(Hi : {| i := sh1idx + 1; Hi := ADT.CIndex_obligation_1 (sh1idx + 1) l0 |} = PRidx)
    by trivial.
    contradict Hi.
    subst.
    unfold sh1idx. unfold PRidx.
    unfold CIndex at 3.
    case_eq (lt_dec 4 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 0 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *.
    inversion Hii.
    lia.
    lia.

    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    lia.
    lia.
    Qed.
        Lemma idxPRsuccNotEqidxSh1 :
    PRidx + 1 < tableSize ->
(*     PRidx + 1< tableSize - 1 ->  *)
    exists succidx1 : index, StateLib.Index.succ PRidx = Some succidx1 /\ (succidx1 = sh1idx -> False).
    Proof.
    unfold StateLib.Index.succ.
    case_eq (lt_dec (PRidx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (PRidx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(PRidx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    lia.
    unfold CIndex.
    case_eq(lt_dec (PRidx + 1) tableSize ); intros.
    assert(Hi : {| i := PRidx + 1; Hi := ADT.CIndex_obligation_1 (PRidx + 1) l0 |} = sh1idx)
    by trivial.
    contradict Hi.
    subst.
    unfold sh1idx. unfold PRidx.
    unfold CIndex at 3.
    case_eq (lt_dec 4 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 0 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *.
    inversion Hii.
    lia.
    lia.

    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    lia.
    lia.
    lia.
    Qed.
Lemma idxPRidxSh1NotEq : PRidx <> sh1idx.
    Proof.
      unfold PRidx. unfold sh1idx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      lia.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      lia. apply tableSizeBigEnough. lia.
      Qed.

          Lemma idxSh1succNotEqidxPD :
    sh1idx + 1 < tableSize ->
    exists succidx2 : index, StateLib.Index.succ sh1idx = Some succidx2 /\ (succidx2 = PDidx -> False).
    Proof.
    unfold StateLib.Index.succ.
    case_eq (lt_dec (sh1idx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (sh1idx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(sh1idx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    lia.
    unfold CIndex.
    case_eq(lt_dec (sh1idx + 1) tableSize ); intros.
    assert(Hi : {| i := sh1idx + 1; Hi := ADT.CIndex_obligation_1 (sh1idx + 1) l0 |} = PDidx)
    by trivial.
    contradict Hi.
    subst.
    unfold sh1idx. unfold PDidx.
    unfold CIndex at 3.
    case_eq (lt_dec 2 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 4 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *.
    inversion Hii.
    lia.
(*     lia.


    contradict H13.
    subst.
    unfold PDidx. unfold sh1idx.
    unfold CIndex at 3.
    case_eq (lt_dec 2 tableSize); intros.
    unfold not; intros.
    inversion H14.
    unfold CIndex in H16.
    case_eq(lt_dec 4 tableSize); intros; rewrite H15 in *.
    inversion H16. *)
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    lia.
    lia.
    lia.
    Qed.

        Lemma  idxPDsucNotEqidxSh1 :
    PDidx + 1 < tableSize ->
    exists succidx1 : index, StateLib.Index.succ PDidx = Some succidx1 /\ (succidx1 = sh1idx -> False).
    Proof.
    unfold StateLib.Index.succ.
    case_eq (lt_dec (PDidx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (PDidx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(PDidx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    lia.
    unfold CIndex.
    case_eq(lt_dec (PDidx + 1) tableSize ); intros.
    assert(Hi : {| i := PDidx + 1; Hi := ADT.CIndex_obligation_1 (PDidx + 1) l0 |} = sh1idx)
    by trivial.
    contradict Hi.
    subst.
    unfold sh1idx. unfold PDidx.
    unfold CIndex at 3.
    case_eq (lt_dec 4 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 2 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *.
    inversion Hii.
    lia.
    lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    lia.
    lia.
    Qed.



          Lemma idxPDsucNotEqidxPR :
    PDidx + 1 < tableSize ->
     exists succidx2 : index, StateLib.Index.succ PDidx = Some succidx2 /\ (succidx2 = PRidx -> False).
     Proof.
    unfold StateLib.Index.succ.
    case_eq (lt_dec (PDidx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (PDidx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(PDidx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    lia.
    unfold CIndex.
    case_eq(lt_dec (PDidx + 1) tableSize ); intros.

    assert(Hii : {| i := PDidx + 1; Hi := ADT.CIndex_obligation_1 (PDidx + 1) l0 |} = PRidx)

by trivial.
    contradict Hii.
    subst.
    unfold PDidx. unfold PRidx.
    unfold CIndex at 3.
    case_eq (lt_dec 0 tableSize); intros.
    unfold not; intros Hi.
    inversion Hi.
    assert(Hii : CIndex 2 + 1 = 0) by trivial.
    unfold CIndex in Hii.
    case_eq(lt_dec 0 tableSize); intros Hi1 Hi2;  rewrite Hi2 in *.
    inversion Hi.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    lia.
    lia.
    lia.
    lia.
    Qed.

        Lemma idxPRsucNotEqidxPD :
    PRidx + 1 < tableSize ->
    exists succidx1 : index, Index.succ PRidx = Some succidx1 /\ (succidx1 = PDidx -> False).
    Proof.
    unfold StateLib.Index.succ.
    case_eq (lt_dec (PRidx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (PRidx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(PRidx + 1) tableSize); intros * Hc2.
    f_equal.
    apply proof_irrelevance.
    lia.
    unfold CIndex.
    case_eq(lt_dec (PRidx + 1) tableSize ); intros * Hc3 Hc4.
    contradict Hc4.
    subst.
    unfold PDidx. unfold PRidx.
    unfold CIndex at 3.
    case_eq (lt_dec 2 tableSize); intros * Hc5.
    unfold not; intros Hc6.
    inversion Hc6 as [Hc7].
    unfold CIndex in Hc7.
    case_eq(lt_dec 0 tableSize); intros * Hc8; rewrite Hc8 in *.
    inversion Hc6.
    simpl in *.
    lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    subst.
    lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    lia.
    lia.

    lia.
    Qed.

        Lemma idxPRidxPDNotEq : PRidx <> PDidx.
    Proof.
      unfold PDidx. unfold PRidx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      lia.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      lia. apply tableSizeBigEnough. lia.
      Qed.
*)
Lemma paddrEqNatEqEquiv : forall (a b : paddr), eq (p a) (p b) <-> (eq a b).
Proof.
split.
intro.
destruct a; destruct b.
simpl in *.
subst.
f_equal. apply proof_irrelevance.

intro.
rewrite H.
reflexivity.
Qed.

Lemma paddrNeqNatNeqEquiv : forall (a b : paddr), (p a) <> (p b) <-> a <> b.
Proof.
intro; split; intro.
destruct a; destruct b.
cbn in *.
injection.
intro.
contradict H1.
assumption.

contradict H.
apply paddrEqNatEqEquiv; assumption.
Qed.


Lemma index0Ltfalse (idx:index):
idx < CIndex 0 -> False.
Proof.
intros.
unfold CIndex in H.
case_eq (le_dec 0 maxIdx).
intros.
rewrite H0 in H.
simpl in *. lia.
intros.
contradict H0.
assert (maxIdx > maxIdxLowerBound).
apply maxIdxBigEnough.
unfold maxIdxLowerBound in *.
lia.
Qed.


Lemma indexDecOrNot :
forall p1 p2 : index, p1 = p2 \/ p1<>p2.
Proof.
destruct p1;simpl in *;subst;destruct p2;simpl in *;subst.
assert (Heq :i=i0 \/ i<> i0) by lia.
destruct Heq as [Heq|Heq].
subst.
left;f_equal;apply proof_irrelevance.
right. unfold not;intros.
inversion H.
subst.
now contradict Heq.
Qed.

(*
Lemma getNbLevelEqNat : 
forall nbL, 
Some nbL = StateLib.getNbLevel -> 
nbLevel - 1 = nbL.
Proof.
intros.
unfold StateLib.getNbLevel in *.
destruct (gt_dec nbLevel 0).
inversion H.
destruct nbL.
simpl in *;trivial.
assert (0 < nbLevel) by apply nbLevelNotZero.
lia.
Qed.


Lemma level_eq_l:
forall x1 x2: level, l x1 = l x2 -> x1 = x2.
Proof.
intros.
destruct x1;destruct x2;simpl in *.
subst.
f_equal.
apply proof_irrelevance.
Qed.*)

Lemma index_eq_i:
forall x1 x2: index, i x1 =i x2 -> x1 = x2.
Proof.
intros.
destruct x1;destruct x2;simpl in *.
subst.
f_equal.
apply proof_irrelevance.
Qed.
