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
    In this file we formalize and prove the weakest precondition of the
    MAL and MALInternal functions *)
Require Import Model.ADT Model.Monad Model.MAL Model.Lib Proof.Consistency Model.MALInternal
Omega List StateLib Hoare.
Lemma ret  (A : Type) (a : A) (P : A -> state -> Prop) : {{ P a }} ret a {{ P }}.
Proof.
intros s H; trivial.
Qed.

Lemma bind  (A B : Type) (m : LLI A) (f : A -> LLI B) (P : state -> Prop)( Q : A -> state -> Prop) (R : B -> state -> Prop) :
  (forall a, {{ Q a }} f a {{ R }}) -> {{ P }} m {{ Q }} -> {{ P }} perform x := m in f x {{ R }}.
Proof.
intros H1 H2 s H3; unfold bind; case_eq (m s); [intros [a s'] H4 | intros k s' H4];
apply H2 in H3; rewrite H4 in H3; trivial.
case_eq (f a s'); [intros [b s''] H5 |  intros k s'' H5];
apply H1 in H3; rewrite H5 in H3; trivial.
Qed.

Lemma put  (s : state) (P : unit -> state -> Prop) : {{ fun _ => P tt s }} put s {{ P }}.
Proof.
intros s0 H;trivial.
Qed.

Lemma get  (P : state -> state -> Prop) : {{ fun s => P s s }} get {{ P }}.
Proof.
intros s H; trivial.
Qed.

Lemma undefined  (A : Type)(a : nat) (P : A -> state -> Prop) : {{ fun s => False }} undefined  a{{ P }}.
Proof.
intros s H; trivial.
Qed.

Lemma weaken (A : Type) (m : LLI A) (P Q : state -> Prop) (R : A -> state -> Prop) :
  {{ Q }} m {{ R }} -> (forall s, P s -> Q s) -> {{ P }} m {{ R }}.
Proof.
intros H1 H2 s H3.
case_eq (m s); [intros [a s'] H4 | intros a H4 ];
apply H2 in H3; apply H1 in H3; try rewrite H4 in H3; trivial.
intros. rewrite H in H3. assumption.
Qed.
Lemma strengthen (A : Type) (m : LLI A) (P: state -> Prop) (Q R: A -> state -> Prop) :
  {{ P }} m {{ R }} -> (forall s a, R a s -> Q a s) -> {{ P }} m {{ Q }}.
Proof.
intros H1 H2 s H3.
case_eq (m s);[ intros  [a s'] H4 | intros H4];
apply H1 in H3.
 rewrite H4 in H3; apply H2 in H3;trivial.
intros. rewrite H in H3. assumption.
Qed.


Lemma bindRev (A B : Type) (m : LLI A) (f : A -> LLI B) (P : state -> Prop)( Q : A -> state -> Prop) (R : B -> state -> Prop) :
  {{ P }} m {{ Q }} -> (forall a, {{ Q a }} f a {{ R }}) -> {{ P }} perform x := m in f x {{ R }}.
Proof.
intros; eapply bind ; eassumption.
Qed.

Lemma modify  f (P : unit -> state -> Prop) : {{ fun s => P tt (f s) }} modify f {{ P }}.
Proof.
unfold modify.
eapply bind .
intros.
eapply put .
simpl.
eapply weaken.
eapply get .
intros. simpl.
assumption.
Qed.


Lemma getCurPartition   (P: paddr -> state -> Prop) :
{{wp P MAL.getCurPartition}} MAL.getCurPartition {{P}}.
Proof.
apply wpIsPrecondition.
Qed.

Module Index.
(* COPY*)
Lemma ltb  index1 index2 (P : bool -> state -> Prop):
{{ fun s : state => P (StateLib.Index.ltb index1 index2)  s }} 
  MALInternal.Index.ltb index1 index2 {{ fun s => P s}}.
Proof.
unfold MALInternal.Index.ltb, StateLib.Index.ltb.
eapply weaken.
eapply ret .
trivial.
Qed.

(* COPY *)
Lemma leb  index1 index2 (P : bool -> state -> Prop):
{{ fun s : state => P (StateLib.Index.leb index1 index2)  s }} 
  MALInternal.Index.leb index1 index2 {{ fun s => P s}}.
Proof.
unfold MALInternal.Index.leb, StateLib.Index.leb.
eapply weaken.
eapply ret .
trivial.
Qed.

Lemma pred  (n : index) (P: index -> state -> Prop) :
{{ fun s : state => n > 0 /\ forall Hi : n - 1 < maxIdx,  
                   P {| i := n -1; Hi := Hi |} s }}
MALInternal.Index.pred n
{{ P }}.
Proof.
unfold MALInternal.Index.pred.
destruct n.
destruct i.
simpl.
case_eq (lt_dec 0 maxIdx).
intros. eapply weaken. apply ret. intros. omega.
intros. eapply weaken. apply undefined. intros. simpl. congruence.
simpl.
case_eq (lt_dec (i - 0) maxIdx).
intros. simpl. eapply weaken. apply ret.
intros. simpl. intuition.
intros. eapply weaken. apply undefined. intros. simpl. intuition.
Qed.

End Index.

Module Paddr.
(* DUP *)
Lemma leb  addr1 addr2 (P : bool -> state -> Prop):
{{ fun s : state => P (StateLib.Paddr.leb addr1 addr2)  s }} 
  MALInternal.Paddr.leb addr1 addr2 {{ fun s => P s}}.
Proof.
unfold MALInternal.Paddr.leb, StateLib.Paddr.leb.
eapply weaken.
eapply ret .
trivial.
Qed.

Lemma subPaddr  (addr1 addr2 : paddr) (P : index -> state -> Prop):
{{ fun s : state => addr1 >= 0 /\ addr2 >= 0 /\ addr1 - addr2 < maxIdx /\ forall Hi : addr1 - addr2 < maxIdx,  
                   P {| i := addr1 - addr2; Hi := Hi |} s }}
MALInternal.Paddr.subPaddr addr1 addr2
{{ P }}.
Proof.
unfold MALInternal.Paddr.subPaddr.
destruct addr1.
destruct addr2.
simpl.
case_eq ( lt_dec (p - p0) maxIdx) .
intros.
eapply weaken.
eapply ret .
intros. intuition.
intros. eapply weaken.
eapply undefined .
simpl. intros.
destruct H0. destruct H1.
destruct H2.
congruence.
Qed.

(* DUP*)
Lemma subPaddrIdx  (n : paddr) (m: index) (P: paddr -> state -> Prop) :
{{ fun s : state => n >= 0 /\ m >= 0 /\ forall Hp : n - m < maxAddr,  
                   P {| p := n -m; Hp := Hp |} s }} MALInternal.Paddr.subPaddrIdx n m {{ P }}.
Proof.
unfold MALInternal.Paddr.subPaddrIdx.
destruct n.
simpl.
case_eq (lt_dec (p - m) maxAddr) .
intros.
eapply weaken.
eapply ret .
intros. intuition.
intros. eapply weaken.
eapply undefined .
simpl. intros.
omega.
Qed.

(* DUP *)
Lemma pred  (n : paddr) (P: paddr -> state -> Prop) :
{{ fun s : state => n > 0 /\ forall Hp : n - 1 < maxAddr,  
                   P {| p := n -1; Hp := Hp |} s }}
MALInternal.Paddr.pred n
{{ P }}.
Proof.
unfold MALInternal.Paddr.pred.
destruct n.
destruct p.
simpl.
case_eq (lt_dec 0 maxAddr).
intros. eapply weaken. apply ret. intros. omega.
intros. eapply weaken. apply undefined. intros. simpl. congruence.
simpl.
case_eq (lt_dec (p - 0) maxAddr).
intros. simpl. eapply weaken. apply ret.
intros. simpl. intuition.
intros. eapply weaken. apply undefined. intros. simpl. intuition.
Qed.

End Paddr.


(* COPY *)
Lemma writeBlockAccessibleFromBlockEntryAddr  (entryaddr : paddr) (flag : bool)  (P : unit -> state -> Prop) :
{{fun  s => exists entry , lookup entryaddr s.(memory) beqAddr = Some (BE entry) /\ 
P tt {|
  currentPartition := currentPartition s;
  memory := add entryaddr
              (*(BE {| read := entry.(read); write :=entry.(write); exec := entry.(exec); 
                     present := entry.(present); accessible := flag;
											blockindex := entry.(blockindex) ; blockrange := entry.(blockrange) ;
										Hidx := entry.(Hidx) |})*)
								(BE (CBlockEntry 	entry.(read) entry.(write) entry.(exec)
																	entry.(present) flag
																	entry.(blockindex) entry.(blockrange)))
              (memory s) beqAddr |} }} writeBlockAccessibleFromBlockEntryAddr entryaddr flag  {{P}}.
Proof.
unfold writeBlockAccessibleFromBlockEntryAddr.
eapply bind .
  - intro s. simpl.
   case_eq (lookup entryaddr s.(memory) beqAddr).
     + intros v Hpage.
       instantiate (1:= fun s s0 => s = s0 /\ exists entry , lookup entryaddr s.(memory) beqAddr = Some (BE entry) /\ 
                                              P tt {| currentPartition := currentPartition s;
                                                      memory := add entryaddr
                                                                  (*(BE {| read := entry.(read); write :=entry.(write); exec := entry.(exec); 
																																				 present := entry.(present); accessible := flag;
																																					blockindex := entry.(blockindex) ; blockrange := entry.(blockrange) ;
																																					Hidx := entry.(Hidx) |})*)
																							(BE (CBlockEntry entry.(read) entry.(write) entry.(exec)
																													entry.(present) flag
																													entry.(blockindex) entry.(blockrange)))
                                                                  (memory s) beqAddr |}).
       simpl in *.
       case_eq v; intros; eapply weaken; try eapply undefined ;simpl;
       subst;
       cbn; intros;
       try destruct H as (Hs & x & H1 & Hp); subst;
       try rewrite H1 in Hpage; inversion Hpage; subst; try assumption.
       eapply modify .
       intros.
       simpl.
       assumption.
     + intros Hpage; eapply weaken; try eapply undefined ;simpl.
       intros s0 H0. destruct H0 as (Hs & x & H1 & Hp).
       rewrite H1 in Hpage.
       inversion Hpage.
  - eapply weaken. eapply get . intuition.
Qed.

Lemma writeBlockPresentFromBlockEntryAddr  (entryaddr : paddr) (flag : bool)  (P : unit -> state -> Prop) :
{{fun  s => exists entry , lookup entryaddr s.(memory) beqAddr = Some (BE entry) /\ 
P tt {|
  currentPartition := currentPartition s;
  memory := add entryaddr
              (*(BE {| read := entry.(read); write :=entry.(write); exec := entry.(exec); 
                     present := flag; accessible := entry.(accessible);
											blockindex := entry.(blockindex) ; blockrange := entry.(blockrange) |})*)
								(BE (CBlockEntry 	entry.(read) entry.(write) entry.(exec)
																	flag entry.(accessible)
																	entry.(blockindex) entry.(blockrange)))
              (memory s) beqAddr |} }} writeBlockPresentFromBlockEntryAddr entryaddr flag  {{P}}.
Proof.
unfold writeBlockPresentFromBlockEntryAddr.
eapply bind .
  - intro s. simpl.
   case_eq (lookup entryaddr s.(memory) beqAddr).
     + intros v Hpage.
       instantiate (1:= fun s s0 => s = s0 /\ exists entry , lookup entryaddr s.(memory) beqAddr = Some (BE entry) /\ 
                                              P tt {| currentPartition := currentPartition s;
                                                      memory := add entryaddr
                                                                  (*(BE {| read := entry.(read); write :=entry.(write); exec := entry.(exec); 
																																				 present := flag; accessible := entry.(accessible) ;
																																					blockindex := entry.(blockindex) ; blockrange := entry.(blockrange) |})*)
																																	(BE (CBlockEntry 	entry.(read) entry.(write) entry.(exec)
																																										flag entry.(accessible)
																																										entry.(blockindex) entry.(blockrange)))
                                                                  (memory s) beqAddr |}).
       simpl in *.
       case_eq v; intros; eapply weaken; try eapply undefined ;simpl;
       subst;
       cbn; intros;
       try destruct H as (Hs & x & H1 & Hp); subst;
       try rewrite H1 in Hpage; inversion Hpage; subst; try assumption.
       eapply modify .
       intros.
       simpl.
       assumption.
     + intros Hpage; eapply weaken; try eapply undefined ;simpl.
       intros s0 H0. destruct H0 as (Hs & x & H1 & Hp).
       rewrite H1 in Hpage.
       inversion Hpage.
  - eapply weaken. eapply get . intuition.
Qed.

(* COPY *)
Lemma writeBlockRFromBlockEntryAddr  (entryaddr : paddr) (flag : bool)  (P : unit -> state -> Prop) :
{{fun  s => exists entry , lookup entryaddr s.(memory) beqAddr = Some (BE entry) /\ 
P tt {|
  currentPartition := currentPartition s;
  memory := add entryaddr
								(BE (CBlockEntry 	flag entry.(write) entry.(exec)
																	entry.(present) entry.(accessible)
																	entry.(blockindex) entry.(blockrange)))
              (memory s) beqAddr |} }}
writeBlockRFromBlockEntryAddr entryaddr flag  {{P}}.
Proof.
unfold writeBlockRFromBlockEntryAddr.
eapply bind .
  - intro s. simpl.
   case_eq (lookup entryaddr s.(memory) beqAddr).
     + intros v Hpage.
       instantiate (1:= fun s s0 => s = s0 /\ exists entry , lookup entryaddr s.(memory) beqAddr = Some (BE entry) /\ 
                                              P tt {| currentPartition := currentPartition s;
                                                      memory := add entryaddr
                                                             (BE (CBlockEntry 	flag entry.(write) entry.(exec)
																	entry.(present) entry.(accessible)
																	entry.(blockindex) entry.(blockrange)))
                                                                  (memory s) beqAddr |}).
       simpl in *.
       case_eq v; intros; eapply weaken; try eapply undefined ;simpl;
       subst;
       cbn; intros;
       try destruct H as (Hs & x & H1 & Hp); subst;
       try rewrite H1 in Hpage; inversion Hpage; subst; try assumption.
       eapply modify .
       intros.
       simpl.
       assumption.
     + intros Hpage; eapply weaken; try eapply undefined ;simpl.
       intros s0 H0. destruct H0 as (Hs & x & H1 & Hp).
       rewrite H1 in Hpage.
       inversion Hpage.
  - eapply weaken. eapply get . intuition.
Qed.


(* COPY *)
Lemma writeBlockWFromBlockEntryAddr  (entryaddr : paddr) (flag : bool)  (P : unit -> state -> Prop) :
{{fun  s => exists entry , lookup entryaddr s.(memory) beqAddr = Some (BE entry) /\ 
P tt {|
  currentPartition := currentPartition s;
  memory := add entryaddr
								(BE (CBlockEntry 	entry.(read) flag entry.(exec)
																	entry.(present) entry.(accessible)
																	entry.(blockindex) entry.(blockrange)))
              (memory s) beqAddr |} }}
writeBlockWFromBlockEntryAddr entryaddr flag  {{P}}.
Proof.
unfold writeBlockWFromBlockEntryAddr.
eapply bind .
  - intro s. simpl.
   case_eq (lookup entryaddr s.(memory) beqAddr).
     + intros v Hpage.
       instantiate (1:= fun s s0 => s = s0 /\ exists entry , lookup entryaddr s.(memory) beqAddr = Some (BE entry) /\ 
                                              P tt {| currentPartition := currentPartition s;
                                                      memory := add entryaddr
                                                             (BE (CBlockEntry 	entry.(read) flag entry.(exec)
																	entry.(present) entry.(accessible)
																	entry.(blockindex) entry.(blockrange)))
                                                                  (memory s) beqAddr |}).
       simpl in *.
       case_eq v; intros; eapply weaken; try eapply undefined ;simpl;
       subst;
       cbn; intros;
       try destruct H as (Hs & x & H1 & Hp); subst;
       try rewrite H1 in Hpage; inversion Hpage; subst; try assumption.
       eapply modify .
       intros.
       simpl.
       assumption.
     + intros Hpage; eapply weaken; try eapply undefined ;simpl.
       intros s0 H0. destruct H0 as (Hs & x & H1 & Hp).
       rewrite H1 in Hpage.
       inversion Hpage.
  - eapply weaken. eapply get . intuition.
Qed.

(* COPY *)
Lemma writeBlockXFromBlockEntryAddr  (entryaddr : paddr) (flag : bool)  (P : unit -> state -> Prop) :
{{fun  s => exists entry , lookup entryaddr s.(memory) beqAddr = Some (BE entry) /\ 
P tt {|
  currentPartition := currentPartition s;
  memory := add entryaddr
								(BE (CBlockEntry 	entry.(read) entry.(write) flag
																	entry.(present) entry.(accessible)
																	entry.(blockindex) entry.(blockrange)))
              (memory s) beqAddr |} }}
writeBlockXFromBlockEntryAddr entryaddr flag  {{P}}.
Proof.
unfold writeBlockXFromBlockEntryAddr.
eapply bind .
  - intro s. simpl.
   case_eq (lookup entryaddr s.(memory) beqAddr).
     + intros v Hpage.
       instantiate (1:= fun s s0 => s = s0 /\ exists entry , lookup entryaddr s.(memory) beqAddr = Some (BE entry) /\ 
                                              P tt {| currentPartition := currentPartition s;
                                                      memory := add entryaddr
                                                             (BE (CBlockEntry 	entry.(read) entry.(write) flag
																	entry.(present) entry.(accessible)
																	entry.(blockindex) entry.(blockrange)))
                                                                  (memory s) beqAddr |}).
       simpl in *.
       case_eq v; intros; eapply weaken; try eapply undefined ;simpl;
       subst;
       cbn; intros;
       try destruct H as (Hs & x & H1 & Hp); subst;
       try rewrite H1 in Hpage; inversion Hpage; subst; try assumption.
       eapply modify .
       intros.
       simpl.
       assumption.
     + intros Hpage; eapply weaken; try eapply undefined ;simpl.
       intros s0 H0. destruct H0 as (Hs & x & H1 & Hp).
       rewrite H1 in Hpage.
       inversion Hpage.
  - eapply weaken. eapply get . intuition.
Qed.

(* COPY *)
Lemma writeBlockEndFromBlockEntryAddr  (entryaddr : paddr) (newendaddr : ADT.paddr)  (P : unit -> state -> Prop) :
{{fun  s => exists entry , lookup entryaddr s.(memory) beqAddr = Some (BE entry) /\ 
P tt {|
  currentPartition := currentPartition s;
  memory := add entryaddr
								(BE (CBlockEntry 	entry.(read) entry.(write) entry.(exec)
																	entry.(present) entry.(accessible)
																	entry.(blockindex) (CBlock entry.(blockrange).(startAddr) newendaddr)))
              (memory s) beqAddr |} }}
writeBlockEndFromBlockEntryAddr entryaddr newendaddr  {{P}}.
Proof.
unfold writeBlockEndFromBlockEntryAddr.
eapply bind .
  - intro s. simpl.
   case_eq (lookup entryaddr s.(memory) beqAddr).
     + intros v Hpage.
       instantiate (1:= fun s s0 => s = s0 /\ exists entry , lookup entryaddr s.(memory) beqAddr = Some (BE entry) /\ 
                                              P tt {| currentPartition := currentPartition s;
                                                      memory := add entryaddr
                                                            (BE (CBlockEntry 	entry.(read) entry.(write) entry.(exec)
																	entry.(present) entry.(accessible)
																	entry.(blockindex) (CBlock entry.(blockrange).(startAddr) newendaddr)))
                                                                  (memory s) beqAddr |}).
       simpl in *.
       case_eq v; intros; eapply weaken; try eapply undefined ;simpl;
       subst;
       cbn; intros;
       try destruct H as (Hs & x & H1 & Hp); subst;
       try rewrite H1 in Hpage; inversion Hpage; subst; try assumption.
       eapply modify .
       intros.
       simpl.
       assumption.
     + intros Hpage; eapply weaken; try eapply undefined ;simpl.
       intros s0 H0. destruct H0 as (Hs & x & H1 & Hp).
       rewrite H1 in Hpage.
       inversion Hpage.
  - eapply weaken. eapply get . intuition.
Qed.

(* COPY *)
Lemma writeBlockStartFromBlockEntryAddr  (entryaddr : paddr) (newstartaddr : ADT.paddr)  (P : unit -> state -> Prop) :
{{fun  s => exists entry , lookup entryaddr s.(memory) beqAddr = Some (BE entry) /\ 
P tt {|
  currentPartition := currentPartition s;
  memory := add entryaddr
								(BE (CBlockEntry 	entry.(read) entry.(write) entry.(exec)
																	entry.(present) entry.(accessible)
																	entry.(blockindex) (CBlock newstartaddr entry.(blockrange).(endAddr))))
              (memory s) beqAddr |} }}
writeBlockStartFromBlockEntryAddr entryaddr newstartaddr  {{P}}.
Proof.
unfold writeBlockStartFromBlockEntryAddr.
eapply bind .
  - intro s. simpl.
   case_eq (lookup entryaddr s.(memory) beqAddr).
     + intros v Hpage.
       instantiate (1:= fun s s0 => s = s0 /\ exists entry , lookup entryaddr s.(memory) beqAddr = Some (BE entry) /\ 
                                              P tt {| currentPartition := currentPartition s;
                                                      memory := add entryaddr
                                                            (BE (CBlockEntry 	entry.(read) entry.(write) entry.(exec)
																	entry.(present) entry.(accessible)
																	entry.(blockindex) (CBlock newstartaddr entry.(blockrange).(endAddr))))
                                                                  (memory s) beqAddr |}).
       simpl in *.
       case_eq v; intros; eapply weaken; try eapply undefined ;simpl;
       subst;
       cbn; intros;
       try destruct H as (Hs & x & H1 & Hp); subst;
       try rewrite H1 in Hpage; inversion Hpage; subst; try assumption.
       eapply modify .
       intros.
       simpl.
       assumption.
     + intros Hpage; eapply weaken; try eapply undefined ;simpl.
       intros s0 H0. destruct H0 as (Hs & x & H1 & Hp).
       rewrite H1 in Hpage.
       inversion Hpage.
  - eapply weaken. eapply get . intuition.
Qed.

(* COPY *)
Lemma writePDFirstFreeSlotPointer  (entryaddr : paddr) (pointer : paddr)  (P : unit -> state -> Prop) :
{{fun  s => exists entry , lookup entryaddr s.(memory) beqAddr = Some (PDT entry) /\ 
P tt {|
  currentPartition := currentPartition s;
  memory := add entryaddr
              (PDT {| structure := entry.(structure); firstfreeslot := pointer; nbfreeslots := entry.(nbfreeslots); 
                     nbprepare := entry.(nbprepare); parent := entry.(parent);
											MPU := entry.(MPU) |})
              (memory s) beqAddr |} }} writePDFirstFreeSlotPointer entryaddr pointer  {{P}}.
Proof.
unfold writePDFirstFreeSlotPointer.
eapply bind .
  - intro s. simpl.
   case_eq (lookup entryaddr s.(memory) beqAddr).
     + intros v Hpage.
       instantiate (1:= fun s s0 => s = s0 /\ exists entry , lookup entryaddr s.(memory) beqAddr = Some (PDT entry) /\ 
                                              P tt {| currentPartition := currentPartition s;
                                                      memory := add entryaddr
                                                                  (PDT {| structure := entry.(structure); firstfreeslot := pointer; nbfreeslots := entry.(nbfreeslots); 
																																				 nbprepare := entry.(nbprepare); parent := entry.(parent);
																																					MPU := entry.(MPU) |})
                                                                  (memory s) beqAddr |}).
       simpl in *.
       case_eq v; intros; eapply weaken; try eapply undefined ;simpl;
       subst;
       cbn; intros;
       try destruct H as (Hs & x & H1 & Hp); subst;
       try rewrite H1 in Hpage; inversion Hpage; subst; try assumption.
       eapply modify .
       intros.
       simpl.
       assumption.
     + intros Hpage; eapply weaken; try eapply undefined ;simpl.
       intros s0 H0. destruct H0 as (Hs & x & H1 & Hp).
       rewrite H1 in Hpage.
       inversion Hpage.
  - eapply weaken. eapply get . intuition.
Qed.

(* COPY *)
Lemma writePDNbFreeSlots  (entryaddr: paddr) (nbfreeslots : index)  (P : unit -> state -> Prop) :
{{fun  s => exists entry , lookup entryaddr s.(memory) beqAddr = Some (PDT entry) /\ 
P tt {|
  currentPartition := currentPartition s;
  memory := add entryaddr
              (PDT {| structure := entry.(structure); firstfreeslot := entry.(firstfreeslot) ; nbfreeslots := nbfreeslots; 
                     nbprepare := entry.(nbprepare); parent := entry.(parent);
											MPU := entry.(MPU) |})
              (memory s) beqAddr |} }}
writePDNbFreeSlots entryaddr nbfreeslots  {{P}}.
Proof.
unfold writePDNbFreeSlots.
eapply bind .
  - intro s. simpl.
   case_eq (lookup entryaddr s.(memory) beqAddr).
     + intros v Hpage.
       instantiate (1:= fun s s0 => s = s0 /\ exists entry , lookup entryaddr s.(memory) beqAddr = Some (PDT entry) /\ 
                                              P tt {| currentPartition := currentPartition s;
                                                      memory := add entryaddr
                                                                  (PDT {| structure := entry.(structure); firstfreeslot := entry.(firstfreeslot) ; nbfreeslots := nbfreeslots; 
                     nbprepare := entry.(nbprepare); parent := entry.(parent);
											MPU := entry.(MPU) |})
                                                                  (memory s) beqAddr |}).
       simpl in *.
       case_eq v; intros; eapply weaken; try eapply undefined ;simpl;
       subst;
       cbn; intros;
       try destruct H as (Hs & x & H1 & Hp); subst;
       try rewrite H1 in Hpage; inversion Hpage; subst; try assumption.
       eapply modify .
       intros.
       simpl.
       assumption.
     + intros Hpage; eapply weaken; try eapply undefined ;simpl.
       intros s0 H0. destruct H0 as (Hs & x & H1 & Hp).
       rewrite H1 in Hpage.
       inversion Hpage.
  - eapply weaken. eapply get . intuition.
Qed.

(* COPY *)
Lemma writePDMPU (pdtablepaddr : paddr) (MPUlist : list paddr) (P : unit -> state -> Prop) :
{{fun  s => exists entry , lookup pdtablepaddr s.(memory) beqAddr = Some (PDT entry) /\
P tt {|
  currentPartition := currentPartition s;
  memory := add pdtablepaddr
              (PDT {| structure := entry.(structure); firstfreeslot := entry.(firstfreeslot) ; nbfreeslots := entry.(nbfreeslots);
                     nbprepare := entry.(nbprepare); parent := entry.(parent);
											MPU := MPUlist |})
              (memory s) beqAddr |} }}
writePDMPU pdtablepaddr MPUlist  {{P}}.
Proof.
unfold writePDMPU.
eapply bind .
  - intro s. simpl.
   case_eq (lookup pdtablepaddr s.(memory) beqAddr).
     + intros v Hpage.
       instantiate (1:= fun s s0 => s = s0 /\ exists entry , lookup pdtablepaddr s.(memory) beqAddr = Some (PDT entry) /\
                                              P tt {| currentPartition := currentPartition s;
                                                      memory := add pdtablepaddr
                                                                  (PDT {| structure := entry.(structure); firstfreeslot := entry.(firstfreeslot) ; nbfreeslots := entry.(nbfreeslots);
                     nbprepare := entry.(nbprepare); parent := entry.(parent);
											MPU := MPUlist |})
                                                                  (memory s) beqAddr |}).
       simpl in *.
       case_eq v; intros; eapply weaken; try eapply undefined ;simpl;
       subst;
       cbn; intros;
       try destruct H as (Hs & x & H1 & Hp); subst;
       try rewrite H1 in Hpage; inversion Hpage; subst; try assumption.
       eapply modify .
       intros.
       simpl.
       assumption.
     + intros Hpage; eapply weaken; try eapply undefined ;simpl.
       intros s0 H0. destruct H0 as (Hs & x & H1 & Hp).
       rewrite H1 in Hpage.
       inversion Hpage.
  - eapply weaken. eapply get . intuition.
Qed.

(* DUP local changes *)
Lemma getBlockRecordField {X : Type } field blockentryaddr (P : X -> state -> Prop) :
{{fun s =>  exists entry, lookup blockentryaddr s.(memory) beqAddr = Some (BE entry) /\
             P entry.(field) s }}
MAL.getBlockRecordField field blockentryaddr {{P}}.
Proof.
unfold MAL.getBlockRecordField.
eapply bind .
  - intro s.
    case_eq (lookup blockentryaddr (memory s) beqAddr).
     + intros v Hpage.
       instantiate (1:= fun s s0 => s=s0 /\ exists p1 ,
                   lookup blockentryaddr s.(memory) beqAddr =
                   Some (BE p1) /\ P (field p1) s).
			simpl.
      case_eq v; intros; eapply weaken; try eapply undefined ;simpl;
			intros s1 H0; try destruct H0 as (Hs & p1 & Hpage' & Hret);
			try rewrite Hpage in Hpage';
			subst; try inversion Hpage';
			try eassumption.
 			unfold Monad.ret.
       eassumption.
     + intros Hpage; eapply weaken; try eapply undefined ;simpl.
       intros s0 H0.  destruct H0 as (Hs & p1 & Hpage' & Hret) .
       rewrite Hpage in Hpage'.
       subst. inversion Hpage'.
  - eapply weaken.
   eapply get . intuition.
Qed.

(* DUP local changes *)
Lemma getPDTRecordField {X : Type } field pd (P : X -> state -> Prop) :
{{fun s =>  exists entry, lookup pd s.(memory) beqAddr = Some (PDT entry) /\
             P entry.(field) s }}
getPDTRecordField field pd {{P}}.
Proof.
unfold getPDTRecordField.
eapply bind .
  - intro s.
    case_eq (lookup pd (memory s) beqAddr).
     + intros v Hpage.
       instantiate (1:= fun s s0 => s=s0 /\ exists p1 ,
                   lookup pd s.(memory) beqAddr =
                   Some (PDT p1) /\ P (field p1) s).
			simpl.
      case_eq v; intros; eapply weaken; try eapply undefined ;simpl;
			intros s1 H0; try destruct H0 as (Hs & p1 & Hpage' & Hret);
			try rewrite Hpage in Hpage';
			subst; try inversion Hpage';
			try eassumption.
 			unfold Monad.ret.
       eassumption.
     + intros Hpage; eapply weaken; try eapply undefined ;simpl.
       intros s0 H0.  destruct H0 as (Hs & p1 & Hpage' & Hret) .
       rewrite Hpage in Hpage'.
       subst. inversion Hpage'.
  - eapply weaken.
   eapply get . intuition.
Qed.

(* DUP local changes *)
Lemma getSh1RecordField {X : Type } field sh1entryaddr (P : X -> state -> Prop) :
{{fun s =>  exists sh1entry : Sh1Entry, lookup sh1entryaddr s.(memory) beqAddr = Some (SHE sh1entry) /\
             P sh1entry.(field) s }}
getSh1RecordField field sh1entryaddr {{P}}.
Proof.
unfold getSh1RecordField.
eapply bind .
  - intro s.
    case_eq (lookup sh1entryaddr (memory s) beqAddr).
     + intros v Hpage.
       instantiate (1:= fun s s0 => s=s0 /\ exists p1 ,
                   lookup sh1entryaddr s.(memory) beqAddr =
                   Some (SHE p1) /\ P (field p1) s).
			simpl.
      case_eq v; intros; eapply weaken; try eapply undefined ;simpl;
			intros s1 H0; try destruct H0 as (Hs & p1 & Hpage' & Hret);
			try rewrite Hpage in Hpage';
			subst; try inversion Hpage';
			try eassumption.
 			unfold Monad.ret.
       eassumption.
     + intros Hpage; eapply weaken; try eapply undefined ;simpl.
       intros s0 H0.  destruct H0 as (Hs & p1 & Hpage' & Hret) .
       rewrite Hpage in Hpage'.
       subst. inversion Hpage'.
  - eapply weaken.
   eapply get . intuition.
Qed.

(* DUP local changes *)
Lemma getSCRecordField {X : Type } field scentryaddr (P : X -> state -> Prop) :
{{fun s =>  exists scentry : SCEntry, lookup scentryaddr s.(memory) beqAddr = Some (SCE scentry) /\
             P scentry.(field) s }}
getSCRecordField field scentryaddr {{P}}.
Proof.
unfold getSCRecordField.
eapply bind .
  - intro s.
    case_eq (lookup scentryaddr (memory s) beqAddr).
     + intros v Hpage.
       instantiate (1:= fun s s0 => s=s0 /\ exists p1 ,
                   lookup scentryaddr s.(memory) beqAddr =
                   Some (SCE p1) /\ P (field p1) s).
			simpl.
      case_eq v; intros; eapply weaken; try eapply undefined ;simpl;
			intros s1 H0; try destruct H0 as (Hs & p1 & Hpage' & Hret);
			try rewrite Hpage in Hpage';
			subst; try inversion Hpage';
			try eassumption.
 			unfold Monad.ret.
       eassumption.
     + intros Hpage; eapply weaken; try eapply undefined ;simpl.
       intros s0 H0.  destruct H0 as (Hs & p1 & Hpage' & Hret) .
       rewrite Hpage in Hpage'.
       subst. inversion Hpage'.
  - eapply weaken.
   eapply get . intuition.
Qed.

(* DUP *)
Lemma readNextFromKernelStructureStart2  (nextaddr : paddr) (P : paddr -> state -> Prop) :
{{fun s  =>  exists addrentry : paddr, lookup nextaddr s.(memory) beqAddr = Some (PADDR addrentry)
             /\ P addrentry s }}
MAL.readNextFromKernelStructureStart2 nextaddr
{{P}}.
Proof.
unfold MAL.readNextFromKernelStructureStart2.
eapply bind .
  - intro s.
    case_eq (lookup nextaddr (memory s) beqAddr).
     + intros v Hpage.
       instantiate (1:= fun s s0 => s=s0 /\ exists p1 ,
                    lookup nextaddr s.(memory) beqAddr =
                    Some (PADDR p1) /\ P p1 s).
 			simpl.
       case_eq v; intros; eapply weaken; try eapply undefined ;simpl;
 			intros s1 H0; try destruct H0 as (Hs & p1 & Hpage' & Hret);
 			try rewrite Hpage in Hpage';
 			subst; try inversion Hpage';
 			try eassumption.
 			unfold Monad.ret.
       eassumption.
     + intros Hpage; eapply weaken; try eapply undefined ;simpl.
       intros s0 H0.  destruct H0 as (Hs & p1 & Hpage' & Hret) .
       rewrite Hpage in Hpage'.
       subst. inversion Hpage'.
  - eapply weaken.
    eapply get . intuition.
Qed.

Lemma WPsubPaddrIdx  (n : paddr) (m: index) (P: paddr -> state -> Prop) :
{{ wp P (MALInternal.Paddr.subPaddrIdx n m)}} MALInternal.Paddr.subPaddrIdx n m{{ P }}.
Proof.
apply wpIsPrecondition.
Qed.

Lemma subPaddrIdx  (n : paddr) (m: index)
																	(P : paddr -> state -> Prop) : 
{{fun s => P n s}}
MALInternal.Paddr.subPaddrIdx n m
{{P}}.
Proof.
Admitted.
(*
eapply weaken.
apply WPsubPaddrIdx.
intros. unfold wp. destruct (Paddr.subPaddrIdx n m s) eqn:sub.
destruct p. intuition. unfold val in sub. eapply (H p s0). assert(H2 := conj p s0 H).*)


Lemma getSh1EntryAddrFromKernelStructureStart  (kernelStartAddr : paddr) (BlockEntryIndex : index)
																	(P : paddr -> state -> Prop) : 
{{fun s =>  wellFormedFstShadowIfBlockEntry s /\ exists entry, lookup kernelStartAddr s.(memory) beqAddr = Some (BE entry)
					/\ P (CPaddr (kernelStartAddr + sh1offset + BlockEntryIndex)) s }}
MAL.getSh1EntryAddrFromKernelStructureStart kernelStartAddr BlockEntryIndex
{{P}}.
Proof.
unfold MAL.getSh1EntryAddrFromKernelStructureStart.
eapply weaken.
apply ret.
intros.
destruct H.
destruct H0.
destruct H0.
apply H1.
Qed.

(* TODO : move getsh1entry here *)
Lemma getSCEntryAddrFromKernelStructureStart  (kernelStartAddr : paddr) (BlockEntryIndex : index)
																	(P : paddr -> state -> Prop) :
{{fun s => P (CPaddr (kernelStartAddr + scoffset + BlockEntryIndex)) s /\
 (*wellFormedFstShadowIfBlockEntry s /\*)
exists entry, lookup kernelStartAddr s.(memory) beqAddr = Some (BE entry)
					}}
MAL.getSCEntryAddrFromKernelStructureStart kernelStartAddr BlockEntryIndex
{{P}}.
Proof.
unfold MAL.getSCEntryAddrFromKernelStructureStart.
eapply weaken.
apply ret.
intros.
destruct H.
apply H.
Qed.

(* DUP *)
Lemma writeSCOriginFromBlockEntryAddr2  (neworigin SCEAddr : paddr) (P : unit -> state -> Prop) :
{{fun  s => (*exists blockentry , lookup entryaddr s.(memory) beqAddr = Some (BE blockentry) /\*)
						(*wellFormedShadowCutIfBlockEntry s /\*)
						exists entry , lookup SCEAddr s.(memory) beqAddr = Some (SCE entry) /\ 
P tt {|
  currentPartition := currentPartition s;
  memory := add SCEAddr
              (SCE {| origin := neworigin ; next := entry.(next) |})
              (memory s) beqAddr |} }}
MAL.writeSCOriginFromBlockEntryAddr2 neworigin SCEAddr  {{P}}.
Proof.
unfold MAL.writeSCOriginFromBlockEntryAddr2.
eapply bind .
  - intro s. simpl.
   case_eq (lookup SCEAddr s.(memory) beqAddr).
     + intros v Hpage.
       instantiate (1:= fun s s0 => s = s0 /\ exists entry , lookup SCEAddr (memory s) beqAddr = Some (SCE entry) /\
                                              P tt {| currentPartition := currentPartition s;
                                                      memory := add SCEAddr
                                                                  (SCE {| origin := neworigin ; next := entry.(next) |})
                                                                  (memory s) beqAddr |}).
       simpl in *.
       case_eq v; intros; eapply weaken; try eapply undefined ;simpl;
       subst;
       cbn; intros;
       try destruct H as (Hs & x & H1 & Hp); subst;
       try rewrite H1 in Hpage; inversion Hpage; subst; try assumption.
       eapply modify .
       intros.
       simpl.
       assumption.
     + intros Hpage; eapply weaken; try eapply undefined ;simpl.
       intros s0 H0. destruct H0 as (Hs & x & H1 & Hp).
       rewrite H1 in Hpage.
       inversion Hpage.
  - eapply weaken. eapply get . intuition.
Qed.

(* DUP *)
Lemma writeSh1PDChildFromBlockEntryAddr2  (Sh1EAddr pdchild : paddr) (P : unit -> state -> Prop) :
{{fun  s => (*exists blockentry , lookup entryaddr s.(memory) beqAddr = Some (BE blockentry) /\*)
						(*wellFormedShadowCutIfBlockEntry s /\*)
						exists entry , lookup Sh1EAddr s.(memory) beqAddr = Some (SHE entry) /\ 
P tt {|
  currentPartition := currentPartition s;
  memory := add Sh1EAddr
              (SHE {|	PDchild := pdchild;
										 	PDflag := entry.(PDflag);
										 	inChildLocation := entry.(inChildLocation) |})
              (memory s) beqAddr |} }}
MAL.writeSh1PDChildFromBlockEntryAddr2 Sh1EAddr pdchild  {{P}}.
Proof.
eapply bind .
  - intro s. simpl.
   case_eq (lookup Sh1EAddr s.(memory) beqAddr).
     + intros v Hpage.
       instantiate (1:= fun s s0 => s = s0 /\ exists entry , lookup Sh1EAddr (memory s) beqAddr = Some (SHE entry) /\
                                              P tt {| currentPartition := currentPartition s;
                                                      memory := add Sh1EAddr
																																		 (SHE
																																				{|
																																				PDchild := pdchild;
																																				PDflag := PDflag entry;
																																				inChildLocation := inChildLocation entry |}) 
                                                                  (memory s) beqAddr |}).
       simpl in *.
       case_eq v; intros; eapply weaken; try eapply undefined ;simpl;
       subst;
       cbn; intros;
       try destruct H as (Hs & x & H1 & Hp); subst;
       try rewrite H1 in Hpage; inversion Hpage; subst; try assumption.
       eapply modify .
       intros.
       simpl.
       assumption.
     + intros Hpage; eapply weaken; try eapply undefined ;simpl.
       intros s0 H0. destruct H0 as (Hs & x & H1 & Hp).
       rewrite H1 in Hpage.
       inversion Hpage.
  - eapply weaken. eapply get . intuition.
Qed.

(* DUP *)
Lemma writeSh1InChildLocationFromBlockEntryAddr2  (Sh1EAddr newinchildlocation : paddr) (P : unit -> state -> Prop) :
{{fun  s => (*exists blockentry , lookup entryaddr s.(memory) beqAddr = Some (BE blockentry) /\*)
						(*wellFormedShadowCutIfBlockEntry s /\*)
						exists entry , lookup Sh1EAddr s.(memory) beqAddr = Some (SHE entry) /\ 
P tt {|
  currentPartition := currentPartition s;
  memory := add Sh1EAddr
              (SHE {|	PDchild := entry.(PDchild);
										 	PDflag := entry.(PDflag);
										 	inChildLocation := newinchildlocation |})
              (memory s) beqAddr |} }}
MAL.writeSh1InChildLocationFromBlockEntryAddr2 Sh1EAddr newinchildlocation  {{P}}.
Proof.
eapply bind .
  - intro s. simpl.
   case_eq (lookup Sh1EAddr s.(memory) beqAddr).
     + intros v Hpage.
       instantiate (1:= fun s s0 => s = s0 /\ exists entry , lookup Sh1EAddr (memory s) beqAddr = Some (SHE entry) /\
                                              P tt {| currentPartition := currentPartition s;
                                                      memory := add Sh1EAddr
																																		 (SHE
																																				{|
																																				PDchild := PDchild entry;
																																				PDflag := PDflag entry;
																																				inChildLocation := newinchildlocation |}) 
                                                                  (memory s) beqAddr |}).
       simpl in *.
       case_eq v; intros; eapply weaken; try eapply undefined ;simpl;
       subst;
       cbn; intros;
       try destruct H as (Hs & x & H1 & Hp); subst;
       try rewrite H1 in Hpage; inversion Hpage; subst; try assumption.
       eapply modify .
       intros.
       simpl.
       assumption.
     + intros Hpage; eapply weaken; try eapply undefined ;simpl.
       intros s0 H0. destruct H0 as (Hs & x & H1 & Hp).
       rewrite H1 in Hpage.
       inversion Hpage.
  - eapply weaken. eapply get . intuition.
Qed.

Lemma checkEntry  (kernelstructurestart blockentryaddr : paddr) (P : bool -> state -> Prop) :
{{fun s => P (entryExists blockentryaddr s.(memory)) s

(*/\ exists bentry : BlockEntry, lookup blockentryaddr s.(memory) beqAddr = Some (BE bentry)*) }}
MAL.checkEntry kernelstructurestart blockentryaddr
{{P}}.
(*{{fun isValidentry s => P s /\ (isValidentry = true -> isBE blockentryaddr s)}}.*)
Proof.
unfold MAL.checkEntry.
eapply bind. intro s.
case_eq (lookup blockentryaddr (memory s) beqAddr).
- intros. instantiate (1:= fun s s0 => s=s0 (*/\ exists p1 ,
                   lookup blockentryaddr s.(memory) beqAddr =
                   Some (BE p1) *) /\ P (entryExists blockentryaddr s0.(memory)) s0).
	destruct v eqn:Hv. eapply weaken. apply ret.
	intros. simpl. intuition. unfold entryExists in *. subst. rewrite H in H2. assumption.
	eapply weaken. apply ret.
	intros. simpl. intuition. unfold entryExists in *. subst. rewrite H in H2. assumption.
eapply weaken. apply ret.
	intros. simpl. intuition. unfold entryExists in *. subst. rewrite H in H2. assumption.
eapply weaken. apply ret.
	intros. simpl. intuition. unfold entryExists in *. subst. rewrite H in H2. assumption.
eapply weaken. apply ret.
	intros. simpl. intuition. unfold entryExists in *. subst. rewrite H in H2. assumption.
- intros.
eapply weaken. apply ret.
	intros. simpl. intuition. unfold entryExists in *. subst. rewrite H in H2. assumption.
- eapply weaken. apply get.
	intros. simpl. intuition.
Qed.


Lemma check32Aligned  (addrToCheck : paddr) (P : bool -> state -> Prop) :
{{fun  s => P (StateLib.is32Aligned addrToCheck) s }}
MAL.check32Aligned addrToCheck  {{P}}.
Proof.
unfold check32Aligned.
eapply weaken. apply ret.
intros. exact H.
Qed.
