(*******************************************************************************)
(*  © Université Lille 1, The Pip Development Team (2015-2018)                 *)
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
This file contains the Hoare logic formalization.

 
-Hoare logic formalization <<{{ P }} m {{ Q }}>>:  
   
 - <<m>> is a monadic function 
  
 - <<P>> is the precondition of the function <<m>>, it is an unary predicate which depends on the state   
   
 - <<Q>> is the postcondition of the function <<m>>, it is a binary predicate which depends on the new state and the return value  
 

-We define some lemmas like [weaken] and [bindWP] to facilitate Hoare logic 
     and monad manipulation.
*)
Require Import FunctionalExtensionality Model.Monad(*Model.ADT*).

Open Scope mpu_state_scope.

Definition hoareTriple {A : Type} (P : state -> Prop) (m : LLI A) (Q : A -> state -> Prop) : Prop :=
  forall s, P s -> match m s with
    | val (a, s') => Q a s'
(*     | hlt => True *)
    | undef _ _=> False
    end.

Notation "{{ P }} m {{ Q }}" := (hoareTriple P m Q)
  (at level 90, format "'[' '[' {{  P  }}  ']' '/  ' '[' m ']' '['  {{  Q  }} ']' ']'") : mpu_state_scope.

Lemma conjProp (A : Type ) (P R : state -> Prop) (Q : A -> state -> Prop) m :

{{ P }} m {{ Q}} -> {{R}} m {{fun _ => R}} -> {{fun s => P s/\ R s}} m {{fun a s => Q a s/\ R s}}.
Proof.
intros H1 H2 s [H3 H4].
apply H1 in H3.
apply H2 in H4.
destruct (m s) as [ [ a s' ] | ]; tauto.
Qed.

Definition wp {A : Type} (P : A -> state -> Prop) (m : LLI A) :=
  fun s => match m s with val (a, s') => P a s'(*  | hlt => True *) | Err => False end.

Lemma wpIsPrecondition {A : Type} (P : A -> state -> Prop) (m : LLI A) :
  {{ wp P m }} m {{ P }}.
Proof.
unfold wp.
congruence.
Qed.

Lemma wpIsWeakestPrecondition
  (A : Type) (P : A -> state -> Prop) (Q : state -> Prop) (m : LLI A) :
  {{ Q }} m {{ P }} -> forall s, Q s -> (wp P m) s.
Proof.
trivial.
Qed.
Lemma assoc (A B C : Type)(m : LLI A)(f : A -> LLI B)(g : B -> LLI C) :
  perform y :=
    perform x := m in
    f x in
  g y =
  perform x := m in
  perform y := f x in
  g y.
Proof.
extensionality s; unfold bind; case (m s); trivial; tauto.
Qed.


(* Lemma runvaluebind {A : Type} (m e: LLI A) (s : state) : 
runvalue (perform x := m in e) s = 
match runvalue m s with 
| None => runvalue e s 
| Some x => runvalue e s 
end.
case_eq(runvalue m s);intros.
unfold runvalue in *.
case_eq(m s);intros.
simpl.
subst.
case_eq((m;; e) s);intros.
destruct p0.
case_eq(e s);intros.
destruct p0.
subst.
unfold bind in *.
rewrite H0 in *.
cbn in *.
simpl in 
*.

simpl. *)


Lemma postAnd :
  forall (A : Type) (P : state -> Prop) (Q R : A -> state -> Prop) (m : LLI A),
  {{ P }} m {{ Q }} -> {{ P }} m {{ R }} -> {{ P }} m {{ fun a s => Q a s /\ R a s }}.
Proof.
intros A P Q R c H1 H2 s H3.
generalize (H1 s H3). clear H1. intro H1.
generalize (H2 s H3). clear H2. intro H2.
destruct (c s) as [ [ a s' ] | ]; tauto.
Qed.

Lemma preOr :
  forall (A : Type) (P Q : state -> Prop) (R : A -> state -> Prop) (m : LLI A),
  {{ P }} m {{ R }} -> {{ Q }} m {{ R }} -> {{ fun s => P s \/ Q s }} m {{ R }}.
Proof.
intros A P Q R c H1 H2 s H3.
destruct H3 as [H3|H3].
generalize (H1 s H3). clear H1. intro H1. assumption.
generalize (H2 s H3). clear H2. intro H2. assumption.
Qed.

Lemma preAndPost : 
 forall (A : Type) (P1 Q1 : state -> Prop) (P2  : A -> state -> Prop) (m : LLI A),
{{P1}} m {{P2}} -> 
{{fun s => P1 s /\ Q1 s}} m {{fun a => Q1 }} -> 
{{fun s => P1 s /\ Q1 s}} m {{fun a s => P2 a s /\ Q1 s}}.
Proof.
intros.
unfold hoareTriple in *.
intros.
assert( P1 s) by intuition.
apply H0 in H1.
apply H in H2.
destruct (m s); trivial.
destruct p.
split; trivial.
Qed.

Lemma andAssocHT  :
 forall (A : Type) (P1 P2 P3 : state -> Prop) (R  : A -> state -> Prop) (m : LLI A),
{{ fun s => (P1 s /\ P2 s) /\ P3 s}} m {{ R}} <-> {{ fun s => P1 s /\ P2 s /\ P3 s }} m {{ R}}.
Proof.
unfold hoareTriple.
intros.
split;
intros;
apply H;
apply and_assoc; assumption.
Qed.

Lemma permutHT :
forall (A : Type) (P1 P2 P3 : state -> Prop) (R  : A -> state -> Prop) (m : LLI A),
{{ fun s => P1 s /\ P2 s /\ P3 s}} m {{ R}} <-> {{ fun s => P1 s /\ P3 s /\ P2 s }} m {{ R}}.
Proof.
      unfold hoareTriple.
intros.
split;
intros;
apply H; intuition.
Qed.

Lemma permutHT1 :
forall (A : Type) (P1 P2 P3 : state -> Prop) (R  : A -> state -> Prop) (m : LLI A),
{{ fun s => P1 s /\ P2 s /\ P3 s}} m {{ R}} <-> {{ fun s =>P3 s /\  P1 s /\ P2 s  /\ P3 s}} m {{ R}}.
Proof.
      unfold hoareTriple.
intros.
split;
intros;
apply H; intuition.
Qed.

Lemma preAnd:
 forall (A : Type) (P1 Q : state -> Prop) (P2  : A -> state -> Prop) (m : LLI A),
{{P1}} m {{P2}} -> {{fun s => P1 s /\ Q s}} m {{P2}}.
Proof.
unfold hoareTriple.
intros; apply H; intuition.
Qed.

Lemma conjPrePost :
forall (A : Type) (P1 Q1 : state -> Prop) (P2 Q2 : A -> state -> Prop) (m : LLI A),
{{P1}} m {{P2}} ->
{{Q1}} m {{Q2}} -> 
{{fun s => P1 s /\ Q1 s}} m {{fun a s => P2 a s /\ Q2 a s}}.
Proof.
intros.
unfold hoareTriple in *.
intros.
destruct H1.
apply H in H1.
apply H0 in H2.
destruct (m s); trivial.
destruct p; intuition.
Qed.