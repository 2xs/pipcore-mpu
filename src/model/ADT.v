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

(**  * Summary 
      The Abstraction Data Type : In this file we define types used by memory Services *)
Require Import List Bool Arith Omega. 
Import List.ListNotations.

(* BEGIN SIMULATION

Definition nbLevel := 2.
Definition tableSize := 12.
Definition nbPage := 100.
Lemma nbLevelNotZero: nbLevel > 0.
Proof. unfold nbLevel; auto. Qed.
Lemma tableSizeNotZero : tableSize <> 0.
Proof. unfold tableSize; auto. Qed.


   END SIMULATION *)

(* BEGIN NOT SIMULATION *)
Axiom tableSize nbLevel nbPage: nat.
Axiom nbLevelNotZero: nbLevel > 0.
Axiom nbPageNotZero: nbPage > 0.


(* index represents whatever entry in a kernel structure *) 
Record index := {
  i :> nat (*;
  Hi : i < tableSize*) }.

Program Definition CIndex  (p : nat) : index := 
(*if (lt_dec p tableSize) then 
Build_index p _ else index_d.*)
Build_index p.

(* TODO: change nbPage + coercion removed*)
Record paddr := { 
  p :> nat(*;
  Hp : p < nbPage *)}.

(* TODO : set nbPage coercion *)
Program Definition CPaddr (p : nat) : paddr := 
(*if (lt_dec p nbPage) then Build_paddr p _ else  page_d.*)
Build_paddr p.

Record block := { 
  startAddr :> paddr;
  endAddr :> paddr ;
  Hp : startAddr < endAddr;
	Hstart : 0 <= startAddr;
	Hend : 0 < endAddr }.

(* TODO: change tableSize*)
Record MPUIndex := {
  MPUi :> nat (*;
  Hi : i < tableSize*) }.

Inductive id : Type :=
  | Id (n : nat).

Definition eqb_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 => n1 =? n2
  end.
  
(*Inductive paddrOption : Type :=
  | Some (n : nat)
  | None.*)