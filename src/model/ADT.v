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
      The Abstraction Data Type :
				In this file we define elementary types representing hardware dependent types
				as well as enriched datatypes used by the Services
*)

Require Import List Bool Arith Omega Model.UserConstants.
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
(*Axiom tableSize nbLevel nbPage: nat.
Axiom nbLevelNotZero: nbLevel > 0.
Axiom nbPageNotZero: nbPage > 0.*)
Axiom maxAddr: nat. (* Size of memory *)
Axiom maxAddrNotZero: maxAddr > 0.
Axiom maxIdx: nat. (* max prepare * kernel entries nb *)
Axiom maxIdxNotZero: maxAddr > 0.

(*******************************************************************************)
(* Elementary datatypes *)
(*******************************************************************************)
(* index corresponds to an integer in C *)
Record index := {
  i :> nat ;
  Hi : i < maxIdx }.
Parameter index_d : index. (* default index : 0 *)
Program Definition CIndex  (p : nat) : index :=
if (lt_dec p maxIdx) then Build_index p _ else  index_d.

(* paddr corresponds to a physical address *)
Record paddr := { 
  p :> nat;
  Hp : p < maxAddr }.
Parameter paddr_d : paddr. (* default paddr : NULL *)
Program Definition CPaddr (p : nat) : paddr := 
if (lt_dec p maxAddr) then Build_paddr p _ else  paddr_d.


(*******************************************************************************)
(* Enriched datatypes *)
(*******************************************************************************)
(* block represents a contiguous region of memory addresses *)
Record block := {
  startAddr : paddr;
  endAddr : paddr ;
  Haddr : startAddr < endAddr
}.
Parameter block_d : block.
Program Definition CBlock (startAddr endAddr : paddr) : block :=
if (lt_dec startAddr endAddr) then Build_block startAddr endAddr _ else  block_d.

(* MPU index represents an entry number in an MPU structure *)
Record MPUIndex := {
  MPUi :> nat ;
  Hmpu : MPUi < kernelStructureEntriesNb }.

Record MPUEntry : Type:=
{
 read :bool;
 write : bool ;
 exec : bool;
 present : bool;
 accessible : bool;
 mpuindex : index;
 mpublock : block
}.

Record Sh1Entry : Type:=
{
 PDchild : paddr;
 PDflag : bool;
 inChildLocation : paddr
}.

Record SCEntry : Type:=
{
 origin : paddr;
 next : paddr
}.

Record PDTable :=
{
 structure : paddr ;
 firstfreeslot : paddr ;
 nbfreeslots : index ;
 nbprepare : index ;
 parent : paddr (*;
 Hp : pd < nbPage *)
}.