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
      The Abstraction Data Type :
				In this file we define elementary types representing hardware dependent types
				as well as enriched datatypes used by the Services
*)

(* NB: entry types are not represented within a superstructure in the model.
	However, they cannot be mixed, intertwined, or overlap because of the consistency properties. *)

Require Import List Bool Arith Model.UserConstants Lia.
Import List.ListNotations.

(*******************************************************************************)
(* Constants (computed from USER CONSTANTS *)
(*******************************************************************************)
Definition kernelStructureEntriesNb := kernelStructureEntriesBits ^ 2 -1.
Definition maxNbPrepare := nbPrepareMaxBits ^ 2.
(*******************************************************************************)


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
Axiom maxAddr: nat. (* Size of memory *)
Axiom maxAddrNotZero: maxAddr > 0.
Axiom maxIdx: nat. (* max prepare * kernel entries nb *)
Definition maxIdxLowerBound := 1. (* at minimum, we need to count to 1 *)
Axiom maxIdxNotZero: maxIdx > 0.
Axiom maxIdxBigEnough : maxIdx > maxIdxLowerBound.
Axiom maxIdxBiggerThanNbOfKernels: maxIdx > kernelStructureEntriesNb.
Axiom maxIdxEqualMaxAddr: maxIdx = maxAddr.

Axiom MPURegionsNb: nat.
Axiom MPURegionsNbNotZero: MPURegionsNb > 0.
Axiom MPURegionsNbBelowMaxIdx: MPURegionsNb <= maxIdx.

Axiom KSEntriesNbNotZero: kernelStructureEntriesNb > 0.
Axiom KSEntriesNbLessThanMaxIdx: kernelStructureEntriesNb < maxIdx - 1.
Axiom maxNbPrepareNotZero: maxNbPrepare > 0.
Axiom maxNbPrepareNbLessThanMaxIdx: maxNbPrepare < maxIdx - 1.

(*******************************************************************************)
(* Elementary datatypes *)
(*******************************************************************************)
(* index corresponds to an integer in C *)
Record index := {
  i :> nat ;
  Hi : i <= maxIdx }.
Parameter index_d : index. (* default index : 0 *)
Program Definition CIndex  (p : nat) : index :=
if (le_dec p maxIdx) then Build_index p _ else  index_d.

(* paddr corresponds to a physical address *)
Record paddr := {
  p :> nat;
  Hp : p <= maxAddr }.
(*Parameter paddr_d : paddr.*) (* default paddr : NULL *)
Program Definition CPaddr (p : nat) : paddr :=
if (le_dec p maxAddr) then Build_paddr p _ else  Build_paddr 0 _. (*paddr_d*)
Next Obligation.
lia.
Qed.

Axiom RAMStartAddr: paddr.
Axiom RAMEndAddr: paddr.

(*******************************************************************************)
(* Enriched datatypes *)
(*******************************************************************************)
(* block represents a contiguous region of memory addresses *)
Record block := {
  startAddr : paddr;
  endAddr : paddr ;
	Hsize : endAddr - startAddr <= maxIdx (* [startAddr ; endAddr ] because the MPU region
																					 end address IS included in the region,
																					however the size is STRICTLY under maxIdx
																					[_______________]
																					^						^		^
																					|						|		| maxIdx = maxAddr
																					|@start --- |@end
*)
}.
Parameter block_d : block.
Program Definition CBlock (startAddr endAddr : paddr) : block :=
if le_dec (endAddr - startAddr) maxIdx
then Build_block startAddr endAddr _
else block_d.

Record BlockEntry : Type:=
{
 read : bool;
 write : bool ;
 exec : bool;
 present : bool;
 accessible : bool;
 blockindex : index;
 blockrange : block ;
 Hidx : blockindex < kernelStructureEntriesNb
}.
Parameter blockentry_d : BlockEntry.

Program Definition CBlockEntry (R W X P A: bool) (blockindex : index) (blockrange : block) :=
if lt_dec blockindex kernelStructureEntriesNb then Build_BlockEntry R W X P A blockindex blockrange _
else blockentry_d .

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
 parent : paddr ;
 MPU : list paddr ;
 vidtAddr : paddr
 (*;
 HMPU : length MPU = MPURegionsNb*)

(*;
 Hp : pd < nbPage *)
}.

Inductive blockOrError :=
| error
| blockAttr' (addr : paddr) (blockentry : BlockEntry)
.

Definition blockAttr := blockAttr'.
