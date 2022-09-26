(*******************************************************************************)
(*  © Université de Lille, The Pip Development Team (2015-2022)                *)
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
    This file contains the definition of some constants and their monadic getters;
    and the module definition of each abstract data type in which we define required
    monadic functions  *)
Require Import Model.ADT Model.Monad.
Require Import List Arith Omega.

Open Scope mpu_state_scope.


(** Specific variables for the Coq part, not used in the C program *)
Definition blkoffset := CIndex 0.
Definition sh1offset := CIndex (blkoffset + kernelStructureEntriesNb).  (* shadow1 *)
Definition scoffset := CIndex (sh1offset + kernelStructureEntriesNb).  (* shadow cut *)
Definition nextoffset := CIndex (scoffset + kernelStructureEntriesNb).

Definition paddrLe (x y: paddr) : bool := x <=? y.
Definition paddrLt (x y: paddr) : bool := x <? y.

Notation paddrLeM x y := (ret (paddrLe x y)) (only parsing).
Notation paddrLtM x y := (ret (paddrLt x y)) (only parsing).

Program Definition paddrSuccM (n : paddr) : LLI paddr :=
let isucc := n+1 in
if (le_dec isucc maxAddr )
then
  ret (Build_paddr isucc _ )
else  undefined 68.

Program Definition paddrPredM (n : paddr) : LLI paddr :=
let ipred := n-1 in
if (le_dec ipred maxAddr )
then
  ret (Build_paddr ipred _ )
else  undefined 69.


Module Paddr.
(* #[deprecated(note="Use paddrLeM instead.")] *)
Notation leb x y := (paddrLeM x y) (only parsing).
(* #[deprecated(note="Use paddrLtM instead.")] *)
Notation ltb x y := (paddrLtM x y) (only parsing).

(* #[deprecated(note="Use paddrSuccM instead.")] *)
Notation succ := paddrSuccM (only parsing).
(* #[deprecated(note="Use paddrPredM instead.")] *)
Notation pred := paddrPredM (only parsing).


Program Definition addPaddrIdx (n : paddr) (m: index) : LLI paddr :=
let res := n+m in
if (le_dec res maxAddr )
then
  ret (Build_paddr res _ )
else  undefined 70.

Program Definition subPaddrIdx (n : paddr) (m: index) : LLI paddr :=
let res := n-m in
if (le_dec res maxAddr )
then
  ret (Build_paddr res _ )
else  undefined 71.

Program Definition subPaddr (n : paddr) (m: paddr) : LLI index :=
let res := n-m in
if (le_dec res maxIdx)
then
  ret (Build_index res _ )
else  undefined 72.
End Paddr.

Definition indexLe (x y: index) : bool := x <=? y.
Definition indexLt (x y: index) : bool := x <? y.

Notation indexLeM x y := (ret (indexLe x y)) (only parsing).
Notation indexLtM x y := (ret (indexLt x y)) (only parsing).

Program Definition indexSuccM (n : index) : LLI index :=
let isucc := n+1 in
if (le_dec isucc maxIdx)
then
  ret (Build_index isucc _ )
else  undefined 68.

Program Definition indexPredM (n : index) : LLI index :=
let ipred := n-1 in
if (le_dec ipred maxIdx)
then
  ret (Build_index ipred _ )
else  undefined 71.


Module Index.

(* #[deprecated(note="Use indexLeM instead.")] *)
Notation leb x y := (indexLeM x y) (only parsing).
(* #[deprecated(note="Use indexLtM instead.")] *)
Notation ltb x y := (indexLtM x y) (only parsing).
(* #[deprecated(note="Use indexSuccM instead.")] *)
Notation succ := indexSuccM (only parsing).
(* #[deprecated(note="Use indexPredM instead.")] *)
Notation pred := indexPredM (only parsing).


Program Definition zero : LLI index:= ret (CIndex 0).

Program Definition subIdx (n : index) (m: index) : LLI index :=
let res := n-m in
if (le_dec res maxIdx )
then
  ret (Build_index res _ )
else  undefined 72.

Program Definition addIdx (n : index) (m: index) : LLI index :=
let res := n+m in
if (le_dec res maxIdx )
then
  ret (Build_index res _ )
else  undefined 72.

Program Definition mulIdx (n : index) (m: index) : LLI index :=
let res := n*m in
if (le_dec res maxIdx )
then
  ret (Build_index res _ )
else  undefined 70.

End Index.

Module Constants.
(** Fix positions into the partition descriptor
    of the partition *)
Definition kernelstructureidx := CIndex 0.

Definition rootPart := CPaddr 0.

Definition minBlockSize := CIndex 32.

(**
 * The minimum VIDT block size for the nRF52832.
 *
 * TODO: Do not hard-code the value.
 *)
Definition vidtSize := CIndex 224.

(* TODO : power of 2*)
Definition kernelStructureTotalLength := CIndex (nextoffset + 1).
Definition PDStructureTotalLength := CIndex (5+8). (*5 fields + table of 8 MPU regions *)
End Constants.

Definition multiplexer := Constants.rootPart.

(*Definition getNextOffset : LLI paddr := ret Constants.nextoffset.*)
Definition getNextOffset : LLI index := ret nextoffset.
Definition getKernelStructureEntriesNb : LLI index := ret (CIndex kernelStructureEntriesNb).
Definition getMaxNbPrepare : LLI index := ret (CIndex maxNbPrepare).
(*Definition getMinBlockSize : LLI paddr := ret Constants.minBlockSize.*)
Definition getMinBlockSize : LLI index := ret Constants.minBlockSize.
Definition getVidtSize : LLI index := ret Constants.vidtSize.
Definition getKernelStructureTotalLength : LLI index := ret Constants.kernelStructureTotalLength.
Definition getPDStructureTotalLength : LLI index := ret Constants.PDStructureTotalLength.
Definition getMPURegionsNb : LLI index := ret (CIndex MPURegionsNb).

Definition beqIdx (a b : ADT.index) : bool := a =? b.
Definition beqAddr (a b : paddr) : bool := a =? b.
Definition nullAddr : paddr := CPaddr 0.
Definition getNullAddr := ret nullAddr.
Notation getBeqAddr a b := (ret (beqAddr a b)) (only parsing).

Definition getBeqIdx (p1 : index)  (p2 : index) : LLI bool := ret (p1 =? p2).

Definition getAddr (paddr : paddr) : LLI ADT.paddr := ret paddr.

