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
    This file contains the definition of some constants and their monadic getters;
    and the module definition of each abstract data type in which we define required
    monadic functions  *)
Require Import Model.ADT Model.Monad Model.UserConstants.
Require Import List Arith Omega.

Open Scope mpu_state_scope.


Module Paddr.
Definition leb (a b : paddr) : LLI bool := ret (a <=? b).
Program Definition succ (n : paddr) : LLI paddr :=
let isucc := n+1 in
if (lt_dec isucc maxAddr )
then
  ret (Build_paddr isucc _ )
else  undefined 68.

Program Definition pred (n : paddr) : LLI paddr :=
let ipred := n-1 in
if (lt_dec ipred maxAddr )
then
  ret (Build_paddr ipred _ )
else  undefined 69.

Program Definition mulIdxPaddr (n : index) (m: paddr) : LLI paddr :=
let res := n*m in
if (lt_dec res maxAddr )
then
  ret (Build_paddr res _ )
else  undefined 70.

Program Definition addPaddr (n : paddr) (m: paddr) : LLI paddr :=
let res := n+m in
if (lt_dec res maxAddr )
then
  ret (Build_paddr res _ )
else  undefined 71.
End Paddr.


Module Index.
Definition leb (a b : index) : LLI bool := ret (a <=? b).
Definition ltb (a b : index) : LLI bool := ret (a <? b).
Program Definition succ (n : index) : LLI index :=
let isucc := n+1 in
if (lt_dec isucc maxIdx)
then
  ret (Build_index isucc _ )
else  undefined 68.
Program Definition pred (n : index) : LLI index :=
let ipred := n-1 in
if (lt_dec ipred maxIdx)
then
  ret (Build_index ipred _ )
else  undefined 71.

Program Definition zero : LLI index:= ret (CIndex 0).
End Index.

Module Constants.
(** Fix positions into the partition descriptor
    of the partition *)
(*Definition pdidx := CPaddr 0.   (* descriptor *)*)
Definition kernelstructureidx := CIndex 0.
Definition nbfreeslotsidx := CIndex 1.
Definition firstfreeslotaddressidx := CIndex 2.
Definition nbprepareidx := CIndex 3.
Definition parentidx := CIndex 4. (* parent (virtual address is null) *)

Definition MPUEntryLength := CPaddr 3.
Definition SHEntryLength := CPaddr 3.
Definition SCEntryLength := CPaddr 2.

Definition mpuoffset := CPaddr 0.
Definition sh1offset := CPaddr (mpuoffset + kernelStructureEntriesNb*MPUEntryLength).  (* shadow1 *) 
Definition scoffset := CPaddr (sh1offset + kernelStructureEntriesNb*SHEntryLength).  (* shadow cut *)
Definition nextoffset := CPaddr (scoffset + kernelStructureEntriesNb*SCEntryLength).

Definition rootPart := CPaddr 0.

Definition minBlockSize := CPaddr 32.

(* TODO : power of 2*)
Definition kernelStructureTotalLength := CPaddr (nextoffset + 1).
End Constants.

Definition getNextOffset : LLI paddr := ret Constants.nextoffset.
Definition getKernelStructureEntriesNb : LLI index := ret (CIndex kernelStructureEntriesNb).
Definition getMaxNbPrepare : LLI index := ret (CIndex maxNbPrepare).
Definition getMinBlockSize : LLI paddr := ret Constants.minBlockSize.
Definition getKernelStructureTotalLength : LLI paddr := ret Constants.kernelStructureTotalLength.

Definition beqIdx (a b : ADT.index) : bool := a =? b.
Definition beqAddr (a b : ADT.paddr) : bool := a =? b.
Definition nullAddr : paddr := CPaddr 0.
Definition getNullAddr := ret nullAddr.
Definition getBeqAddr (p1 : paddr)  (p2 : paddr) : LLI bool := ret (p1 =? p2).
Definition getBeqIdx (p1 : index)  (p2 : index) : LLI bool := ret (p1 =? p2).

Definition getAddr (paddr : paddr) : LLI ADT.paddr := ret paddr.

Definition getMPUEntryAddrFromKernelStructureStart (kernelStartAddr : paddr) (MPUEntryIndex : index) : LLI paddr :=
(* return kernel_structure_address_begin + self.constants.MPU + MPU_entry_index*self.constants.MPU_entry_length*)
	let mpuEntryAddr := CPaddr (kernelStartAddr + Constants.mpuoffset + MPUEntryIndex*Constants.MPUEntryLength) in
	ret mpuEntryAddr.

(*         """Get the location of the Sh1's entry given the <MPU_entry_index>
        and the <kernel_structure_address_begin"""*)
(*Definition getSh1EntryIndexFromKernelStructureStart (kernelStartIndex MPUEntryIndex : PipMPU.index) : PipMPU.LLI index :=
(* return kernel_structure_address_begin + self.constants.indexSh1 + MPU_entry_index*self.constants.Sh1_entry_length*)
	let sh1EntryIdx := Build_index (kernelStartIndex + sh1idx + MPUEntryIndex) in
	PipMPU.ret sh1EntryIdx.*)
Definition getSh1EntryAddrFromKernelStructureStart (kernelStartAddr : paddr) (MPUEntryIndex : index) : LLI paddr :=
(* return kernel_structure_address_begin + self.constants.indexSh1 + MPU_entry_index*self.constants.Sh1_entry_length*)
	let sh1EntryAddr := CPaddr (kernelStartAddr + Constants.sh1offset + MPUEntryIndex*Constants.SHEntryLength) in
	ret sh1EntryAddr.

Definition getKernelStructureStartAddr (mpuentryaddr : paddr) (mpuindex : index) : LLI paddr :=
	(* compute kernel start *)
	(* MPU_entry_index = self.get_MPU_index(MPU_entry_address)
  # we compute the start of the kernel structure knowing the MPU's entry address and index
  kernel_structure_start = MPU_entry_address - MPU_entry_index * self.constants.MPU_entry_length*)
(* TODO : check if paddr - MPUEntryIndexidx*Constants.MPUEntryLength > 0 ? *)
	let kernelStartAddr := CPaddr (mpuentryaddr - mpuindex*Constants.MPUEntryLength) in
	ret kernelStartAddr.

Definition getSCEntryAddrFromKernelStructureStart (kernelStartAddr : paddr) (MPUEntryIndex : index) : LLI paddr :=
(* return kernel_structure_address_begin + self.constants.indexSC + MPU_entry_index*self.constants.SC_entry_length*)
	let scEntryAddr := CPaddr (kernelStartAddr + Constants.scoffset + MPUEntryIndex*Constants.SCEntryLength) in
	ret scEntryAddr.

Definition getNextAddrFromKernelStructureStart (kernelStartAddr : paddr) : LLI paddr :=
	let nextAddr := CPaddr (kernelStartAddr + Constants.nextoffset) in
	ret nextAddr.

Definition getMPUEntryAddrAtIndexFromKernelStructureStart (kernelstructurestart : paddr) (idx : index) : LLI paddr :=
	let addr := CPaddr (kernelstructurestart + idx*Constants.MPUEntryLength) in
	ret addr.
