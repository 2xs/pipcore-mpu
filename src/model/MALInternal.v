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
    This file contains the definition of some constants and its monadic getters;
    and the module definition of each abstract data type in which we define required
    monadic functions  *)
Require Import Model.ADT Model.Hardware Model.Lib. 
Require Import List Arith Omega.

Open Scope mpu_state_scope.


Module Constants.
(* To be set by the user *)
(*  # To be set by the user
  self.kernel_structure_entries_bits = 3 *)
Definition kernelStructureEntriesBits := 3.


(** Fix positions into the partition descriptor
    of the partition *)
(*Definition pdidx := CPaddr 0.   (* descriptor *)*)
Definition kernelstructureidx := CIndex 0.
Definition nbfreeslotsidx := CIndex 1.
Definition firstfreeslotaddressidx := CIndex 2.
Definition nbprepareidx := CIndex 3.
Definition parentidx := CIndex 4. (* parent (virtual address is null) *)

(* kernel structure *)
(*# default values kernel structure
  self.kernel_structure_entries_nb = pow(2, self.kernel_structure_entries_bits)
  self.MPU_entry_length = (
              self.kernel_structure_entries_bits + 2 * memory.size_of_int + 2)  # start - end - accessible - present
  self.Sh1_entry_length = (2 * memory.size_of_int + 1)  # PDChild - PD flag - inChildLocation
  self.SC_entry_length = 2 * memory.size_of_int  # origin - next
  self.kernel_structure_total_length = self.kernel_structure_entries_nb * (
          self.MPU_entry_length + self.Sh1_entry_length + self.SC_entry_length) \
                                       + memory.size_of_int  # + next*)
Definition kernelStructureEntriesNb := kernelStructureEntriesBits ^ 2.

Definition MPUEntryLength := Build_paddr 3.
Definition SHEntryLength := Build_paddr 3.
Definition SCEntryLength := Build_paddr 2.

Definition mpuoffset := CPaddr 0.
Definition sh1offset := CPaddr (mpuoffset + kernelStructureEntriesNb*MPUEntryLength).  (* shadow1 *) 
Definition scoffset := CPaddr (sh1offset + kernelStructureEntriesNb*SHEntryLength).  (* shadow cut *)
(*Definition getPDidx : LLI index:= ret pdidx.*)
Definition nextoffset := CPaddr (scoffset + kernelStructureEntriesNb*SCEntryLength).

Definition rootPart := CPaddr 0.

Definition minBlockSize := Build_paddr 32.


End Constants.


Definition beqIdx (a b : ADT.index) : bool := a =? b.
Definition beqAddr (a b : ADT.paddr) : bool := a =? b.
Definition nullAddr : paddr := CPaddr 0.
Definition getNullAddr := ret nullAddr.
Definition getBeqAddr (p1 : paddr)  (p2 : paddr) : LLI bool := ret (p1 =? p2).
Definition getBeqIdx (p1 : index)  (p2 : index) : LLI bool := ret (p1 =? p2).
Definition getNextOffset : LLI paddr := ret Constants.nextoffset.
Definition getKernelStructureEntriesNb : LLI nat := ret Constants.kernelStructureEntriesNb.
Definition getMinBlockSize : LLI paddr := ret Constants.minBlockSize.

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

Definition getNextAddrFromKernelStructureStart (kernelStartAddr : paddr) : LLI paddr :=
	let nextAddr := CPaddr (kernelStartAddr + Constants.nextoffset) in
	ret nextAddr.

Definition getAddrAtIndexFromKernelStructureStart (kernelstructurestart : paddr) (idx : index) : LLI paddr :=
	let addr := CPaddr (kernelstructurestart + idx*Constants.MPUEntryLength) in
	ret addr.

Definition pred (n : paddr) : paddr :=
  match n with
    | Build_paddr t => Build_paddr (t-1)
  end.

Definition succ (n : paddr) : paddr :=
  match n with
    | Build_paddr t => Build_paddr (t+1)
  end.

Module Paddr.
Definition leb (a b : paddr) : LLI bool := ret (a <=? b).
End Paddr.

Module Index.
Program Definition succ (n : index) : LLI index :=
(*
let isucc := n+1 in
if (lt_dec isucc tableSize )
then
  ret (Build_index isucc _ )
else  undefined 28.*)
let isucc := n+1 in
ret (Build_index isucc).

Program Definition zero : LLI index:= ret (Build_index 0).
End Index.
