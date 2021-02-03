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
     Memory Abstraction Layer : is the interface exposed to services to read and
    write data into physical memory  *)
Require Export Model.MALInternal. 
Require Import Model.ADT Model.Hardware Model.Lib.
Require Import Arith Bool NPeano List Omega.

Export Hardware.

Set Printing Implicit.
Print Visibility.
Print Model.Hardware.get.
Set Typeclasses Debug Verbosity 2.
Open Scope mpu_state_scope.

Check (fun s => ret s.(currentPartition)).
Check bind get (fun s => ret s.(currentPartition)).
Check perform s := get in ret s.(currentPartition).

  (** The 'getCurPartition' function returns the current Partition from the current state *)
(*Definition getCurPartition : LLI index :=
	perform s := PipMPU.get in PipMPU.ret s.(PipMPU.currentPartition).*)
Definition getCurPartition : LLI paddr :=
	perform s := get in ret s.(currentPartition).


Definition readPDTable (paddr : paddr)  : LLI PDTable :=
	perform s := get in
  let entry :=  lookup paddr s.(memory) beqAddr in
  match entry with
  | Some (PDT a) => ret a
  | Some _ => undefined 5
  | None => undefined 4
  end.

Definition readPDStructurePointer  (pdtablepaddr: paddr) : LLI paddr :=
  perform s := get in
  let entry :=  lookup pdtablepaddr s.(memory) beqAddr in
  match entry with
  | Some (PDT a) => ret a.(structure)
  | Some _ => undefined 12
  | None => undefined 11
  end.

Definition writePDStructurePointer (pdtablepaddr: paddr) (structurepaddr : paddr) : LLI unit :=
	perform s := get in
	let entry :=  lookup pdtablepaddr s.(memory) beqAddr in
	match entry with
		| Some (PDT a) =>  let newEntry := {| structure := structurepaddr;
																					firstfreeslot := a.(firstfreeslot);
																					nbfreeslots := a.(nbfreeslots);
																					nbprepare := a.(nbprepare);
																					parent := a.(parent)
																			|} in
											modify (fun s => {| currentPartition := s.(currentPartition);
																								memory := add pdtablepaddr (PDT newEntry) s.(memory) beqAddr|} )
		| Some _ => undefined 60
		| None => undefined 59
	end.

Definition writePDFirstFreeSlotAddr (pdtablepaddr: paddr) (firstfreeslotpaddr : paddr) : LLI unit :=
	perform s := get in
	let entry :=  lookup pdtablepaddr s.(memory) beqAddr in
	match entry with
		| Some (PDT a) =>  let newEntry := {| structure := a.(structure);
																					firstfreeslot := firstfreeslotpaddr;
																					nbfreeslots := a.(nbfreeslots);
																					nbprepare := a.(nbprepare);
																					parent := a.(parent)
																			|} in
											modify (fun s => {| currentPartition := s.(currentPartition);
																								memory := add pdtablepaddr (PDT newEntry) s.(memory) beqAddr|} )
		| Some _ => undefined 60
		| None => undefined 59
	end.

Definition writePDNbFreeSlots (pdtablepaddr: paddr) (nbfreeslots : nat) : LLI unit :=
	perform s := get in
	let entry :=  lookup pdtablepaddr s.(memory) beqAddr in
	match entry with
		| Some (PDT a) =>  let newEntry := {| structure := a.(structure);
																					firstfreeslot := a.(firstfreeslot);
																					nbfreeslots := nbfreeslots;
																					nbprepare := a.(nbprepare);
																					parent := a.(parent)
																			|} in
											modify (fun s => {| currentPartition := s.(currentPartition);
																								memory := add pdtablepaddr (PDT newEntry) s.(memory) beqAddr|} )
		| Some _ => undefined 60
		| None => undefined 59
	end.

Definition writePDNbPrepare (pdtablepaddr: paddr) (nbprepare : nat) : LLI unit :=
	perform s := get in
	let entry :=  lookup pdtablepaddr s.(memory) beqAddr in
	match entry with
		| Some (PDT a) =>  let newEntry := {| structure := a.(structure);
																					firstfreeslot := a.(firstfreeslot);
																					nbfreeslots := a.(nbfreeslots);
																					nbprepare := nbprepare;
																					parent := a.(parent)
																			|} in
											modify (fun s => {| currentPartition := s.(currentPartition);
																								memory := add pdtablepaddr (PDT newEntry) s.(memory) beqAddr|} )
		| Some _ => undefined 60
		| None => undefined 59
	end.

Definition readPDParent  (pdtablepaddr: paddr) : LLI paddr :=
  perform s := get in
  let entry :=  lookup pdtablepaddr s.(memory) beqAddr in
  match entry with
  | Some (PDT a) => ret a.(parent)
  | Some _ => undefined 12
  | None => undefined 11
  end.

Definition writePDParent (pdtablepaddr: paddr) (parent : paddr) : LLI unit :=
	perform s := get in
	let entry :=  lookup pdtablepaddr s.(memory) beqAddr in
	match entry with
		| Some (PDT a) =>  let newEntry := {| structure := a.(structure);
																					firstfreeslot := a.(firstfreeslot);
																					nbfreeslots := a.(nbfreeslots);
																					nbprepare := a.(nbprepare);
																					parent := parent
																			|} in
											modify (fun s => {| currentPartition := s.(currentPartition);
																								memory := add pdtablepaddr (PDT newEntry) s.(memory) beqAddr|} )
		| Some _ => undefined 60
		| None => undefined 59
	end.


Definition readMPUEntry (paddr : paddr) : LLI MPUEntry :=
  perform s := get in
  let entry :=  lookup paddr s.(memory) beqAddr in
  match entry with
  | Some (MPUE a) => ret a
  | Some _ => undefined 9
  | None => undefined 8
  end.
(*
Definition readMPUAccessibleFromMPUEntryAddr  (paddridx : PipMPU.index) : LLI bool :=
  perform s := get in
  let entry :=  PipMPU.lookup paddridx s.(memory) PipMPU.beqIdx in
  match entry with
  | Some (MPUE a) => ret a.(accessible)
  | Some _ => undefined 12
  | None => undefined 11
  end.*)
Check LLI paddr.
Definition readMPUStartFromMPUEntryAddr  (paddr : paddr) : LLI ADT.paddr :=
  perform s := get in
  let entry :=  lookup paddr s.(memory) beqAddr in
  match entry with
  | Some (MPUE a) => ret a.(mpublock).(startAddr)
  | Some _ => undefined 12
  | None => undefined 11
  end.
Print readMPUStartFromMPUEntryAddr.

Definition readMPUAccessibleFromMPUEntryAddr  (paddr : paddr) : LLI bool :=
  perform s := get in
  let entry :=  lookup paddr s.(memory) beqAddr in
  match entry with
  | Some (MPUE a) => ret a.(accessible)
  | Some _ => undefined 12
  | None => undefined 11
  end.

Definition writeMPUAccessibleFromMPUEntryAddr  (paddr : paddr) (accessiblebit  : bool) : LLI unit :=
  perform s := get in
  let entry :=  lookup paddr s.(memory) beqAddr in
  match entry with
  | Some (MPUE a) => let newEntry := {|	read := a.(read);
																			 	write := a.(write);
																			 	exec := a.(exec);
																			 	present := a.(present);
																			 	accessible := accessiblebit;
																			 	mpuindex := a.(mpuindex);
																			 	mpublock := a.(mpublock)
																			|} in
											modify (fun s => {| currentPartition := s.(currentPartition);
																								memory := add paddr (MPUE newEntry) s.(memory) beqAddr|} )
		| Some _ => undefined 60
		| None => undefined 59
  end.

Definition readMPUPresentFromMPUEntryAddr  (paddr : paddr) : LLI bool :=
  perform s := get in
  let entry :=  lookup paddr s.(memory) beqAddr in
  match entry with
  | Some (MPUE a) => ret a.(present)
  | Some _ => undefined 12
  | None => undefined 11
  end.

(*Definition readMPUIndexFromMPUEntry  (paddridx : PipMPU.index) : LLI nat :=
  perform s := get in
  let entry :=  PipMPU.lookup paddridx s.(memory) PipMPU.beqIdx in
  match entry with
  | Some (MPUE a) => ret a.(mpuindex)
  | Some _ => undefined 12
  | None => undefined 11
  end.*)
Definition readMPUIndexFromMPUEntry  (paddr : paddr) : LLI nat :=
  perform s := get in
  let entry :=  lookup paddr s.(memory) beqAddr in
  match entry with
  | Some (MPUE a) => ret a.(mpuindex)
  | Some _ => undefined 12
  | None => undefined 11
  end.

Definition readMPUBlockFromMPUEntryAddr  (paddr : paddr) : LLI block :=
  perform s := get in
  let entry :=  lookup paddr s.(memory) beqAddr in
  match entry with
  | Some (MPUE a) => ret a.(mpublock)
  | Some _ => undefined 12
  | None => undefined 11
  end.


(*Definition readPDChildFromMPUEntry (paddridx : PipMPU.index) : LLI PipMPU.index :=
(* compute kernel start *)

(* MPU_entry_index = self.get_MPU_index(MPU_entry_address)
  # we compute the start of the kernel structure knowing the MPU's entry address and index
  kernel_structure_start = MPU_entry_address - MPU_entry_index * self.constants.MPU_entry_length
  return self.get_address_Sh1_PDchild_from_kernel_structure_start(kernel_structure_start, MPU_entry_index)*)
	perform MPUEntryIndex := readMPUIndexFromMPUEntry paddridx in
	let MPUEntryIndexidx := CIndex MPUEntryIndex in
	let kernelStartIdx := CIndex (paddridx - MPUEntryIndexidx) in
	perform Sh1Eidx := PipMPU.getSh1EntryIndexFromKernelStructureStart kernelStartIdx MPUEntryIndexidx in
  perform s := get in
  let entry :=  PipMPU.lookup Sh1Eidx s.(memory) PipMPU.beqIdx in
  match entry with
  | Some (SHE a) => ret a.(PDchild)
  | Some _ => undefined 12
  | None => undefined 11
  end.*)

Definition readSh1PDChildFromMPUEntryAddr (paddr : paddr) : LLI ADT.paddr :=
(* compute kernel start *)

(* MPU_entry_index = self.get_MPU_index(MPU_entry_address)
  # we compute the start of the kernel structure knowing the MPU's entry address and index
  kernel_structure_start = MPU_entry_address - MPU_entry_index * self.constants.MPU_entry_length
  return self.get_address_Sh1_PDchild_from_kernel_structure_start(kernel_structure_start, MPU_entry_index)*)
	perform MPUEntryIndex := readMPUIndexFromMPUEntry paddr in
	let MPUEntryIndexidx := CIndex MPUEntryIndex in

(* TODO : check if paddr - MPUEntryIndexidx*PipMPU.Constants.MPUEntryLength > 0 ? *)
	let kernelStartAddr := CPaddr (paddr - MPUEntryIndexidx*Constants.MPUEntryLength) in
perform Sh1EAddr := getSh1EntryAddrFromKernelStructureStart kernelStartAddr MPUEntryIndexidx in
  perform s := get in
  let entry :=  lookup Sh1EAddr s.(memory) beqAddr in
  match entry with
  | Some (SHE a) => ret a.(PDchild)
  | Some _ => undefined 12
  | None => undefined 11
  end.
Print readSh1PDChildFromMPUEntryAddr.

Definition writeSh1PDFlagFromMPUEntryAddr (paddr : paddr) (pdflag : bool) : LLI unit :=
(* compute kernel start *)

(* MPU_entry_index = self.get_MPU_index(MPU_entry_address)
  # we compute the start of the kernel structure knowing the MPU's entry address and index
  kernel_structure_start = MPU_entry_address - MPU_entry_index * self.constants.MPU_entry_length
  return self.get_address_Sh1_PDchild_from_kernel_structure_start(kernel_structure_start, MPU_entry_index)*)
	perform MPUEntryIndex := readMPUIndexFromMPUEntry paddr in
	let MPUEntryIndexidx := CIndex MPUEntryIndex in

(* TODO : check if paddr - MPUEntryIndexidx*Constants.MPUEntryLength > 0 ? *)
	let kernelStartAddr := CPaddr (paddr - MPUEntryIndexidx*Constants.MPUEntryLength) in
	perform Sh1EAddr := getSh1EntryAddrFromKernelStructureStart kernelStartAddr MPUEntryIndexidx in
  perform s := get in
  let entry :=  lookup Sh1EAddr s.(memory) beqAddr in
  match entry with
  | Some (SHE a) => let newEntry := {|	PDchild := a.(PDchild);
																			 	PDflag := pdflag;
																			 	inChildLocation := a.(inChildLocation)
																			|} in
											modify (fun s => {| currentPartition := s.(currentPartition);
																								memory := add paddr (SHE newEntry) s.(memory) beqAddr|} )
  | Some _ => undefined 12
  | None => undefined 11
  end.


Definition readSCOriginFromMPUEntryAddr  (paddr : paddr) : LLI ADT.paddr :=
  perform s := get in
  let entry :=  lookup paddr s.(memory) beqAddr in
  match entry with
  | Some (SCE a) => ret a.(origin)
  | Some _ => undefined 12
  | None => undefined 11
  end.

Definition readSCNextFromMPUEntryAddr  (paddr : paddr) : LLI ADT.paddr :=
  perform s := get in
  let entry :=  lookup paddr s.(memory) beqAddr in
  match entry with
  | Some (SCE a) => ret a.(next)
  | Some _ => undefined 12
  | None => undefined 11
  end. 

Definition eraseAddr (paddr : paddr): LLI unit :=
modify (fun s => {| currentPartition := s.(currentPartition);
	memory := removeDup paddr s.(memory) beqAddr|} ).

Definition writePDTable (pdtablepaddr : paddr) (newEntry : PDTable)  : LLI unit:=
  modify (fun s => {| 
			currentPartition := s.(currentPartition);
			memory := add pdtablepaddr (PDT newEntry) s.(memory) beqAddr|} ).

Definition getEmptyPDTable : LLI PDTable :=
	perform nullAddr := getNullAddr in
	let emptyPDTable := {| structure := nullAddr;
										firstfreeslot := nullAddr;
										nbfreeslots := 0;
										nbprepare := 0;
										parent := nullAddr |} in 
	ret emptyPDTable.

Definition readNextFromKernelStructureStart  (structurepaddr : paddr) : LLI paddr :=
	perform nextaddr :=  getNextAddrFromKernelStructureStart structurepaddr in (** Our last index is table size - 1, as we're indexed on zero*)
  perform s := get in
  let entry :=  lookup nextaddr s.(memory) beqAddr in
  match entry with
  | Some (PADDR a) => ret a
  | Some _ => undefined 12
  | None => undefined 11
  end.
