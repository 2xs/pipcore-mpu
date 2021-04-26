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
Require Export Model.MALInternal Model.ADT.
Require Import Model.Monad Model.Lib.
Require Import Arith Bool NPeano List Omega.

Open Scope mpu_state_scope.


(** Fixed fuel/timeout value to prove function termination *)
Definition N := 100.

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
																					parent := a.(parent);
																					MPU := a.(MPU)
																			|} in
											modify (fun s => {| currentPartition := s.(currentPartition);
																								memory := add pdtablepaddr (PDT newEntry) s.(memory) beqAddr|} )
		| Some _ => undefined 60
		| None => undefined 59
	end.

Definition readPDFirstFreeSlotPointer  (pdtablepaddr: paddr) : LLI paddr :=
  perform s := get in
  let entry :=  lookup pdtablepaddr s.(memory) beqAddr in
  match entry with
  | Some (PDT a) => ret a.(firstfreeslot)
  | Some _ => undefined 62
  | None => undefined 61
  end.

Definition writePDFirstFreeSlotPointer (pdtablepaddr: paddr) (firstfreeslotpaddr : paddr) : LLI unit :=
	perform s := get in
	let entry :=  lookup pdtablepaddr s.(memory) beqAddr in
	match entry with
		| Some (PDT a) =>  let newEntry := {| structure := a.(structure);
																					firstfreeslot := firstfreeslotpaddr;
																					nbfreeslots := a.(nbfreeslots);
																					nbprepare := a.(nbprepare);
																					parent := a.(parent);
																					MPU := a.(MPU)
																			|} in
											modify (fun s => {| currentPartition := s.(currentPartition);
																								memory := add pdtablepaddr (PDT newEntry) s.(memory) beqAddr|} )
		| Some _ => undefined 60
		| None => undefined 59
	end.

Definition readPDNbFreeSlots  (pdtablepaddr: paddr) : LLI index :=
  perform s := get in
  let entry :=  lookup pdtablepaddr s.(memory) beqAddr in
  match entry with
  | Some (PDT a) => ret a.(nbfreeslots)
  | Some _ => undefined 12
  | None => undefined 11
  end.

Definition writePDNbFreeSlots (pdtablepaddr: paddr) (nbfreeslots : index) : LLI unit :=
	perform s := get in
	let entry :=  lookup pdtablepaddr s.(memory) beqAddr in
	match entry with
		| Some (PDT a) =>  let newEntry := {| structure := a.(structure);
																					firstfreeslot := a.(firstfreeslot);
																					nbfreeslots := nbfreeslots;
																					nbprepare := a.(nbprepare);
																					parent := a.(parent);
																					MPU := a.(MPU)
																			|} in
											modify (fun s => {| currentPartition := s.(currentPartition);
																								memory := add pdtablepaddr (PDT newEntry) s.(memory) beqAddr|} )
		| Some _ => undefined 60
		| None => undefined 59
	end.

Definition readPDNbPrepare  (pdtablepaddr: paddr) : LLI index :=
  perform s := get in
  let entry :=  lookup pdtablepaddr s.(memory) beqAddr in
  match entry with
  | Some (PDT a) => ret a.(nbprepare)
  | Some _ => undefined 12
  | None => undefined 11
  end.

Definition writePDNbPrepare (pdtablepaddr: paddr) (nbprepare : index) : LLI unit :=
	perform s := get in
	let entry :=  lookup pdtablepaddr s.(memory) beqAddr in
	match entry with
		| Some (PDT a) =>  let newEntry := {| structure := a.(structure);
																					firstfreeslot := a.(firstfreeslot);
																					nbfreeslots := a.(nbfreeslots);
																					nbprepare := nbprepare;
																					parent := a.(parent);
																					MPU := a.(MPU)
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
																					parent := parent;
																					MPU := a.(MPU)
																			|} in
											modify (fun s => {| currentPartition := s.(currentPartition);
																								memory := add pdtablepaddr (PDT newEntry) s.(memory) beqAddr|} )
		| Some _ => undefined 60
		| None => undefined 59
	end.

Definition readPDMPU  (pdtablepaddr: paddr) : LLI (list paddr) :=
  perform s := get in
  let entry :=  lookup pdtablepaddr s.(memory) beqAddr in
  match entry with
  | Some (PDT a) => ret a.(MPU)
  | Some _ => undefined 62
  | None => undefined 61
  end.

Definition writePDMPU (pdtablepaddr: paddr) (MPUlist : list paddr) : LLI unit :=
	perform s := get in
	let entry :=  lookup pdtablepaddr s.(memory) beqAddr in
	match entry with
		| Some (PDT a) =>  let newEntry := {| structure := a.(structure);
																					firstfreeslot := a.(firstfreeslot);
																					nbfreeslots := a.(nbfreeslots);
																					nbprepare := a.(nbprepare);
																					parent := a.(parent);
																					MPU := MPUlist
																			|} in
											modify (fun s => {| currentPartition := s.(currentPartition);
																								memory := add pdtablepaddr (PDT newEntry) s.(memory) beqAddr|} )
		| Some _ => undefined 60
		| None => undefined 59
	end.

Definition readMPUStartFromMPUEntryAddr  (paddr : paddr) : LLI ADT.paddr :=
  perform s := get in
  let entry :=  lookup paddr s.(memory) beqAddr in
  match entry with
  | Some (MPUE a) => ret a.(mpublock).(startAddr)
  | Some _ => undefined 12
  | None => undefined 11
  end.

Definition writeMPUStartFromMPUEntryAddr  (paddr : paddr) (newstartaddr : ADT.paddr) : LLI unit :=
  perform s := get in
  let entry :=  lookup paddr s.(memory) beqAddr in
  match entry with
  | Some (MPUE a) => 	let endaddr := a.(mpublock).(endAddr) in
											let newblock := CBlock newstartaddr endaddr in
											let newEntry := {|	read := a.(read);
																			 	write := a.(write);
																			 	exec := a.(exec);
																			 	present := a.(present);
																			 	accessible := a.(accessible);
																			 	mpuindex := a.(mpuindex);
																			 	mpublock := newblock
																			|} in
											modify (fun s => {| currentPartition := s.(currentPartition);
																								memory := add paddr (MPUE newEntry) s.(memory) beqAddr|} )
		| Some _ => undefined 60
		| None => undefined 59
  end.

Definition readMPUEndFromMPUEntryAddr  (paddr : paddr) : LLI ADT.paddr :=
  perform s := get in
  let entry :=  lookup paddr s.(memory) beqAddr in
  match entry with
  | Some (MPUE a) => ret a.(mpublock).(endAddr)
  | Some _ => undefined 12
  | None => undefined 11
  end.

Definition writeMPUEndFromMPUEntryAddr  (paddr : paddr) (newendaddr : ADT.paddr) : LLI unit :=
  perform s := get in
  let entry :=  lookup paddr s.(memory) beqAddr in
  match entry with
  | Some (MPUE a) => 	let startaddr := a.(mpublock).(startAddr) in
											let newblock := CBlock startaddr newendaddr in
											let newEntry := {|	read := a.(read);
																			 	write := a.(write);
																			 	exec := a.(exec);
																			 	present := a.(present);
																			 	accessible := a.(accessible);
																			 	mpuindex := a.(mpuindex);
																			 	mpublock := newblock
																			|} in
											modify (fun s => {| currentPartition := s.(currentPartition);
																								memory := add paddr (MPUE newEntry) s.(memory) beqAddr|} )
		| Some _ => undefined 60
		| None => undefined 59
  end.

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

Definition writeMPUPresentFromMPUEntryAddr  (paddr : paddr) (presentbit  : bool) : LLI unit :=
  perform s := get in
  let entry :=  lookup paddr s.(memory) beqAddr in
  match entry with
  | Some (MPUE a) => let newEntry := {|	read := a.(read);
																			 	write := a.(write);
																			 	exec := a.(exec);
																			 	present := presentbit;
																			 	accessible := a.(accessible);
																			 	mpuindex := a.(mpuindex);
																			 	mpublock := a.(mpublock)
																			|} in
											modify (fun s => {| currentPartition := s.(currentPartition);
																								memory := add paddr (MPUE newEntry) s.(memory) beqAddr|} )
		| Some _ => undefined 60
		| None => undefined 59
  end.


Definition readMPUIndexFromMPUEntryAddr  (paddr : paddr) : LLI index :=
  perform s := get in
  let entry :=  lookup paddr s.(memory) beqAddr in
  match entry with
  | Some (MPUE a) => ret a.(mpuindex)
  | Some _ => undefined 12
  | None => undefined 11
  end.

Definition writeMPUIndexFromMPUEntryAddr  	(paddr : paddr) (newindex : index)
																					: LLI unit :=
  perform s := get in
  let entry :=  lookup paddr s.(memory) beqAddr in
  match entry with
  | Some (MPUE a) => let newEntry := {|	read := a.(read);
																			 	write := a.(write);
																			 	exec := a.(exec);
																			 	present := a.(present);
																			 	accessible := a.(accessible);
																			 	mpuindex := newindex;
																			 	mpublock := a.(mpublock)
																			|} in
											modify (fun s => {| currentPartition := s.(currentPartition);
																								memory := add paddr (MPUE newEntry) s.(memory) beqAddr|} )
		| Some _ => undefined 60
		| None => undefined 59
  end.

(*def write_MPU_entry(self, MPU_entry_address, start, end, accessible, present):
    """Writes at the MPU entry <MPU_entry_address> the values (<start>, <end>, <accessible bit>, <present bit>)"""
    # index (0), start (1), end (2), accessible (3), present (4)
    self.memory.write_int(MPU_entry_address + self.constants.kernel_structure_entries_bits, start)
    self.memory.write_int(MPU_entry_address + self.constants.kernel_structure_entries_bits + self.memory.size_of_int, end)
    self.memory.write_bit(MPU_entry_address + self.constants.kernel_structure_entries_bits + 2*self.memory.size_of_int, accessible)
    self.memory.write_bit(MPU_entry_address + self.constants.kernel_structure_entries_bits + 2*self.memory.size_of_int + 1, present)*)

Definition writeMPUEntryFromMPUEntryAddr (mpuentryaddr : paddr) (mpuentry : MPUEntry) : LLI unit :=
	writeMPUStartFromMPUEntryAddr mpuentryaddr mpuentry.(mpublock).(startAddr);;
	writeMPUEndFromMPUEntryAddr mpuentryaddr mpuentry.(mpublock).(endAddr);;
	writeMPUAccessibleFromMPUEntryAddr mpuentryaddr mpuentry.(accessible);;
	writeMPUPresentFromMPUEntryAddr mpuentryaddr mpuentry.(present);;
	ret tt.

(*def write_MPU_entry_with_index(self, MPU_entry_address, index, start, end, accessible, present):
    """Writes at the MPU entry <MPU_entry_address> the values (<index>, <start>, <end>, <accessible bit>, <present bit>)"""
    self.memory.write_bits(MPU_entry_address, index, self.constants.kernel_structure_entries_bits)
    self.write_MPU_entry(MPU_entry_address, start, end, accessible, present)*)
Definition writeMPUEntryWithIndexFromMPUEntryAddr 	(mpuentryaddr : paddr)
																									(mpuindex : index)
																									(mpuentry : MPUEntry) : LLI unit :=
	writeMPUEntryFromMPUEntryAddr mpuentryaddr mpuentry;;
	writeMPUIndexFromMPUEntryAddr mpuentryaddr mpuindex;;
	ret tt.

Definition getSh1EntryAddrFromMPUEntryAddr (mpuentryaddr : paddr) : LLI paddr :=
	perform MPUEntryIndex := readMPUIndexFromMPUEntryAddr mpuentryaddr in
	let MPUEntryIndexidx := CIndex MPUEntryIndex in
	perform kernelStartAddr := getKernelStructureStartAddr mpuentryaddr MPUEntryIndexidx in
	perform SHEAddr := getSh1EntryAddrFromKernelStructureStart kernelStartAddr MPUEntryIndexidx in
	ret SHEAddr.

Definition readSh1PDChildFromMPUEntryAddr (paddr : paddr) : LLI ADT.paddr :=
	perform Sh1EAddr := getSh1EntryAddrFromMPUEntryAddr paddr in
	perform s := get in
  let entry :=  lookup Sh1EAddr s.(memory) beqAddr in
  match entry with
  | Some (SHE a) => ret a.(PDchild)
  | Some _ => undefined 12
  | None => undefined 11
  end.

Definition writeSh1PDChildFromMPUEntryAddr (paddr : paddr) (pdchild : ADT.paddr) : LLI unit :=
	perform Sh1EAddr := getSh1EntryAddrFromMPUEntryAddr paddr in
  perform s := get in
  let entry :=  lookup Sh1EAddr s.(memory) beqAddr in
  match entry with
  | Some (SHE a) => let newEntry := {|	PDchild := pdchild;
																			 	PDflag := a.(PDflag);
																			 	inChildLocation := a.(inChildLocation)
																			|} in
											modify (fun s => {| currentPartition := s.(currentPartition);
																								memory := add paddr (SHE newEntry) s.(memory) beqAddr|} )
  | Some _ => undefined 12
  | None => undefined 11
  end.

Definition readSh1PDFlagFromMPUEntryAddr (paddr : paddr) : LLI bool :=
	perform Sh1EAddr := getSh1EntryAddrFromMPUEntryAddr paddr in
	perform s := get in
  let entry :=  lookup Sh1EAddr s.(memory) beqAddr in
  match entry with
  | Some (SHE a) => ret a.(PDflag)
  | Some _ => undefined 12
  | None => undefined 11
  end.

Definition writeSh1PDFlagFromMPUEntryAddr (paddr : paddr) (pdflag : bool) : LLI unit :=
	perform Sh1EAddr := getSh1EntryAddrFromMPUEntryAddr paddr in
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

Definition readSh1InChildLocationFromMPUEntryAddr (paddr : paddr) : LLI ADT.paddr :=
	perform Sh1EAddr := getSh1EntryAddrFromMPUEntryAddr paddr in
	perform s := get in
  let entry :=  lookup Sh1EAddr s.(memory) beqAddr in
  match entry with
  | Some (SHE a) => ret a.(inChildLocation)
  | Some _ => undefined 12
  | None => undefined 11
  end.

Definition writeSh1InChildLocationFromMPUEntryAddr (paddr : paddr)
																									(newinchildlocation : ADT.paddr)
																										 : LLI unit :=
	perform Sh1EAddr := getSh1EntryAddrFromMPUEntryAddr paddr in
  perform s := get in
  let entry :=  lookup Sh1EAddr s.(memory) beqAddr in
  match entry with
  | Some (SHE a) => let newEntry := {|	PDchild := a.(PDchild);
																			 	PDflag := a.(PDflag);
																			 	inChildLocation := newinchildlocation
																			|} in
											modify (fun s => {| currentPartition := s.(currentPartition);
																								memory := add paddr (SHE newEntry) s.(memory) beqAddr|} )
  | Some _ => undefined 12
  | None => undefined 11
  end.

Definition writeSh1EntryFromMPUEntryAddr (mpuentryaddr : paddr)
																				(sh1entry : Sh1Entry) : LLI unit :=
	writeSh1PDChildFromMPUEntryAddr mpuentryaddr sh1entry.(PDchild);;
	writeSh1PDFlagFromMPUEntryAddr mpuentryaddr sh1entry.(PDflag);;
	writeSh1InChildLocationFromMPUEntryAddr mpuentryaddr sh1entry.(inChildLocation);;
	ret tt.

Definition getSCEntryAddrFromMPUEntryAddr (mpuentryaddr : paddr) : LLI paddr :=
	perform MPUEntryIndex := readMPUIndexFromMPUEntryAddr mpuentryaddr in
	let MPUEntryIndexidx := CIndex MPUEntryIndex in
	perform kernelStartAddr := getKernelStructureStartAddr mpuentryaddr MPUEntryIndexidx in
	perform SCEAddr := getSCEntryAddrFromKernelStructureStart kernelStartAddr MPUEntryIndexidx in
	ret SCEAddr.

Definition readSCOriginFromMPUEntryAddr  (paddr : paddr) : LLI ADT.paddr :=
	perform SCEAddr := getSCEntryAddrFromMPUEntryAddr paddr in
  perform s := get in
  let entry :=  lookup SCEAddr s.(memory) beqAddr in
  match entry with
  | Some (SCE a) => ret a.(origin)
  | Some _ => undefined 12
  | None => undefined 11
  end.

Definition writeSCOriginFromMPUEntryAddr (paddr : paddr) (neworigin : ADT.paddr) : LLI unit :=
	perform SCEAddr := getSCEntryAddrFromMPUEntryAddr paddr in
  perform s := get in
  let entry :=  lookup SCEAddr s.(memory) beqAddr in
  match entry with
  | Some (SCE a) => let newEntry := {|	origin := neworigin;
																			 	next := a.(next)
																			|} in
											modify (fun s => {| currentPartition := s.(currentPartition);
																								memory := add paddr (SCE newEntry) s.(memory) beqAddr|} )
  | Some _ => undefined 12
  | None => undefined 11
  end.

Definition readSCNextFromMPUEntryAddr  (paddr : paddr) : LLI ADT.paddr :=
	perform SCEAddr := getSCEntryAddrFromMPUEntryAddr paddr in
  perform s := get in
  let entry :=  lookup SCEAddr s.(memory) beqAddr in
  match entry with
  | Some (SCE a) => ret a.(next)
  | Some _ => undefined 12
  | None => undefined 11
  end.

Definition writeSCNextFromMPUEntryAddr (paddr : paddr) (newnext : ADT.paddr) : LLI unit :=
	perform SCEAddr := getSCEntryAddrFromMPUEntryAddr paddr in
	perform s := get in
  let entry :=  lookup SCEAddr s.(memory) beqAddr in
  match entry with
  | Some (SCE a) => let newEntry := {|	origin := a.(origin);
																			 	next := newnext
																			|} in
											modify (fun s => {| currentPartition := s.(currentPartition);
																								memory := add paddr (SCE newEntry) s.(memory) beqAddr|} )
  | Some _ => undefined 12
  | None => undefined 11
  end.

Definition writeSCEntryFromMPUEntryAddr 	(mpuentryaddr : paddr)
																				(scentry : SCEntry)	: LLI unit :=
	writeSCOriginFromMPUEntryAddr mpuentryaddr scentry.(origin);;
	writeSCNextFromMPUEntryAddr mpuentryaddr scentry.(next);;
	ret tt.

Definition eraseAddr (paddr : paddr): LLI unit :=
modify (fun s => {| currentPartition := s.(currentPartition);
	memory := removeDup paddr s.(memory) beqAddr|} ).

Definition writePDTable (pdtablepaddr : paddr) (newEntry : PDTable)  : LLI unit:=
  modify (fun s => {| 
			currentPartition := s.(currentPartition);
			memory := add pdtablepaddr (PDT newEntry) s.(memory) beqAddr|} ).

Definition getEmptyPDTable : LLI PDTable :=
	perform nullAddr := getNullAddr in
	perform zero := Index.zero in
	let emptyPDTable := {| structure := nullAddr;
										firstfreeslot := nullAddr;
										nbfreeslots := zero;
										nbprepare := zero;
										parent := nullAddr;
										MPU := nil |} in 
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

Definition writeNextFromKernelStructureStart (structurepaddr : paddr) (newnext : ADT.paddr) : LLI unit :=
	perform nextaddr := getNextAddrFromKernelStructureStart structurepaddr in
  perform s := get in
  let entry :=  lookup nextaddr s.(memory) beqAddr in
  match entry with
  | Some (PADDR a) => modify (fun s => {| currentPartition := s.(currentPartition);
																				memory := add structurepaddr (PADDR newnext) s.(memory) beqAddr|})
  | Some _ => undefined 12
  | None => undefined 11
  end.

Definition getDefaultMPUEntry : LLI MPUEntry :=
	let emptyblock := CBlock nullAddr nullAddr in
	perform entriesnb := getKernelStructureEntriesNb in
	let emptyentry := {|	read := false;
										 	write := false;
										 	exec := false;
										 	present := false;
										 	accessible := false;
											(* default index is outside possible values*)
											mpuindex := entriesnb;
										 	mpublock := emptyblock
									|} in
	ret emptyentry.

Definition getDefaultSh1Entry : LLI Sh1Entry :=
	let emptyentry := {| PDchild := nullAddr;
											 PDflag := false;
											 inChildLocation := nullAddr
										|} in 
	ret emptyentry.

Definition getDefaultSCEntry : LLI SCEntry :=
	let emptyentry := {| origin := nullAddr;
											next := nullAddr 
										|} in 
	ret emptyentry.

Definition buildMPUEntry (startaddr endaddr : paddr) 
												(accessiblebit presentbit : bool): LLI MPUEntry :=
	perform defaultentry := getDefaultMPUEntry in
	let newblock := CBlock startaddr endaddr in
	let entry := {|	read := defaultentry.(read);
								 	write := defaultentry.(write);
								 	exec := defaultentry.(exec);
								 	present := presentbit;
								 	accessible := accessiblebit;
								 	mpuindex := defaultentry.(mpuindex);
								 	mpublock := newblock
								|} in
	ret entry.

Definition getPDStructurePointerAddrFromPD (pdAddr : paddr) : LLI paddr :=
	let structurePointerAddr := CPaddr (pdAddr + Constants.kernelstructureidx) in
	ret structurePointerAddr.

Fixpoint removeBlockFromList (mpuentryaddr : paddr) (realMPU : list paddr)
																															: list paddr :=
  match realMPU with
    | nil => realMPU
    | realentryaddr::l' =>if beqAddr realentryaddr mpuentryaddr
													then (* the entry should be removed, stop *)
														l'
													else (* entry is in the rest of the list *)
														realentryaddr::removeBlockFromList mpuentryaddr l'
  end.

Definition removeBlockFromPhysicalMPUIfNotAccessible (pd : paddr)
																								(mpuentryaddr : paddr)
																								(accessiblebit : bool) : LLI unit :=
	if negb accessiblebit then
	(* the block becomes inaccessible: remove from this pd's MPU configuration *)
		perform realMPU := readPDMPU pd in
		writePDMPU pd (removeBlockFromList mpuentryaddr realMPU)
	else ret tt.

(** The [eraseBlockAux] function recursively zeroes all addresses until it reaches
		the <startAddr>
		Stop condition: reached base address
    Processing: zeroes the current address
    Recursive calls: until base address
*)
Fixpoint eraseBlockAux 	(timeout : nat) (startAddr currentAddr : paddr): LLI unit :=
	match timeout with
		| 0 => ret tt (*Stop condition 1: reached end of structure list*)
		| S timeout1 =>	eraseAddr currentAddr ;; (*erase the current address*)
										if beqAddr currentAddr startAddr then
											(*Reached start address, no more addresses to erase*)
											ret tt
										else
											(*Continue to erase lower addresses*)
											perform predAddr := Paddr.pred currentAddr in
											eraseBlockAux timeout1 startAddr predAddr
end.

(** The [eraseBlock] function fixes the timeout value of [eraseBlockAux] *)
Definition eraseBlock (startAddr endAddr : paddr) : LLI bool :=
	perform isEndAddrBeforeStartAddr := Paddr.ltb endAddr startAddr in
	if isEndAddrBeforeStartAddr then ret false else
	eraseBlockAux N startAddr endAddr ;;
	ret true.
