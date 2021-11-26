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
     Memory Abstraction Layer : is the interface exposed to services to read and
    write data into physical memory  *)
Require Export Model.MALInternal Model.ADT.
Require Import Model.Monad Model.Lib.
Require Import Arith Bool NPeano List Omega.

Open Scope mpu_state_scope.

(** Fixed fuel/timeout value to prove function termination *)
Definition N := 100.

  (** The 'getCurPartition' function returns the current Partition from the current state *)
Definition getCurPartition : LLI paddr :=
	perform s := get in ret s.(currentPartition).

Definition getKernelStructureStartAddr (blockentryaddr : paddr) (blockindex : index) : LLI paddr :=
	(* compute kernel start *)
(* TODO : check if > 0 ? *)
	perform kernelStartAddr := Paddr.subPaddrIdx blockentryaddr blockindex in
	ret kernelStartAddr.

Definition getBlockEntryAddrFromKernelStructureStart (kernelStartAddr : paddr) (BlockEntryIndex : index) : LLI paddr :=
	let blockEntryAddr := CPaddr (kernelStartAddr + blkoffset + BlockEntryIndex) in
	ret blockEntryAddr.

Definition getSh1EntryAddrFromKernelStructureStart (kernelStartAddr : paddr) (BlockEntryIndex : index) : LLI paddr :=
	let sh1EntryAddr := CPaddr (kernelStartAddr + sh1offset + BlockEntryIndex) in
	ret sh1EntryAddr.

Definition getSCEntryAddrFromKernelStructureStart (kernelStartAddr : paddr) (BlockEntryIndex : index) : LLI paddr :=
	let scEntryAddr := CPaddr (kernelStartAddr + scoffset + BlockEntryIndex) in
	ret scEntryAddr.

Definition readPDTable (paddr : paddr)  : LLI PDTable :=
	perform s := get in
  let entry :=  lookup paddr s.(memory) beqAddr in
  match entry with
  | Some (PDT a) => ret a
  | Some _ => undefined 5
  | None => undefined 4
  end.

Definition getPDTRecordField {Y : Type} (field : PDTable -> Y) (pdtablepaddr : paddr) : LLI Y :=
	perform s := get in
  let entry :=  lookup pdtablepaddr s.(memory) beqAddr in
  match entry with
  | Some (PDT a) => ret a.(field)
  | Some _ => undefined 12
  | None => undefined 11
  end.
(*
Definition readPDStructurePointer  (pdtablepaddr: paddr) : LLI paddr :=
  perform s := get in
  let entry :=  lookup pdtablepaddr s.(memory) beqAddr in
  match entry with
  | Some (PDT a) => ret a.(structure)
  | Some _ => undefined 12
  | None => undefined 11
  end.*)
Definition readPDStructurePointer (pdtablepaddr: paddr) : LLI paddr :=
	getPDTRecordField structure pdtablepaddr.

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
(*
Definition readPDFirstFreeSlotPointer  (pdtablepaddr: paddr) : LLI paddr :=
  perform s := get in
  let entry :=  lookup pdtablepaddr s.(memory) beqAddr in
  match entry with
  | Some (PDT a) => ret a.(firstfreeslot)
  | Some _ => undefined 62
  | None => undefined 61
  end.*)
Definition readPDFirstFreeSlotPointer (pdtablepaddr: paddr) : LLI paddr :=
	getPDTRecordField firstfreeslot pdtablepaddr.

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
(*
Definition readPDNbFreeSlots  (pdtablepaddr: paddr) : LLI index :=
  perform s := get in
  let entry :=  lookup pdtablepaddr s.(memory) beqAddr in
  match entry with
  | Some (PDT a) => ret a.(nbfreeslots)
  | Some _ => undefined 12
  | None => undefined 11
  end.*)
Definition readPDNbFreeSlots (pdtablepaddr: paddr) : LLI index :=
	getPDTRecordField nbfreeslots pdtablepaddr.

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

(*
Definition readPDNbPrepare  (pdtablepaddr: paddr) : LLI index :=
  perform s := get in
  let entry :=  lookup pdtablepaddr s.(memory) beqAddr in
  match entry with
  | Some (PDT a) => ret a.(nbprepare)
  | Some _ => undefined 12
  | None => undefined 11
  end.*)
Definition readPDNbPrepare (pdtablepaddr: paddr) : LLI index :=
	getPDTRecordField nbprepare pdtablepaddr.

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
(*
Definition readPDParent  (pdtablepaddr: paddr) : LLI paddr :=
  perform s := get in
  let entry :=  lookup pdtablepaddr s.(memory) beqAddr in
  match entry with
  | Some (PDT a) => ret a.(parent)
  | Some _ => undefined 12
  | None => undefined 11
  end.*)
Definition readPDParent (pdtablepaddr: paddr) : LLI paddr :=
	getPDTRecordField parent pdtablepaddr.

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
(*
Definition readPDMPU  (pdtablepaddr: paddr) : LLI (list paddr) :=
  perform s := get in
  let entry :=  lookup pdtablepaddr s.(memory) beqAddr in
  match entry with
  | Some (PDT a) => ret a.(MPU)
  | Some _ => undefined 62
  | None => undefined 61
  end.*)
Definition readPDMPU (pdtablepaddr: paddr) : LLI (list paddr) :=
	getPDTRecordField MPU pdtablepaddr.

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

(*
Definition readBlockStartFromBlockEntryAddr  (paddr : paddr) : LLI ADT.paddr :=
  perform s := get in
  let entry :=  lookup paddr s.(memory) beqAddr in
  match entry with
  | Some (BE a) => ret a.(blockrange).(startAddr)
  | Some _ => undefined 12
  | None => undefined 11
  end.*)

Definition writeBlockStartFromBlockEntryAddr  (paddr : paddr) (newstartaddr : ADT.paddr) : LLI unit :=
  perform s := get in
  let entry :=  lookup paddr s.(memory) beqAddr in
  match entry with
  | Some (BE a) => 	let endaddr := a.(blockrange).(endAddr) in
											let newblock := CBlock newstartaddr endaddr in
											(*let newEntry := {|	read := a.(read);
																			 	write := a.(write);
																			 	exec := a.(exec);
																			 	present := a.(present);
																			 	accessible := a.(accessible);
																			 	blockindex := a.(blockindex);
																			 	blockrange := newblock
																			|} in*)
											let newEntry := CBlockEntry a.(read)
																									a.(write)
																									a.(exec)
																			 						a.(present)
																									a.(accessible)
																			 						a.(blockindex)
																									newblock in
											modify (fun s => {| currentPartition := s.(currentPartition);
																								memory := add paddr (BE newEntry) s.(memory) beqAddr|} )
		| Some _ => undefined 60
		| None => undefined 59
  end.

(*
Definition readBlockEndFromBlockEntryAddr  (paddr : paddr) : LLI ADT.paddr :=
  perform s := get in
  let entry :=  lookup paddr s.(memory) beqAddr in
  match entry with
  | Some (BE a) => ret a.(blockrange).(endAddr)
  | Some _ => undefined 12
  | None => undefined 11
  end.
*)

Definition writeBlockEndFromBlockEntryAddr  (paddr : paddr) (newendaddr : ADT.paddr) : LLI unit :=
  perform s := get in
  let entry :=  lookup paddr s.(memory) beqAddr in
  match entry with
  | Some (BE a) => 	let startaddr := a.(blockrange).(startAddr) in
											let newblock := CBlock startaddr newendaddr in
											(*let newEntry := {|	read := a.(read);
																			 	write := a.(write);
																			 	exec := a.(exec);
																			 	present := a.(present);
																			 	accessible := a.(accessible);
																			 	blockindex := a.(blockindex);
																			 	blockrange := newblock
																			|} in*)
											let newEntry := CBlockEntry a.(read)
																									a.(write)
																									a.(exec)
																			 						a.(present)
																									a.(accessible)
																			 						a.(blockindex)
																									newblock in
											modify (fun s => {| currentPartition := s.(currentPartition);
																								memory := add paddr (BE newEntry) s.(memory) beqAddr|} )
		| Some _ => undefined 60
		| None => undefined 59
  end.

Definition getBlockRecordField {Y : Type} (field : BlockEntry -> Y) (addr : paddr) : LLI Y :=
	perform s := get in
  let entry :=  lookup addr s.(memory) beqAddr in
  match entry with
  | Some (BE a) => ret a.(field)
  | Some _ => undefined 12
  | None => undefined 11
  end.

Definition readBlockStartFromBlockEntryAddr  (addr : paddr) : LLI paddr :=
	perform blockrange := getBlockRecordField blockrange addr in
	ret (blockrange.(startAddr)).

Definition readBlockEndFromBlockEntryAddr  (addr : paddr) : LLI paddr :=
	perform blockrange := getBlockRecordField blockrange addr in
	ret (blockrange.(endAddr)).

(*
Definition readBlockAccessibleFromBlockEntryAddr  (paddr : paddr) : LLI bool :=
  perform s := get in
  let entry :=  lookup paddr s.(memory) beqAddr in
  match entry with
  | Some (BE a) => ret a.(accessible)
  | Some _ => undefined 12
  | None => undefined 11
  end.*)
Definition readBlockAccessibleFromBlockEntryAddr  (addr : paddr) : LLI bool :=
	getBlockRecordField accessible addr.

Definition writeBlockAccessibleFromBlockEntryAddr  (paddr : paddr) (accessiblebit  : bool) : LLI unit :=
  perform s := get in
  let entry :=  lookup paddr s.(memory) beqAddr in
  match entry with
  | Some (BE a) => (*let newEntry := {|	read := a.(read);
																			 	write := a.(write);
																			 	exec := a.(exec);
																			 	present := a.(present);
																			 	accessible := accessiblebit;
																			 	blockindex := a.(blockindex);
																			 	blockrange := a.(blockrange)
																			|} in*)
										let newEntry := CBlockEntry a.(read)
																								a.(write)
																								a.(exec)
																		 						a.(present)
																								accessiblebit
																		 						a.(blockindex)
																								a.(blockrange) in
											modify (fun s => {| currentPartition := s.(currentPartition);
																								memory := add paddr (BE newEntry) s.(memory) beqAddr|} )
		| Some _ => undefined 60
		| None => undefined 59
  end.

(*
Definition readBlockPresentFromBlockEntryAddr  (paddr : paddr) : LLI bool :=
  perform s := get in
  let entry :=  lookup paddr s.(memory) beqAddr in
  match entry with
  | Some (BE a) => ret a.(present)
  | Some _ => undefined 12
  | None => undefined 11
  end.
*)

Definition readBlockPresentFromBlockEntryAddr  (addr : paddr) : LLI bool :=
	getBlockRecordField present addr.

Definition writeBlockPresentFromBlockEntryAddr  (paddr : paddr) (presentbit  : bool) : LLI unit :=
  perform s := get in
  let entry :=  lookup paddr s.(memory) beqAddr in
  match entry with
  | Some (BE a) => (*let newEntry := {|	read := a.(read);
																			 	write := a.(write);
																			 	exec := a.(exec);
																			 	present := presentbit;
																			 	accessible := a.(accessible);
																			 	blockindex := a.(blockindex);
																			 	blockrange := a.(blockrange)
																			|} in*)
										let newEntry := CBlockEntry a.(read)
																								a.(write)
																								a.(exec)
																		 						presentbit
																								a.(accessible)
																		 						a.(blockindex)
																								a.(blockrange) in
											modify (fun s => {| currentPartition := s.(currentPartition);
																								memory := add paddr (BE newEntry) s.(memory) beqAddr|} )
		| Some _ => undefined 60
		| None => undefined 59
  end.

(*
Definition readBlockIndexFromBlockEntryAddr  (paddr : paddr) : LLI index :=
  perform s := get in
  let entry :=  lookup paddr s.(memory) beqAddr in
  match entry with
  | Some (BE a) => ret a.(blockindex)
  | Some _ => undefined 12
  | None => undefined 11
  end.*)

Definition readBlockIndexFromBlockEntryAddr  (addr : paddr) : LLI index :=
	getBlockRecordField blockindex addr.

Definition writeBlockIndexFromBlockEntryAddr  	(paddr : paddr) (newindex : index)
																					: LLI unit :=
  perform s := get in
  let entry :=  lookup paddr s.(memory) beqAddr in
  match entry with
  | Some (BE a) => (*let newEntry := {|	read := a.(read);
																			 	write := a.(write);
																			 	exec := a.(exec);
																			 	present := a.(present);
																			 	accessible := a.(accessible);
																			 	blockindex := newindex;
																			 	blockrange := a.(blockrange)
																			|} in*)
										let newEntry := CBlockEntry a.(read)
																								a.(write)
																								a.(exec)
																		 						a.(present)
																								a.(accessible)
																		 						newindex
																								a.(blockrange) in
											modify (fun s => {| currentPartition := s.(currentPartition);
																								memory := add paddr (BE newEntry) s.(memory) beqAddr|} )
		| Some _ => undefined 60
		| None => undefined 59
  end.

(*
Definition readBlockRFromBlockEntryAddr  (paddr : paddr) : LLI bool :=
  perform s := get in
  let entry :=  lookup paddr s.(memory) beqAddr in
  match entry with
  | Some (BE a) => ret a.(read)
  | Some _ => undefined 12
  | None => undefined 11
  end.*)

Definition readBlockRFromBlockEntryAddr  (addr : paddr) : LLI bool :=
	getBlockRecordField read addr.


Definition writeBlockRFromBlockEntryAddr (paddr : paddr) (newread : bool) : LLI unit :=
  perform s := get in
  let entry :=  lookup paddr s.(memory) beqAddr in
  match entry with
  | Some (BE a) => (*let newEntry := {|	read := newread;
																			 	write := a.(write);
																			 	exec := a.(exec);
																			 	present := a.(present);
																			 	accessible := a.(accessible);
																			 	blockindex := a.(blockindex);
																			 	blockrange := a.(blockrange)
																			|} in*)
										let newEntry := CBlockEntry newread
																								a.(write)
																								a.(exec)
																	 							a.(present)
																								a.(accessible)
																	 							a.(blockindex)
																								a.(blockrange) in
											modify (fun s => {| currentPartition := s.(currentPartition);
																								memory := add paddr (BE newEntry) s.(memory) beqAddr|} )
		| Some _ => undefined 60
		| None => undefined 59
  end.

(*
Definition readBlockWFromBlockEntryAddr  (paddr : paddr) : LLI bool :=
  perform s := get in
  let entry :=  lookup paddr s.(memory) beqAddr in
  match entry with
  | Some (BE a) => ret a.(write)
  | Some _ => undefined 12
  | None => undefined 11
  end.*)
Definition readBlockWFromBlockEntryAddr  (addr : paddr) : LLI bool :=
	getBlockRecordField write addr.

Definition writeBlockWFromBlockEntryAddr (paddr : paddr) (newwrite : bool) : LLI unit :=
  perform s := get in
  let entry :=  lookup paddr s.(memory) beqAddr in
  match entry with
  | Some (BE a) => (*let newEntry := {|	read := a.(read);
																			 	write := newwrite;
																			 	exec := a.(exec);
																			 	present := a.(present);
																			 	accessible := a.(accessible);
																			 	blockindex := a.(blockindex);
																			 	blockrange := a.(blockrange)
																			|} in*)
										let newEntry := CBlockEntry a.(read)
																								newwrite
																								a.(exec)
																	 							a.(present)
																								a.(accessible)
																	 							a.(blockindex)
																								a.(blockrange) in
											modify (fun s => {| currentPartition := s.(currentPartition);
																								memory := add paddr (BE newEntry) s.(memory) beqAddr|} )
		| Some _ => undefined 60
		| None => undefined 59
  end.

(*
Definition readBlockXFromBlockEntryAddr  (paddr : paddr) : LLI bool :=
  perform s := get in
  let entry :=  lookup paddr s.(memory) beqAddr in
  match entry with
  | Some (BE a) => ret a.(exec)
  | Some _ => undefined 12
  | None => undefined 11
  end.*)

Definition readBlockXFromBlockEntryAddr  (addr : paddr) : LLI bool :=
	getBlockRecordField exec addr.

Definition writeBlockXFromBlockEntryAddr (paddr : paddr) (newexec : bool) : LLI unit :=
  perform s := get in
  let entry :=  lookup paddr s.(memory) beqAddr in
  match entry with
  | Some (BE a) => (*let newEntry := {|	read := a.(read);
																			 	write := a.(write);
																			 	exec := newexec;
																			 	present := a.(present);
																			 	accessible := a.(accessible);
																			 	blockindex := a.(blockindex);
																			 	blockrange := a.(blockrange)
																			|} in*)
										let newEntry := CBlockEntry a.(read)
																								a.(write)
																								newexec
																	 							a.(present)
																								a.(accessible)
																	 							a.(blockindex)
																								a.(blockrange) in
											modify (fun s => {| currentPartition := s.(currentPartition);
																								memory := add paddr (BE newEntry) s.(memory) beqAddr|} )
		| Some _ => undefined 60
		| None => undefined 59
  end.

Definition readBlockEntryFromBlockEntryAddr  (paddr : paddr) : LLI BlockEntry :=
  perform s := get in
  let entry :=  lookup paddr s.(memory) beqAddr in
  match entry with
  | Some (BE a) => ret a
  | Some _ => undefined 12
  | None => undefined 11
  end.


Definition writeBlockEntryFromBlockEntryAddr (blockentryaddr : paddr) (blockentry : BlockEntry) : LLI unit :=
	writeBlockStartFromBlockEntryAddr blockentryaddr blockentry.(blockrange).(startAddr);;
	writeBlockEndFromBlockEntryAddr blockentryaddr blockentry.(blockrange).(endAddr);;
	writeBlockAccessibleFromBlockEntryAddr blockentryaddr blockentry.(accessible);;
	writeBlockPresentFromBlockEntryAddr blockentryaddr blockentry.(present);;
	writeBlockRFromBlockEntryAddr blockentryaddr blockentry.(read);;
	writeBlockWFromBlockEntryAddr blockentryaddr blockentry.(write);;
	writeBlockXFromBlockEntryAddr blockentryaddr blockentry.(exec);;
	ret tt.

Definition writeBlockEntryWithIndexFromBlockEntryAddr 	(blockentryaddr : paddr)
																									(blockindex : index)
																									(blockentry : BlockEntry) : LLI unit :=
	writeBlockEntryFromBlockEntryAddr blockentryaddr blockentry;;
	writeBlockIndexFromBlockEntryAddr blockentryaddr blockindex;;
	ret tt.

Definition getSh1EntryAddrFromBlockEntryAddr (blockentryaddr : paddr) : LLI paddr :=
	perform BlockEntryIndex := readBlockIndexFromBlockEntryAddr blockentryaddr in
	perform kernelStartAddr := getKernelStructureStartAddr blockentryaddr BlockEntryIndex in
	perform SHEAddr := getSh1EntryAddrFromKernelStructureStart kernelStartAddr BlockEntryIndex in
	ret SHEAddr.

Definition getSh1RecordField {Y : Type} (field : Sh1Entry -> Y) (addr : paddr) : LLI Y :=
	perform s := get in
  let entry :=  lookup addr s.(memory) beqAddr in
  match entry with
  | Some (SHE a) => ret a.(field)
  | Some _ => undefined 12
  | None => undefined 11
  end.

(*
Definition readSh1PDChildFromBlockEntryAddr2 (Sh1EAddr : paddr) : LLI paddr :=
	perform s := get in
  let entry :=  lookup Sh1EAddr s.(memory) beqAddr in
  match entry with
  | Some (SHE a) => ret a.(PDchild)
  | Some _ => undefined 12
  | None => undefined 11
  end.

Definition readSh1PDChildFromBlockEntryAddr (blockentryaddr : paddr) : LLI paddr :=
	perform Sh1EAddr := getSh1EntryAddrFromBlockEntryAddr blockentryaddr in
	perform pdchild := readSh1PDChildFromBlockEntryAddr2 Sh1EAddr in
	ret pdchild.
*)

Definition readSh1PDChildFromBlockEntryAddr (blockentryaddr : paddr) : LLI paddr :=
	perform Sh1EAddr := getSh1EntryAddrFromBlockEntryAddr blockentryaddr in
	perform pdchild := getSh1RecordField PDchild Sh1EAddr in
	ret pdchild.

Definition writeSh1PDChildFromBlockEntryAddr2 (Sh1EAddr pdchild : paddr) : LLI unit :=
  perform s := get in
  let entry :=  lookup Sh1EAddr s.(memory) beqAddr in
  match entry with
  | Some (SHE a) => let newEntry := {|	PDchild := pdchild;
																			 	PDflag := a.(PDflag);
																			 	inChildLocation := a.(inChildLocation)
																			|} in
											modify (fun s => {| currentPartition := s.(currentPartition);
																								memory := add Sh1EAddr (SHE newEntry) s.(memory) beqAddr|} )
  | Some _ => undefined 12
  | None => undefined 11
  end.

Definition writeSh1PDChildFromBlockEntryAddr (blockentryaddr pdchild : paddr) : LLI unit :=
	perform Sh1EAddr := getSh1EntryAddrFromBlockEntryAddr blockentryaddr in
  writeSh1PDChildFromBlockEntryAddr2 Sh1EAddr pdchild.


(*
Definition readSh1PDFlagFromBlockEntryAddr2 (Sh1EAddr : paddr) : LLI bool :=
	perform s := get in
  let entry :=  lookup Sh1EAddr s.(memory) beqAddr in
  match entry with
  | Some (SHE a) => ret a.(PDflag)
  | Some _ => undefined 12
  | None => undefined 11
  end.

Definition readSh1PDFlagFromBlockEntryAddr (paddr : paddr) : LLI bool :=
	perform Sh1EAddr := getSh1EntryAddrFromBlockEntryAddr paddr in
	perform pdflag := readSh1PDFlagFromBlockEntryAddr2 Sh1EAddr in
	ret pdflag.
*)

Definition readSh1PDFlagFromBlockEntryAddr (blockentryaddr : paddr) : LLI bool :=
	perform Sh1EAddr := getSh1EntryAddrFromBlockEntryAddr blockentryaddr in
	perform pdflag := getSh1RecordField PDflag Sh1EAddr in
	ret pdflag.

Definition writeSh1PDFlagFromBlockEntryAddr (paddr : paddr) (pdflag : bool) : LLI unit :=
	perform Sh1EAddr := getSh1EntryAddrFromBlockEntryAddr paddr in
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


(*
Definition readSh1InChildLocationFromBlockEntryAddr2 (Sh1EAddr : paddr) : LLI ADT.paddr :=
	perform s := get in
  let entry :=  lookup Sh1EAddr s.(memory) beqAddr in
  match entry with
  | Some (SHE a) => ret a.(inChildLocation)
  | Some _ => undefined 12
  | None => undefined 11
  end.

Definition readSh1InChildLocationFromBlockEntryAddr (paddr : paddr) : LLI ADT.paddr :=
	perform Sh1EAddr := getSh1EntryAddrFromBlockEntryAddr paddr in
	perform inchildlocation := readSh1InChildLocationFromBlockEntryAddr2 Sh1EAddr in
	ret inchildlocation.*)

Definition readSh1InChildLocationFromBlockEntryAddr (blockentryaddr : paddr) : LLI paddr :=
	perform Sh1EAddr := getSh1EntryAddrFromBlockEntryAddr blockentryaddr in
	perform inchildlocation := getSh1RecordField inChildLocation Sh1EAddr in
	ret inchildlocation.


Definition writeSh1InChildLocationFromBlockEntryAddr2 	(Sh1EAddr : paddr)
																											(newinchildlocation : paddr)
																										 : LLI unit :=
  perform s := get in
  let entry :=  lookup Sh1EAddr s.(memory) beqAddr in
  match entry with
  | Some (SHE a) => let newEntry := {|	PDchild := a.(PDchild);
																			 	PDflag := a.(PDflag);
																			 	inChildLocation := newinchildlocation
																			|} in
											modify (fun s => {| currentPartition := s.(currentPartition);
																								memory := add Sh1EAddr (SHE newEntry) s.(memory) beqAddr|} )
  | Some _ => undefined 12
  | None => undefined 11
  end.

Definition writeSh1InChildLocationFromBlockEntryAddr (blockentryaddr : paddr)
																										(newinchildlocation : ADT.paddr)
																										 : LLI unit :=
	perform Sh1EAddr := getSh1EntryAddrFromBlockEntryAddr blockentryaddr in
	writeSh1InChildLocationFromBlockEntryAddr2 Sh1EAddr newinchildlocation.

Definition writeSh1EntryFromBlockEntryAddr (blockentryaddr : paddr)
																				(sh1entry : Sh1Entry) : LLI unit :=
	writeSh1PDChildFromBlockEntryAddr blockentryaddr sh1entry.(PDchild);;
	writeSh1PDFlagFromBlockEntryAddr blockentryaddr sh1entry.(PDflag);;
	writeSh1InChildLocationFromBlockEntryAddr blockentryaddr sh1entry.(inChildLocation);;
	ret tt.

Definition getSCEntryAddrFromBlockEntryAddr (blockentryaddr : paddr) : LLI paddr :=
	perform BlockEntryIndex := readBlockIndexFromBlockEntryAddr blockentryaddr in
	perform kernelStartAddr := getKernelStructureStartAddr blockentryaddr BlockEntryIndex in
	perform SCEAddr := getSCEntryAddrFromKernelStructureStart kernelStartAddr BlockEntryIndex in
	ret SCEAddr.

Definition getSCRecordField {Y : Type} (field : SCEntry -> Y) (addr : paddr) : LLI Y :=
	perform s := get in
  let entry :=  lookup addr s.(memory) beqAddr in
  match entry with
  | Some (SCE a) => ret a.(field)
  | Some _ => undefined 12
  | None => undefined 11
  end.

(*Definition readSCOriginFromBlockEntryAddr2  (SCEAddr : paddr) : LLI paddr :=
  perform s := get in
  let entry :=  lookup SCEAddr s.(memory) beqAddr in
  match entry with
  | Some (SCE a) => ret a.(origin)
  | Some _ => undefined 12
  | None => undefined 11
  end.

Definition readSCOriginFromBlockEntryAddr  (blockentryaddr : paddr) : LLI paddr :=
	perform SCEAddr := getSCEntryAddrFromBlockEntryAddr blockentryaddr in
  perform origin := readSCOriginFromBlockEntryAddr2 SCEAddr in
	ret origin.
*)

Definition readSCOriginFromBlockEntryAddr (blockentryaddr : paddr) : LLI paddr :=
	perform SCEAddr := getSCEntryAddrFromBlockEntryAddr blockentryaddr in
	perform origin := getSCRecordField origin SCEAddr in
	ret origin.

Definition writeSCOriginFromBlockEntryAddr2 (neworigin SCEAddr : paddr) : LLI unit :=
  perform s := get in
  let entry :=  lookup SCEAddr s.(memory) beqAddr in
  match entry with
  | Some (SCE a) => let newEntry := {|	origin := neworigin;
																			 	next := a.(next)
																			|} in
											modify (fun s => {| currentPartition := s.(currentPartition);
																								memory := add SCEAddr (SCE newEntry) s.(memory) beqAddr|} )
  | Some _ => undefined 12
  | None => undefined 11
  end.

Definition writeSCOriginFromBlockEntryAddr (blockentryaddr neworigin : paddr) : LLI unit :=
	perform SCEAddr := getSCEntryAddrFromBlockEntryAddr blockentryaddr in
	writeSCOriginFromBlockEntryAddr2 neworigin SCEAddr.


(*
Definition readSCNextFromBlockEntryAddr2  (SCEAddr : paddr) : LLI paddr :=
  perform s := get in
  let entry :=  lookup SCEAddr s.(memory) beqAddr in
  match entry with
  | Some (SCE a) => ret a.(next)
  | Some _ => undefined 12
  | None => undefined 11
  end.

Definition readSCNextFromBlockEntryAddr  (blockentryaddr : paddr) : LLI paddr :=
	perform SCEAddr := getSCEntryAddrFromBlockEntryAddr blockentryaddr in
  perform next := readSCNextFromBlockEntryAddr2 SCEAddr in
	ret next.
*)

Definition readSCNextFromBlockEntryAddr (blockentryaddr : paddr) : LLI paddr :=
	perform SCEAddr := getSCEntryAddrFromBlockEntryAddr blockentryaddr in
	perform next := getSCRecordField next SCEAddr in
	ret next.


Definition writeSCNextFromBlockEntryAddr (paddr : paddr) (newnext : ADT.paddr) : LLI unit :=
	perform SCEAddr := getSCEntryAddrFromBlockEntryAddr paddr in
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

Definition writeSCEntryFromBlockEntryAddr 	(blockentryaddr : paddr)
																				(scentry : SCEntry)	: LLI unit :=
	writeSCOriginFromBlockEntryAddr blockentryaddr scentry.(origin);;
	writeSCNextFromBlockEntryAddr blockentryaddr scentry.(next);;
	ret tt.

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

Definition getNextAddrFromKernelStructureStart (kernelStartAddr : paddr) : LLI paddr :=
	let nextAddr := CPaddr (kernelStartAddr + nextoffset) in
	ret nextAddr.

Definition readNextFromKernelStructureStart2  (nextaddr : paddr) : LLI paddr :=
	perform s := get in
  let entry :=  lookup nextaddr s.(memory) beqAddr in
  match entry with
  | Some (PADDR a) => ret a
  | Some _ => undefined 12
  | None => undefined 11
  end.

Definition readNextFromKernelStructureStart  (structurepaddr : paddr) : LLI paddr :=
	perform nextaddr :=  getNextAddrFromKernelStructureStart structurepaddr in (** Our last index is table size - 1, as we're indexed on zero*)
  perform nextkernelstructure := readNextFromKernelStructureStart2 nextaddr in
	ret nextkernelstructure.

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

Definition getDefaultBlockEntry : LLI BlockEntry :=
	let emptyblock := CBlock nullAddr nullAddr in
	perform entriesnb := getKernelStructureEntriesNb in
	(*let emptyentry := {|	read := false;
										 	write := false;
										 	exec := false;
										 	present := false;
										 	accessible := false;
											(* default index is outside possible values*)
											blockindex := entriesnb;
										 	blockrange := emptyblock
									|} in*)
	let emptyentry := CBlockEntry false
															false
															false
								 							false
															false
															(* default index is outside possible values*)
								 							entriesnb
															emptyblock in
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

Definition buildBlockEntry (startaddr endaddr : paddr)
													(accessiblebit presentbit : bool): LLI BlockEntry :=
	perform defaultentry := getDefaultBlockEntry in
	let newblock := CBlock startaddr endaddr in
	(*let entry := {|	read := defaultentry.(read);
								 	write := defaultentry.(write);
								 	exec := defaultentry.(exec);
								 	present := presentbit;
								 	accessible := accessiblebit;
								 	blockindex := defaultentry.(blockindex);
								 	blockrange := newblock
								|} in*)
	let entry := CBlockEntry 	defaultentry.(read)
														defaultentry.(write)
														defaultentry.(exec)
						 								presentbit
														accessiblebit
						 								defaultentry.(blockindex)
														newblock in
	ret entry.

Definition getPDStructurePointerAddrFromPD (pdAddr : paddr) : LLI paddr :=
	let structurePointerAddr := CPaddr (pdAddr + Constants.kernelstructureidx) in
	ret structurePointerAddr.

Definition readBlockFromPhysicalMPU (pd : paddr) (index : index) : LLI paddr :=
	perform realMPU := readPDMPU pd in
	ret (readElementAt index realMPU nullAddr).

Fixpoint removeBlockFromPhysicalMPUAux (blockentryaddr : paddr) (realMPU : list paddr)
																															: list paddr :=
  match realMPU with
    | nil => realMPU
    | realentryaddr::l' =>if beqAddr realentryaddr blockentryaddr
													then (* the entry should be removed, stop *)
														l'
													else (* entry is in the rest of the list *)
														realentryaddr::removeBlockFromPhysicalMPUAux blockentryaddr l'
  end.

Definition removeBlockFromPhysicalMPU (pd : paddr) (blockentryaddr : paddr)
																															: LLI unit :=
	perform realMPU := readPDMPU pd in
	writePDMPU pd (removeBlockFromPhysicalMPUAux blockentryaddr realMPU) ;;
	ret tt.

Definition removeBlockFromPhysicalMPUIfNotAccessible (pd : paddr)
																										(blockentryaddr : paddr)
																										(accessiblebit : bool)
																																	: LLI unit :=
	if negb accessiblebit then
	(* the block becomes inaccessible: remove from this pd's MPU configuration *)
		removeBlockFromPhysicalMPU pd blockentryaddr ;;
		ret tt
	else ret tt.

(** The [replaceBlockInPhysicalMPU] function replaces the physical MPU's <MPURegionNb>
region by the new block <blockentryaddr> in the partition <pd>*)
Definition replaceBlockInPhysicalMPU (pd : paddr)
																		(blockentryaddr : paddr)
																		(MPURegionNb : index)
																																	: LLI unit :=
	perform realMPU := readPDMPU pd in
	writePDMPU pd (addElementAt MPURegionNb blockentryaddr realMPU nullAddr) ;;
	ret tt.


(** The [findBlockIdxInPhysicalMPU] function finds the MPU region number of the
		<blockToFound> within the physical MPU of <idPD>, else returns <defaultidx>.
*)
Definition findBlockIdxInPhysicalMPU 	(idPD : paddr)
																		(blockToFind : paddr)
																		(defaultidx : index) : LLI index :=
	perform realMPU := readPDMPU idPD in
	perform zero := Index.zero in
  let foundidx := indexOf blockToFind zero realMPU beqAddr defaultidx in
	ret (CIndex foundidx).


(** The [eraseBlockAux] function recursively zeroes all addresses until it reaches
		the <startAddr>
		Stop condition: reached base address
    Processing: zeroes the current address
    Recursive calls: until base address
*)
Fixpoint eraseBlockAux 	(timeout : nat) (startAddr currentAddr : paddr): LLI unit :=
	match timeout with
		| 0 => ret tt (*Stop condition 1: reached end of structure list*)
		| S timeout1 =>	(*erase the current address*)
										modify (fun s =>
														{| currentPartition := s.(currentPartition);
															memory := removeDup currentAddr s.(memory) beqAddr
														|}
										) ;;
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

(** The [checkEntry] function checks whether the entry passed in parameter exists *)
Definition checkEntry (kernelstructurestart blockentryaddr : paddr) : LLI bool :=
	perform s := get in
  let entry :=  lookup blockentryaddr s.(memory) beqAddr in
  match entry with
  | Some (BE a) => ret true
	| _ => ret false
  end.

(** The [checkBlockInRAM] function checks whether the provided block lies in RAM *)
Definition checkBlockInRAM (blockentryaddr : paddr) : LLI bool :=
	perform s := get in
  let entry :=  lookup blockentryaddr s.(memory) beqAddr in
  match entry with
  | Some (BE a) => 	let startInRAM := RAMStartAddr <=? a.(blockrange).(startAddr) in
										let endInRAM := a.(blockrange).(endAddr) <=? RAMEndAddr in
										ret (startInRAM && endInRAM)
	| _ => ret false
  end.

(** The [check32Aligned] function checks if the cutAddr is 32-bytes aligned *)
Definition check32Aligned (addrToCheck : paddr) : LLI bool :=
	let modulo := addrToCheck/32 in
	ret (modulo =? 0).

