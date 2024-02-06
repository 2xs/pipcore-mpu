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

Require Import Model.ADT Model.Lib Model.MAL Model.Monad.

Require Import Proof.StateLib Proof.Isolation Proof.Consistency.

Definition MapMPUPropagatedProperties
currentPart globalIdPD blockToEnableAddr
MPURegionNb
realMPU
s0 s1
entry
  :=
(s1 = {|
        currentPartition := currentPartition s0;
        memory :=
          add globalIdPD
            (PDT
               {|
                 structure := structure entry;
                 firstfreeslot := firstfreeslot entry;
                 nbfreeslots := nbfreeslots entry;
                 nbprepare := nbprepare entry;
                 parent := parent entry;
                 MPU := addElementAt MPURegionNb blockToEnableAddr realMPU nullAddr;
                 vidtAddr := vidtAddr entry
               |}) (memory s0) beqAddr
      |})
/\ pdentryMPU globalIdPD realMPU s0
/\ partitionsIsolation s0
/\ kernelDataIsolation s0
/\ verticalSharing s0
/\ consistency s0
/\ currentPart = currentPartition s0
/\ isPDT globalIdPD s0
/\ lookup globalIdPD (memory s0) beqAddr = Some (PDT entry).

Lemma MapMPUVS
currentPart globalIdPD blockToEnableAddr
MPURegionNb
realMPU
s0 s1
entry :

MapMPUPropagatedProperties
currentPart globalIdPD blockToEnableAddr
MPURegionNb
realMPU
s0 s1
entry
-> verticalSharing s1.
Proof.

Admitted.

Lemma MapMPUKI
currentPart globalIdPD blockToEnableAddr
MPURegionNb
realMPU
s0 s1
entry :

MapMPUPropagatedProperties
currentPart globalIdPD blockToEnableAddr
MPURegionNb
realMPU
s0 s1
entry
-> kernelDataIsolation s1.
Proof.

Admitted.

Lemma MapMPUHI
currentPart globalIdPD blockToEnableAddr
MPURegionNb
realMPU
s0 s1
entry :

MapMPUPropagatedProperties
currentPart globalIdPD blockToEnableAddr
MPURegionNb
realMPU
s0 s1
entry
-> partitionsIsolation s1.
Proof.

Admitted.