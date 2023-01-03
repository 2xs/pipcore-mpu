(*******************************************************************************)
(*  © Université de Lille, The Pip Development Team (2015-2023)                *)
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

From Coq Require Import ZArith.
From Coq Require Import List String.
Import ListNotations.

Close Scope nat_scope.
Open Scope Z_scope.

From compcert.cfrontend Require Csyntax Ctypes Cop.
From compcert.common Require Values.
From compcert.lib Require Integers.

From dx      Require Import CoqIR IR IRtoC ResultMonad.
From dx.Type Require Bool Nat.

Import UserIdentNotations.

From Model Require Monad ADT MALInternal MAL.
From Core  Require Internal Services.

Definition voidStar : Ctypes.type :=
  Ctypes.Tpointer Ctypes.Tvoid Ctypes.noattr.

Definition uint32 : Ctypes.type :=
  Ctypes.Tint Ctypes.I32 Ctypes.Unsigned Ctypes.noattr.

Module PipTypes.
  Definition paddrCompilableType := MkCompilableType ADT.paddr voidStar.
  Definition indexCompilableType := MkCompilableType ADT.index uint32.
End PipTypes.

Definition funPaddrPaddrBoolType :=
  MkCompilableSymbolType
    [ PipTypes.paddrCompilableType; PipTypes.paddrCompilableType ]
    (Some Bool.boolCompilableType).

Definition funIndexIndexBoolType :=
  MkCompilableSymbolType
    [ PipTypes.indexCompilableType; PipTypes.indexCompilableType ]
    (Some Bool.boolCompilableType).

Definition cBinOp o es :=
  match es with
  | [e1;e2] => Ok (Csyntax.Ebinop o e1 e2 Ctypes.type_bool)
  | _       => Err PrimitiveEncodingFailed
  end.

Definition cEq := cBinOp Cop.Oeq.
Definition cLe := cBinOp Cop.Ole.
Definition cLt := cBinOp Cop.Olt.

Module PipPrimitives.
  Definition paddrEqPrim := MkPrimitive funPaddrPaddrBoolType MALInternal.beqAddr cEq.
  Definition paddrLePrim := MkPrimitive funPaddrPaddrBoolType MALInternal.paddrLe cLe.
  Definition indexEqPrim := MkPrimitive funIndexIndexBoolType MALInternal.indexEq cEq.
  Definition indexLePrim := MkPrimitive funIndexIndexBoolType MALInternal.indexLe cLe.
  Definition indexLtPrim := MkPrimitive funIndexIndexBoolType MALInternal.indexLt cLt.
End PipPrimitives.

GenerateIntermediateRepresentation
  InternalHIRSyms
  Monad.LLI Monad.bind Monad.ret

  Bool.Exports
  Nat.Exports

  PipTypes

  Internal
  .

Definition dxModuleInternalH := makeDXModuleWithDefaults InternalHIRSyms.

GenerateIntermediateRepresentation
  InternalIRSyms
  Monad.LLI Monad.bind Monad.ret

  Bool.Exports
  Nat.Exports

  PipTypes
  PipPrimitives

  MALInternal
  MAL

  __

  Internal
  .

Definition dxModuleInternal := makeDXModuleWithDefaults InternalIRSyms.

GenerateIntermediateRepresentation
  ServicesHIRSyms
  Monad.LLI Monad.bind Monad.ret

  Bool.Exports
  Nat.Exports

  PipTypes
  PipPrimitives

  MALInternal
  MAL

  Services
  .

Definition dxModuleServicesH := makeDXModuleWithDefaults ServicesHIRSyms.

GenerateIntermediateRepresentation
  ServicesIRSyms
  Monad.LLI Monad.bind Monad.ret

  Bool.Exports
  Nat.Exports

  PipTypes
  PipPrimitives

  MALInternal
  MAL

  Internal

  __

  Services
  .

Definition dxModuleServices := makeDXModuleWithDefaults ServicesIRSyms.
