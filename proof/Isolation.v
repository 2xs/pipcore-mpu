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

(** * Summary
    This file contains the formalization of interesting properties that we need
    to prove *)
Require Import Model.ADT Model.MALInternal.
Require Import Proof.StateLib Proof.Lib.
Require Import List.
Import List.ListNotations.

(** THE VERTICAL SHARING PROPERTY:
    All child used blocks (PD + kernel structures + mapped blocks) are mapped into
    the parent partition  *)
Definition verticalSharing s : Prop :=

forall parent child : paddr,
  In parent (getPartitions multiplexer s) ->

  In child (getChildren parent s) ->

	incl (getUsedPaddr child s) (getMappedPaddr parent s).


(** THE ISOLATION PROPERTY BETWEEN PARTITIONS,
    If we take two different children of a given parent,
    then all their used blocks are different  *)
Definition partitionsIsolation  s : Prop :=
forall parent child1 child2 : paddr ,

  In parent (getPartitions multiplexer s) ->

  In child1 (getChildren parent s) ->

  In child2 (getChildren parent s) ->

	child1 <> child2 ->

	disjoint (getUsedPaddr child1 s) (getUsedPaddr child2 s).


(** THE ISOLATION PROPERTY BETWEEN THE KERNEL DATA AND PARTITIONS
    kernel data is the configuration pages of partitions.
    All configuration tables of a given partition are inaccessible by all
    partitions *)

(* the config blocks are NOT the inaccessible blocks within a partition but
	its PDT + its kernel structures *)
Definition kernelDataIsolation s : Prop :=

	forall partition1 partition2 : paddr,

	In partition1 (getPartitions multiplexer s) ->

  In partition2 (getPartitions multiplexer s) ->

	disjoint (getAccessibleMappedPaddr partition1 s) (getConfigPaddr partition2 s).
