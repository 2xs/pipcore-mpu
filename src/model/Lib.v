(*******************************************************************************)
(*  © Université de Lille, The Pip Development Team (2015-2023)                *)
(*  Copyright (C) 2020-2023 Orange                                             *)
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

Require Import List.
Import List.ListNotations.

Fixpoint lookup {A C: Type} (a : A)  (assoc : list (A*C))  (eqA : A -> A -> bool) :=
  match assoc with
    | nil => None
    | (x, y) :: assoc' => if eqA x a then Some y else lookup a assoc' eqA
  end.



Fixpoint removeDup {A C: Type} (a : A) (assoc : list (A * C)) (eqA : A -> A -> bool) :=
  match assoc with
    | nil => nil
    | (p, v) :: assoc' => if eqA p a
													then removeDup a assoc' eqA
													else (p, v) :: (removeDup a assoc' eqA)
  end.

Definition add {A C: Type} (a : A) (v : C) (assoc : list (A * C)) (eqA : A -> A -> bool)  :=
  (a, v) :: removeDup a assoc eqA.

(* 	Adds an element at the given index or replace it if there is an element already.
		Notes :
			- It inserts the default element until the target index is reached
			- the list grows for an index not reached before
*)
Fixpoint addElementAt {A: Type} (remainingIdx: nat) (newelement: A) (assoc : list A) (default:A)    :=
  match remainingIdx with
    | 0 => (* reached target index *)
						match assoc with
						| nil => (*add *) newelement::nil
						| p::post => (* replace *) newelement::post
						end

    | S n => match assoc with
						| nil => (* adds default element in between*) default::(addElementAt n newelement nil default)
						| p::post => p :: (addElementAt n newelement post default)
						end
		end.

Fixpoint readElementAt {A: Type} (remainingIdx: nat) (assoc : list A) (default:A)   :=
  match remainingIdx with
    | 0 => (* reached target index *)
						match assoc with
						| nil => (*no element at this index *) default
						| p::post => (* found element *) p
						end

    | S n => match assoc with
						| nil => (* not enough elements in list *) default
						| p::post => (* continue search in remaining elements *) readElementAt n post default
						end
		end.

Fixpoint indexOf {A: Type} 	(a : A) (idx : nat)  (assoc : list A)
														(eqA : A -> A -> bool) (default: nat) :=
	match assoc with
    | nil => default
    | x :: assoc' => 	if eqA x a
											then (* found element, return index *) idx
											else (* continue search *) indexOf a (S idx) assoc' eqA default
  end.

