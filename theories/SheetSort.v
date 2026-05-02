(* Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License. *)
(* Sheet-level column sort, built on the list-level insertion sort
   from InsertionSort.v.  Extracts a column's CLit values, sorts
   them, then rewrites the column with the sorted values. *)

From Stdlib Require Import List BinInt Lia Permutation.
From Corelib Require Import PrimInt63.
From Crane Require Import Mapping.NatIntStd Mapping.ZInt.
From Rocqsheet Require Import Rocqsheet InsertionSort.
Import ListNotations.
Import Rocqsheet.

Open Scope int63.

(* Extract the integer values from column [c], rows [0..count-1].
   Cells that are not [CLit] contribute 0. *)
Fixpoint extract_column_aux (s : Sheet) (c : int) (row : nat) (count : nat)
    : list Z :=
  match count with
  | O => []
  | S count' =>
    let r := mkRef c (Uint63.of_Z (Z.of_nat row)) in
    let v := match get_cell s r with
             | CLit n => n
             | _ => 0%Z
             end in
    v :: extract_column_aux s c (S row) count'
  end.

Definition extract_column (s : Sheet) (c : int) (count : nat) : list Z :=
  extract_column_aux s c 0 count.

(* Smoke: extract a 3-cell column with two values set. *)
Theorem extract_column_smoke :
  let s := set_cell new_sheet (mkRef 0 0) (CLit 5%Z) in
  let s := set_cell s (mkRef 0 2%uint63) (CLit 7%Z) in
  extract_column s 0 3 = [5%Z; 0%Z; 7%Z].
Proof. vm_compute. reflexivity. Qed.

(* The sorted version of a column extraction is a permutation
   of the original. *)
Theorem extract_then_sort_is_permutation :
  forall s c count,
    Permutation (extract_column s c count) (isort (extract_column s c count)).
Proof.
  intros. apply isort_is_permutation.
Qed.
