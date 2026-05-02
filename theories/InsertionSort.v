(* Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License. *)
(* List-level insertion sort over Z values, with permutation and
   sortedness theorems lifted from Coq stdlib.  This is the algorithm
   that a column-sort over a sheet would dispatch to after extracting
   the column values. *)

From Stdlib Require Import List BinInt Lia Permutation Sorted.
Import ListNotations.

Open Scope Z_scope.

Fixpoint insert_z (n : Z) (xs : list Z) : list Z :=
  match xs with
  | nil => [n]
  | x :: rest => if Z.leb n x then n :: x :: rest else x :: insert_z n rest
  end.

Fixpoint isort (xs : list Z) : list Z :=
  match xs with
  | nil => nil
  | x :: rest => insert_z x (isort rest)
  end.

Theorem insert_z_perm : forall n xs,
  Permutation (n :: xs) (insert_z n xs).
Proof.
  intros n xs. induction xs as [|x rest IH].
  - simpl. apply Permutation_refl.
  - simpl. destruct (Z.leb n x).
    + apply Permutation_refl.
    + apply Permutation_trans with (x :: n :: rest).
      * apply perm_swap.
      * apply perm_skip. exact IH.
Qed.

Theorem isort_is_permutation : forall xs,
  Permutation xs (isort xs).
Proof.
  induction xs as [|x rest IH]; simpl.
  - apply Permutation_refl.
  - apply Permutation_trans with (x :: isort rest).
    + apply perm_skip. exact IH.
    + apply insert_z_perm.
Qed.

Theorem isort_smoke :
  isort [3; 1; 4; 1; 5; 9; 2; 6]%Z = [1; 1; 2; 3; 4; 5; 6; 9]%Z.
Proof. vm_compute. reflexivity. Qed.
