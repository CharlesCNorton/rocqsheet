(* Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License. *)
From Stdlib Require Import List Bool BinInt Lia Permutation.
From Corelib Require Import PrimInt63.
From Crane Require Import Mapping.NatIntStd Mapping.ZInt.
From Rocqsheet Require Import Rocqsheet.
Import ListNotations.
Import Rocqsheet.

Open Scope int63.

(* --- Row swap: building block for any row-based sort. ---------- *)

Fixpoint swap_rows_aux (fuel : nat) (src acc : Sheet) (a b col : int) : Sheet :=
  match fuel with
  | O => acc
  | S fuel' =>
    if PrimInt63.leb NUM_COLS col then acc
    else
      let idx_a := PrimInt63.add (PrimInt63.mul a NUM_COLS) col in
      let idx_b := PrimInt63.add (PrimInt63.mul b NUM_COLS) col in
      let cell_a := PrimArray.get src idx_a in
      let cell_b := PrimArray.get src idx_b in
      let acc' := PrimArray.set acc idx_a cell_b in
      let acc'' := PrimArray.set acc' idx_b cell_a in
      swap_rows_aux fuel' src acc'' a b (PrimInt63.add col 1)
  end.

Definition swap_rows (s : Sheet) (a b : int) : Sheet :=
  swap_rows_aux 300 s s a b 0.

(* Swapping the same row with itself leaves the sheet unchanged at
   any specific cell that's read after the swap (smoke test). *)
Theorem swap_self_is_noop_smoke :
  let s := set_cell new_sheet (mkRef 0 3%uint63) (CLit 42%Z) in
  get_cell (swap_rows s 3%uint63 3%uint63) (mkRef 0 3%uint63) = CLit 42%Z.
Proof. vm_compute. reflexivity. Qed.

(* After swapping rows a and b, the cell at (col, a) holds what was
   at (col, b), and vice versa.  Smoke at concrete coords. *)
Theorem swap_rows_exchanges_smoke :
  let s := set_cell new_sheet (mkRef 0 1%uint63) (CLit 10%Z) in
  let s' := set_cell s (mkRef 0 4%uint63) (CLit 20%Z) in
  let sw := swap_rows s' 1%uint63 4%uint63 in
  get_cell sw (mkRef 0 1%uint63) = CLit 20%Z
  /\ get_cell sw (mkRef 0 4%uint63) = CLit 10%Z.
Proof. vm_compute. split; reflexivity. Qed.

(* Swap then swap back recovers the original at the swapped cells.
   sort_is_permutation specialised to a single swap pair. *)
Theorem swap_swap_restores_smoke :
  let s := set_cell new_sheet (mkRef 0 2%uint63) (CLit 7%Z) in
  let s2 := swap_rows s 2%uint63 8%uint63 in
  let s3 := swap_rows s2 2%uint63 8%uint63 in
  get_cell s3 (mkRef 0 2%uint63) = CLit 7%Z.
Proof. vm_compute. reflexivity. Qed.

(* --- Permutation predicate over rows ---------------------------- *)

(* Two sheets are row-equivalent at column [c] when they agree on
   that column up to a row permutation.  Cheapest specification: the
   multisets of (cell at column c) over rows match.  We use lists
   modulo Permutation. *)

Fixpoint column_values_aux (s : Sheet) (c : int) (row : nat) (count : nat)
    : list Cell :=
  match count with
  | O => []
  | S count' =>
    get_cell s (mkRef c (Uint63.of_Z (Z.of_nat row)))
    :: column_values_aux s c (S row) count'
  end.

Definition column_values (s : Sheet) (c : int) : list Cell :=
  column_values_aux s c 0 200.

(* A swap is a permutation of the column values: the smoke checks
   the multiset is preserved at one column. *)
Theorem swap_preserves_column_smoke :
  let s := set_cell new_sheet (mkRef 0 1%uint63) (CLit 10%Z) in
  let s' := set_cell s (mkRef 0 4%uint63) (CLit 20%Z) in
  let sw := swap_rows s' 1%uint63 4%uint63 in
  Permutation (column_values s' 0%uint63) (column_values sw 0%uint63).
Proof.
  vm_compute. apply perm_swap.
Qed.
