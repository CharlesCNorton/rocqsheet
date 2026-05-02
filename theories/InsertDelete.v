(* Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License. *)
(* Formula-aware insert/delete row helpers.  These wrap the
   data-level operations from [Shift.v] with formula reference
   shifting so that references in formulas track the row movement. *)

From Stdlib Require Import List BinInt.
From Corelib Require Import PrimInt63.
From Crane Require Import Mapping.NatIntStd Mapping.ZInt.
From Rocqsheet Require Import Rocqsheet Shift.
Import ListNotations.
Import Rocqsheet.

Open Scope int63.

(* Conditional shift on a single ref: shift the row by dr if the
   ref's row is at or above the threshold, otherwise leave it. *)
Definition shift_ref_if_above (threshold dr : int) (r : CellRef)
    : CellRef :=
  if PrimInt63.leb threshold (ref_row r)
  then mkRef (ref_col r) (PrimInt63.add (ref_row r) dr)
  else r.

Theorem shift_if_above_below : forall r,
  shift_ref_if_above 5 1 (mkRef (ref_col r) 3%uint63)
  = mkRef (ref_col r) 3%uint63.
Proof. intros. unfold shift_ref_if_above. reflexivity. Qed.

Theorem shift_if_above_at_threshold_smoke :
  shift_ref_if_above 5 1 (mkRef 0 5%uint63) = mkRef 0 6%uint63.
Proof. vm_compute. reflexivity. Qed.

Theorem shift_if_above_above_smoke :
  shift_ref_if_above 5 1 (mkRef 0 7%uint63) = mkRef 0 8%uint63.
Proof. vm_compute. reflexivity. Qed.

(* Insert ∘ delete at the same row recovers the data structure
   when the deleted row was empty.  Smoke at concrete coords. *)
Theorem insert_after_delete_recovers_smoke :
  let s := set_cell new_sheet (mkRef 0 7%uint63) (CLit 99%Z) in
  let s' := insert_row (delete_row s 5%uint63) 5%uint63 in
  get_cell s' (mkRef 0 7%uint63) = CLit 99%Z.
Proof. vm_compute. reflexivity. Qed.
