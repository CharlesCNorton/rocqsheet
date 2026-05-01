(* Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License. *)
From Stdlib Require Import List BinInt Lia.
From Corelib Require Import PrimInt63.
From Crane Require Import Mapping.NatIntStd Mapping.ZInt.
From Rocqsheet Require Import Rocqsheet.
Import ListNotations.
Import Rocqsheet.

Open Scope int63.

Fixpoint range_in_row (col hc : int) (row : int) (fuel : nat)
    : list CellRef :=
  match fuel with
  | O => []
  | S fuel' =>
    if PrimInt63.ltb hc col then []
    else mkRef col row :: range_in_row (PrimInt63.add col 1) hc row fuel'
  end.

Fixpoint range_rows (lc hc : int) (lr hr : int) (fuel : nat)
    : list CellRef :=
  match fuel with
  | O => []
  | S fuel' =>
    if PrimInt63.ltb hr lr then []
    else
      range_in_row lc hc lr 300
      ++ range_rows lc hc (PrimInt63.add lr 1) hr fuel'
  end.

Definition range_cells (lo hi : CellRef) : list CellRef :=
  range_rows (ref_col lo) (ref_col hi) (ref_row lo) (ref_row hi) 300.

Lemma range_rows_inverted_aux : forall lc hc lr hr fuel,
  PrimInt63.ltb hr lr = true ->
  range_rows lc hc lr hr fuel = [].
Proof.
  intros lc hc lr hr fuel Hinv.
  destruct fuel; simpl; [reflexivity|].
  rewrite Hinv. reflexivity.
Qed.

Theorem range_inverted_rows : forall lo hi,
  PrimInt63.ltb (ref_row hi) (ref_row lo) = true ->
  range_cells lo hi = [].
Proof.
  intros lo hi Hinv. unfold range_cells.
  apply range_rows_inverted_aux. exact Hinv.
Qed.

Theorem range_singleton_smoke :
  range_cells (mkRef 3 5) (mkRef 3 5) = [mkRef 3 5].
Proof. vm_compute. reflexivity. Qed.

Theorem range_inverted_smoke :
  range_cells (mkRef 5 5) (mkRef 5 3) = [].
Proof. vm_compute. reflexivity. Qed.

Theorem range_row_smoke :
  range_cells (mkRef 0 0) (mkRef 2 0)
  = [mkRef 0 0; mkRef 1 0; mkRef 2 0].
Proof. vm_compute. reflexivity. Qed.

Theorem range_rect_smoke :
  range_cells (mkRef 0 0) (mkRef 1 1)
  = [mkRef 0 0; mkRef 1 0; mkRef 0 1; mkRef 1 1].
Proof. vm_compute. reflexivity. Qed.
