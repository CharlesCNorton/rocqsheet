(* Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License. *)
(**
   Rocqsheet — a small spreadsheet kernel.

   Models a fixed-size grid of cells.  Each cell is empty, a signed
   integer literal, or a formula tree of arithmetic over cell
   references.  [eval_expr] is total: it carries a fuel parameter
   (a hard termination bound) and a "visited" path of cell refs so
   reference cycles are detected by visited-set membership rather
   than via fuel exhaustion.

   The whole module extracts to a single [Rocqsheet] C++ class via
   the [Crane Extraction] call at the bottom; the generated
   [rocqsheet.{h,cpp}] are consumed by the Dear ImGui front-end
   under [src/].
*)

From Stdlib Require Import List BinInt PArray.
From Corelib Require Import PrimInt63.
From Crane Require Import Mapping.NatIntStd Mapping.ZInt.
From Crane Require Extraction.
Import ListNotations.

Module Rocqsheet.

Open Scope int63.

(* Grid dimensions: 104 columns (A..CZ) by 100 rows.  The 104 limit
   keeps the eventual ImGui table under its hard column cap. *)
Definition NUM_COLS : int := 104.
Definition NUM_ROWS : int := 100.
Definition GRID_SIZE : int := PrimInt63.mul NUM_COLS NUM_ROWS.

Record CellRef : Type := mkRef
  { ref_col : int
  ; ref_row : int }.

Definition cellref_eqb (r1 r2 : CellRef) : bool :=
  andb (PrimInt63.eqb (ref_col r1) (ref_col r2))
       (PrimInt63.eqb (ref_row r1) (ref_row r2)).

Definition cell_index (r : CellRef) : int :=
  PrimInt63.add (PrimInt63.mul (ref_row r) NUM_COLS) (ref_col r).

Inductive Expr : Type :=
  | EInt : Z -> Expr
  | ERef : CellRef -> Expr
  | EAdd : Expr -> Expr -> Expr
  | ESub : Expr -> Expr -> Expr
  | EMul : Expr -> Expr -> Expr
  | EDiv : Expr -> Expr -> Expr.

Inductive Cell : Type :=
  | CEmpty : Cell
  | CLit   : Z -> Cell
  | CForm  : Expr -> Cell.

Definition Sheet : Type := PrimArray.array Cell.

Definition new_sheet : Sheet :=
  PrimArray.make GRID_SIZE CEmpty.

Definition get_cell (s : Sheet) (r : CellRef) : Cell :=
  PrimArray.get s (cell_index r).

Definition set_cell (s : Sheet) (r : CellRef) (c : Cell) : Sheet :=
  PrimArray.set s (cell_index r) c.

(* Membership check on a path of CellRefs.  Used by [eval_expr] to
   distinguish cycles from legitimate deep chains. *)
Fixpoint mem_cellref (r : CellRef) (xs : list CellRef) : bool :=
  match xs with
  | nil => false
  | y :: ys => if cellref_eqb r y then true else mem_cellref r ys
  end.

(* Total evaluator with fuel and a visited-path.

   [visited] tracks which cells the current evaluation chain has
   already entered through an [ERef].  Re-encountering a ref on
   [visited] means a cycle, so we return [None].  [fuel] is a
   generous total-termination cap; only adversarially deep
   expression trees should ever exhaust it.  Division by zero also
   returns [None]. *)
Fixpoint eval_expr (fuel : nat) (visited : list CellRef) (s : Sheet)
                   (e : Expr) : option Z :=
  match fuel with
  | O => None
  | S fuel' =>
    match e with
    | EInt n => Some n
    | ERef r =>
      if mem_cellref r visited then None
      else
        match get_cell s r with
        | CEmpty => Some 0%Z
        | CLit n => Some n
        | CForm e' => eval_expr fuel' (r :: visited) s e'
        end
    | EAdd a b =>
      match eval_expr fuel' visited s a, eval_expr fuel' visited s b with
      | Some va, Some vb => Some (Z.add va vb)
      | _, _ => None
      end
    | ESub a b =>
      match eval_expr fuel' visited s a, eval_expr fuel' visited s b with
      | Some va, Some vb => Some (Z.sub va vb)
      | _, _ => None
      end
    | EMul a b =>
      match eval_expr fuel' visited s a, eval_expr fuel' visited s b with
      | Some va, Some vb => Some (Z.mul va vb)
      | _, _ => None
      end
    | EDiv a b =>
      match eval_expr fuel' visited s a, eval_expr fuel' visited s b with
      | Some va, Some vb =>
        if Z.eqb vb 0%Z then None else Some (Z.div va vb)
      | _, _ => None
      end
    end
  end.

Definition eval_cell (fuel : nat) (s : Sheet) (r : CellRef) : option Z :=
  match get_cell s r with
  | CEmpty => Some 0%Z
  | CLit n => Some n
  | CForm e => eval_expr fuel (r :: nil) s e
  end.

(* A generous safety cap.  Real cycles are caught by the visited-set
   check before fuel matters; fuel only stops adversarially deep
   expression trees that exhaust grid traversal budget. *)
Definition DEFAULT_FUEL : nat := 100000.

(* Smoke value used by the harness during bring-up. *)
Definition smoke : option Z :=
  let a1 := mkRef 0 0 in
  let b1 := mkRef 1 0 in
  let c1 := mkRef 2 0 in
  let s0 := new_sheet in
  let s1 := set_cell s0 a1 (CLit 2%Z) in
  let s2 := set_cell s1 b1 (CLit 3%Z) in
  let s3 := set_cell s2 c1
    (CForm (EMul (EAdd (ERef a1) (ERef b1)) (EInt 7%Z))) in
  eval_cell DEFAULT_FUEL s3 c1.

(* --- Theorems ----------------------------------------------------- *)

Theorem eval_empty : forall s r fuel,
  get_cell s r = CEmpty -> eval_cell fuel s r = Some 0%Z.
Proof. intros s r fuel H. unfold eval_cell. rewrite H. reflexivity. Qed.

Theorem eval_lit : forall s r n fuel,
  get_cell s r = CLit n -> eval_cell fuel s r = Some n.
Proof. intros s r n fuel H. unfold eval_cell. rewrite H. reflexivity. Qed.

(* set/get coherence: writing a cell then reading it back returns the
   value, provided the index is in bounds for the underlying array. *)
Theorem get_set_eq : forall s r c,
  PrimInt63.ltb (cell_index r) (PrimArray.length s) = true ->
  get_cell (set_cell s r c) r = c.
Proof.
  intros s r c Hbound.
  unfold get_cell, set_cell.
  exact (@get_set_same Cell s (cell_index r) c Hbound).
Qed.

(* Frame preservation: writing one cell does not disturb a different
   cell, as long as the two refs hash to different array indices. *)
Theorem get_set_neq : forall s r1 r2 c,
  cell_index r1 <> cell_index r2 ->
  get_cell (set_cell s r2 c) r1 = get_cell s r1.
Proof.
  intros s r1 r2 c Hneq.
  unfold get_cell, set_cell.
  exact (@get_set_other Cell s (cell_index r2) (cell_index r1) c
    (fun H => Hneq (eq_sym H))).
Qed.

Theorem smoke_computes : smoke = Some 35%Z.
Proof. vm_compute. reflexivity. Qed.

Theorem eval_self_cycle_diverges :
  let r := mkRef 0 0 in
  let s := set_cell new_sheet r (CForm (ERef r)) in
  eval_cell DEFAULT_FUEL s r = None.
Proof. vm_compute. reflexivity. Qed.

Theorem eval_divzero :
  let r := mkRef 0 0 in
  let s := set_cell new_sheet r
    (CForm (EDiv (EInt 1%Z) (EInt 0%Z))) in
  eval_cell DEFAULT_FUEL s r = None.
Proof. vm_compute. reflexivity. Qed.

(* Visited-set catches cycles in general: if a ref is already on the
   evaluation path and the expression is just that ref, [eval_expr]
   returns [None] for any positive fuel. *)
Theorem mem_cellref_eval_ref_none : forall fuel visited s r,
  mem_cellref r visited = true ->
  eval_expr (S fuel) visited s (ERef r) = None.
Proof.
  intros fuel visited s r H.
  simpl. rewrite H. reflexivity.
Qed.

End Rocqsheet.

Crane Extraction "rocqsheet" Rocqsheet.
