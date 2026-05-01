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

From Stdlib Require Import List BinInt PArray Lia.
From Stdlib.Numbers.Cyclic.Int63 Require Import Uint63.
From Corelib Require Import PrimInt63 Uint63Axioms.
From Crane Require Import Mapping.NatIntStd Mapping.ZInt.
From Crane Require Extraction.
Import ListNotations.

(* Override Z arithmetic so the extracted C++ saturates on int64_t
   overflow rather than wrapping (which is undefined behaviour for
   signed types).  The Rocq proofs are over unbounded Z, so they
   remain valid; the override only affects extracted runtime. *)
Crane Extract Inlined Constant Z.add =>
  "([&]() -> int64_t { int64_t _r; if (__builtin_add_overflow(%a0, %a1, &_r)) return ((%a0) < 0) ? INT64_MIN : INT64_MAX; return _r; }())".
Crane Extract Inlined Constant Z.sub =>
  "([&]() -> int64_t { int64_t _r; if (__builtin_sub_overflow(%a0, %a1, &_r)) return ((%a0) < 0) ? INT64_MIN : INT64_MAX; return _r; }())".
Crane Extract Inlined Constant Z.mul =>
  "([&]() -> int64_t { int64_t _r; if (__builtin_mul_overflow(%a0, %a1, &_r)) return (((%a0) < 0) != ((%a1) < 0)) ? INT64_MIN : INT64_MAX; return _r; }())".

Module Rocqsheet.

Open Scope int63.

(* Grid dimensions: 260 columns (A..IZ) by 200 rows.  260 leaves
   plenty of headroom under ImGui's 511-column hard cap. *)
Definition NUM_COLS : int := 260.
Definition NUM_ROWS : int := 200.
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
  | EDiv : Expr -> Expr -> Expr
  | EEq  : Expr -> Expr -> Expr
  | ELt  : Expr -> Expr -> Expr
  | EGt  : Expr -> Expr -> Expr
  | EIf  : Expr -> Expr -> Expr -> Expr.

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
    | EEq a b =>
      match eval_expr fuel' visited s a, eval_expr fuel' visited s b with
      | Some va, Some vb => Some (if Z.eqb va vb then 1%Z else 0%Z)
      | _, _ => None
      end
    | ELt a b =>
      match eval_expr fuel' visited s a, eval_expr fuel' visited s b with
      | Some va, Some vb => Some (if Z.ltb va vb then 1%Z else 0%Z)
      | _, _ => None
      end
    | EGt a b =>
      match eval_expr fuel' visited s a, eval_expr fuel' visited s b with
      | Some va, Some vb => Some (if Z.gtb va vb then 1%Z else 0%Z)
      | _, _ => None
      end
    | EIf c t e =>
      match eval_expr fuel' visited s c with
      | Some 0%Z => eval_expr fuel' visited s e
      | Some _ => eval_expr fuel' visited s t
      | None => None
      end
    end
  end.

Definition eval_cell (fuel : nat) (s : Sheet) (r : CellRef) : option Z :=
  match get_cell s r with
  | CEmpty => Some 0%Z
  | CLit n => Some n
  | CForm e => eval_expr fuel (r :: nil) s e
  end.

(* Safety cap on the Rocq-side evaluator's recursion depth.  The C++
   front-end does not call the extracted recursive [eval_cell]
   directly; it uses [formula::eval_iter] in src/eval_iter.cpp, an
   iterative implementation with a heap-allocated continuation stack
   that mirrors this kernel step-for-step.  Cycles, division by zero,
   and signed-overflow saturation match. *)
Definition DEFAULT_FUEL : nat := 4000.

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

(* IF picks the then-branch when the condition evaluates to non-zero. *)
Theorem eval_if_then :
  let r := mkRef 0 0 in
  let s := set_cell new_sheet r
    (CForm (EIf (EInt 1%Z) (EInt 7%Z) (EInt 99%Z))) in
  eval_cell DEFAULT_FUEL s r = Some 7%Z.
Proof. vm_compute. reflexivity. Qed.

(* IF picks the else-branch when the condition evaluates to zero. *)
Theorem eval_if_else :
  let r := mkRef 0 0 in
  let s := set_cell new_sheet r
    (CForm (EIf (EInt 0%Z) (EInt 7%Z) (EInt 99%Z))) in
  eval_cell DEFAULT_FUEL s r = Some 99%Z.
Proof. vm_compute. reflexivity. Qed.

(* Equality on identical literals returns 1; on distinct literals, 0. *)
Theorem eval_eq_refl :
  let r := mkRef 0 0 in
  let s := set_cell new_sheet r
    (CForm (EEq (EInt 42%Z) (EInt 42%Z))) in
  eval_cell DEFAULT_FUEL s r = Some 1%Z.
Proof. vm_compute. reflexivity. Qed.

Theorem eval_eq_distinct :
  let r := mkRef 0 0 in
  let s := set_cell new_sheet r
    (CForm (EEq (EInt 1%Z) (EInt 2%Z))) in
  eval_cell DEFAULT_FUEL s r = Some 0%Z.
Proof. vm_compute. reflexivity. Qed.

(* Less-than and greater-than on closed literals. *)
Theorem eval_lt_true :
  let r := mkRef 0 0 in
  let s := set_cell new_sheet r
    (CForm (ELt (EInt 1%Z) (EInt 2%Z))) in
  eval_cell DEFAULT_FUEL s r = Some 1%Z.
Proof. vm_compute. reflexivity. Qed.

Theorem eval_gt_false :
  let r := mkRef 0 0 in
  let s := set_cell new_sheet r
    (CForm (EGt (EInt 1%Z) (EInt 2%Z))) in
  eval_cell DEFAULT_FUEL s r = Some 0%Z.
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

(* --- Friendly preconditions for callers ----------------------------- *)

(* Boolean predicate: a ref's column and row each fit in the grid. *)
Definition valid_ref (r : CellRef) : bool :=
  andb (PrimInt63.ltb (ref_col r) NUM_COLS)
       (PrimInt63.ltb (ref_row r) NUM_ROWS).

(* The fresh sheet has length GRID_SIZE.  Closed computation. *)
Lemma length_new_sheet : PrimArray.length new_sheet = GRID_SIZE.
Proof. vm_compute. reflexivity. Qed.

(* set_cell preserves array length.  Direct from PArray.length_set. *)
Lemma length_set_cell : forall s r c,
  PrimArray.length (set_cell s r c) = PrimArray.length s.
Proof.
  intros s r c. unfold set_cell.
  apply (@length_set Cell s (cell_index r) c).
Qed.

(* The cell_index bound for valid refs.  Move int63 inequalities
   into Z via [ltb_spec], compute the literal Z constants by
   [reflexivity], and discharge the modular reduction by showing the
   product / sum stays well below wB. *)
Lemma cell_index_in_grid : forall r,
  valid_ref r = true ->
  PrimInt63.ltb (cell_index r) GRID_SIZE = true.
Proof.
  intros r Hv.
  unfold valid_ref in Hv.
  apply Bool.andb_true_iff in Hv as [Hcol Hrow].
  rewrite ltb_spec in Hcol, Hrow.
  apply ltb_spec.
  pose proof (to_Z_bounded (ref_col r)).
  pose proof (to_Z_bounded (ref_row r)).
  unfold cell_index.
  rewrite add_spec, mul_spec.
  assert (E1 : to_Z NUM_COLS = 260%Z) by reflexivity.
  assert (E2 : to_Z NUM_ROWS = 200%Z) by reflexivity.
  assert (E3 : to_Z GRID_SIZE = 52000%Z) by reflexivity.
  assert (EwB : wB = 9223372036854775808%Z) by reflexivity.
  rewrite E1 in *. rewrite E2 in *. rewrite E3. rewrite EwB in *.
  rewrite Z.mod_small.
  - rewrite Z.mod_small.
    + assert (HM : (to_Z (ref_row r) * 260 + to_Z (ref_col r)
                    <= 199 * 260 + 259)%Z) by nia.
      lia.
    + split; nia.
  - split.
    + apply Z.add_nonneg_nonneg;
        [ apply Z.mod_pos_bound; lia | lia ].
    + assert (HM : ((to_Z (ref_row r) * 260) mod 9223372036854775808
                    < 52000)%Z).
      { rewrite Z.mod_small by nia. nia. }
      lia.
Qed.

(* User-friendly variant: callers prove [valid_ref r] (a closed boolean
   check on the input) and a length invariant on the sheet (preserved
   by [set_cell] and starting at [GRID_SIZE] for [new_sheet]) instead
   of the raw int63 [ltb (cell_index r) (length s)] precondition. *)
Theorem get_set_eq_valid : forall s r c,
  PrimArray.length s = GRID_SIZE ->
  valid_ref r = true ->
  get_cell (set_cell s r c) r = c.
Proof.
  intros s r c Hlen Hv.
  apply get_set_eq.
  rewrite Hlen.
  apply cell_index_in_grid; assumption.
Qed.

End Rocqsheet.

(* Extraction is driven from theories/RocqsheetMain.v. *)
