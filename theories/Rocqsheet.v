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
From Corelib Require PrimFloat FloatAxioms.
From Corelib Require Import PrimString.
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

Crane Extract Inlined Constant Z.div =>
  "((%a1 == 0) ? INT64_C(0) : (((%a0 == INT64_MIN) && (%a1 == -1)) ? INT64_MIN : ((%a0) / (%a1))))".
Crane Extract Inlined Constant Z.modulo =>
  "((%a1 == 0) ? INT64_C(0) : (((%a0 == INT64_MIN) && (%a1 == -1)) ? INT64_C(0) : ((%a0) % (%a1))))".

Module Rocqsheet.

Open Scope int63.

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
  | EInt   : Z -> Expr
  | ERef   : CellRef -> Expr
  | EAdd   : Expr -> Expr -> Expr
  | ESub   : Expr -> Expr -> Expr
  | EMul   : Expr -> Expr -> Expr
  | EDiv   : Expr -> Expr -> Expr
  | EEq    : Expr -> Expr -> Expr
  | ELt    : Expr -> Expr -> Expr
  | EGt    : Expr -> Expr -> Expr
  | EIf    : Expr -> Expr -> Expr -> Expr
  | EMod   : Expr -> Expr -> Expr
  | EPow   : Expr -> Expr -> Expr
  | ENot   : Expr -> Expr
  | EAnd   : Expr -> Expr -> Expr
  | EOr    : Expr -> Expr -> Expr
  | ESum   : CellRef -> CellRef -> Expr
  | EAvg   : CellRef -> CellRef -> Expr
  | ECount : CellRef -> CellRef -> Expr
  | EIfErr : Expr -> Expr -> Expr
  | EFloat : PrimFloat.float -> Expr
  | EFAdd  : Expr -> Expr -> Expr
  | EFSub  : Expr -> Expr -> Expr
  | EFMul  : Expr -> Expr -> Expr
  | EFDiv  : Expr -> Expr -> Expr
  | EStr   : PrimString.string -> Expr
  | EConcat: Expr -> Expr -> Expr
  | ELen   : Expr -> Expr
  | ESubstr: Expr -> Expr -> Expr -> Expr
  | EBool  : bool -> Expr
  | EBNot  : Expr -> Expr
  | EBAnd  : Expr -> Expr -> Expr
  | EBOr   : Expr -> Expr -> Expr.

Inductive Cell : Type :=
  | CEmpty : Cell
  | CLit   : Z -> Cell
  | CFloat : PrimFloat.float -> Cell
  | CStr   : PrimString.string -> Cell
  | CBool  : bool -> Cell
  | CForm  : Expr -> Cell.

Definition Sheet : Type := PrimArray.array Cell.

Definition new_sheet : Sheet :=
  PrimArray.make GRID_SIZE CEmpty.

Definition get_cell (s : Sheet) (r : CellRef) : Cell :=
  PrimArray.get s (cell_index r).

Definition set_cell (s : Sheet) (r : CellRef) (c : Cell) : Sheet :=
  PrimArray.set s (cell_index r) c.

Fixpoint mem_cellref (r : CellRef) (xs : list CellRef) : bool :=
  match xs with
  | nil => false
  | y :: ys => if cellref_eqb r y then true else mem_cellref r ys
  end.

Definition cell_col_of (r : CellRef) : int :=
  PrimInt63.mod (cell_index r) NUM_COLS.

Definition cell_row_of (r : CellRef) : int :=
  PrimInt63.div (cell_index r) NUM_COLS.

(* Three-state evaluation result.  [EVal v] is success.  [EErr] is a
   deterministic error (cycle, divide-by-zero, modulo-by-zero,
   negative power).  [EFuel] is fuel exhaustion.  Distinguishing
   these matters for [EIfErr], whose semantics traps [EErr] but
   propagates [EFuel] so that fuel-monotonicity holds. *)
Inductive EvalResult : Type :=
  | EVal  : Z -> EvalResult
  | EFVal : PrimFloat.float -> EvalResult
  | EValS : PrimString.string -> EvalResult
  | EValB : bool -> EvalResult
  | EErr  : EvalResult
  | EFuel : EvalResult.

(* Combine two binary [Z] operands into a single result, preserving
   error and fuel propagation.  A float operand in this integer
   context degrades to [EErr] (type mismatch). *)
Definition combine_bin (op : Z -> Z -> EvalResult)
                       (ra rb : EvalResult) : EvalResult :=
  match ra, rb with
  | EFuel, _      => EFuel
  | _, EFuel      => EFuel
  | EErr, _       => EErr
  | _, EErr       => EErr
  | EVal va, EVal vb => op va vb
  | _, _          => EErr
  end.

(* Same shape, for two [float] operands.  An integer operand here
   degrades to [EErr]. *)
Definition combine_binf (op : PrimFloat.float -> PrimFloat.float -> EvalResult)
                        (ra rb : EvalResult) : EvalResult :=
  match ra, rb with
  | EFuel, _      => EFuel
  | _, EFuel      => EFuel
  | EErr, _       => EErr
  | _, EErr       => EErr
  | EFVal fa, EFVal fb => op fa fb
  | _, _          => EErr
  end.

(* Same shape, for two [string] operands.  Other operand types here
   degrade to [EErr]. *)
Definition combine_bins (op : PrimString.string -> PrimString.string -> EvalResult)
                        (ra rb : EvalResult) : EvalResult :=
  match ra, rb with
  | EFuel, _      => EFuel
  | _, EFuel      => EFuel
  | EErr, _       => EErr
  | _, EErr       => EErr
  | EValS sa, EValS sb => op sa sb
  | _, _          => EErr
  end.

Fixpoint eval_expr (fuel : nat) (visited : list CellRef) (s : Sheet)
                   (e : Expr) : EvalResult :=
  match fuel with
  | O => EFuel
  | S fuel' =>
    match e with
    | EInt n => EVal n
    | EFloat f => EFVal f
    | ERef r =>
      if mem_cellref r visited then EErr
      else
        match get_cell s r with
        | CEmpty   => EVal 0%Z
        | CLit n   => EVal n
        | CFloat f => EFVal f
        | CStr s'  => EValS s'
        | CBool b  => EValB b
        | CForm e' => eval_expr fuel' (r :: visited) s e'
        end
    | EAdd a b =>
      combine_bin (fun va vb => EVal (Z.add va vb))
        (eval_expr fuel' visited s a) (eval_expr fuel' visited s b)
    | ESub a b =>
      combine_bin (fun va vb => EVal (Z.sub va vb))
        (eval_expr fuel' visited s a) (eval_expr fuel' visited s b)
    | EMul a b =>
      combine_bin (fun va vb => EVal (Z.mul va vb))
        (eval_expr fuel' visited s a) (eval_expr fuel' visited s b)
    | EDiv a b =>
      combine_bin
        (fun va vb => if Z.eqb vb 0%Z then EErr
                      else EVal (Z.div va vb))
        (eval_expr fuel' visited s a) (eval_expr fuel' visited s b)
    | EEq a b =>
      combine_bin
        (fun va vb => EVal (if Z.eqb va vb then 1%Z else 0%Z))
        (eval_expr fuel' visited s a) (eval_expr fuel' visited s b)
    | ELt a b =>
      combine_bin
        (fun va vb => EVal (if Z.ltb va vb then 1%Z else 0%Z))
        (eval_expr fuel' visited s a) (eval_expr fuel' visited s b)
    | EGt a b =>
      combine_bin
        (fun va vb => EVal (if Z.gtb va vb then 1%Z else 0%Z))
        (eval_expr fuel' visited s a) (eval_expr fuel' visited s b)
    | EIf c t e =>
      match eval_expr fuel' visited s c with
      | EVal 0%Z => eval_expr fuel' visited s e
      | EVal _   => eval_expr fuel' visited s t
      | EFVal _  => eval_expr fuel' visited s t
      | EValS _  => eval_expr fuel' visited s t
      | EValB true  => eval_expr fuel' visited s t
      | EValB false => eval_expr fuel' visited s e
      | EErr     => EErr
      | EFuel    => EFuel
      end
    | EMod a b =>
      combine_bin
        (fun va vb => if Z.eqb vb 0%Z then EErr
                      else EVal (Z.modulo va vb))
        (eval_expr fuel' visited s a) (eval_expr fuel' visited s b)
    | EPow a b =>
      combine_bin
        (fun va vb => if Z.ltb vb 0%Z then EErr
                      else EVal (Z.pow va vb))
        (eval_expr fuel' visited s a) (eval_expr fuel' visited s b)
    | ENot a =>
      match eval_expr fuel' visited s a with
      | EVal v => EVal (if Z.eqb v 0%Z then 1%Z else 0%Z)
      | r => r
      end
    | EAnd a b =>
      combine_bin
        (fun va vb =>
          EVal (if andb (negb (Z.eqb va 0%Z)) (negb (Z.eqb vb 0%Z))
                then 1%Z else 0%Z))
        (eval_expr fuel' visited s a) (eval_expr fuel' visited s b)
    | EOr a b =>
      combine_bin
        (fun va vb =>
          EVal (if orb (negb (Z.eqb va 0%Z)) (negb (Z.eqb vb 0%Z))
                then 1%Z else 0%Z))
        (eval_expr fuel' visited s a) (eval_expr fuel' visited s b)
    | ESum tl br =>
      sum_rows fuel' visited s
        (cell_col_of tl) (cell_col_of br)
        (cell_row_of tl) (cell_row_of br) 0%Z
    | ECount tl br =>
      let lc := cell_col_of tl in
      let hc := cell_col_of br in
      let lr := cell_row_of tl in
      let hr := cell_row_of br in
      if orb (PrimInt63.ltb hc lc) (PrimInt63.ltb hr lr) then EVal 0%Z
      else
        let cs := PrimInt63.add (PrimInt63.sub hc lc) 1 in
        let rs := PrimInt63.add (PrimInt63.sub hr lr) 1 in
        EVal (Uint63.to_Z (PrimInt63.mul cs rs))
    | EAvg tl br =>
      let lc := cell_col_of tl in
      let hc := cell_col_of br in
      let lr := cell_row_of tl in
      let hr := cell_row_of br in
      if orb (PrimInt63.ltb hc lc) (PrimInt63.ltb hr lr) then EErr
      else
        let cs := PrimInt63.add (PrimInt63.sub hc lc) 1 in
        let rs := PrimInt63.add (PrimInt63.sub hr lr) 1 in
        let count := Uint63.to_Z (PrimInt63.mul cs rs) in
        if Z.eqb count 0%Z then EErr
        else
          match sum_rows fuel' visited s lc hc lr hr 0%Z with
          | EVal sum => EVal (Z.div sum count)
          | r => r
          end
    | EIfErr a fb =>
      match eval_expr fuel' visited s a with
      | EVal v  => EVal v
      | EFVal f => EFVal f
      | EValS s' => EValS s'
      | EValB b => EValB b
      | EErr    => eval_expr fuel' visited s fb
      | EFuel   => EFuel
      end
    | EFAdd a b =>
      combine_binf (fun fa fb => EFVal (PrimFloat.add fa fb))
        (eval_expr fuel' visited s a) (eval_expr fuel' visited s b)
    | EFSub a b =>
      combine_binf (fun fa fb => EFVal (PrimFloat.sub fa fb))
        (eval_expr fuel' visited s a) (eval_expr fuel' visited s b)
    | EFMul a b =>
      combine_binf (fun fa fb => EFVal (PrimFloat.mul fa fb))
        (eval_expr fuel' visited s a) (eval_expr fuel' visited s b)
    | EFDiv a b =>
      combine_binf (fun fa fb => EFVal (PrimFloat.div fa fb))
        (eval_expr fuel' visited s a) (eval_expr fuel' visited s b)
    | EStr s' => EValS s'
    | EConcat a b =>
      combine_bins (fun sa sb => EValS (PrimString.cat sa sb))
        (eval_expr fuel' visited s a) (eval_expr fuel' visited s b)
    | ELen a =>
      match eval_expr fuel' visited s a with
      | EValS sv => EVal (Uint63.to_Z (PrimString.length sv))
      | EErr     => EErr
      | EFuel    => EFuel
      | _        => EErr
      end
    | ESubstr str start len =>
      match eval_expr fuel' visited s str,
            eval_expr fuel' visited s start,
            eval_expr fuel' visited s len with
      | EFuel, _, _ => EFuel
      | _, EFuel, _ => EFuel
      | _, _, EFuel => EFuel
      | EErr, _, _ => EErr
      | _, EErr, _ => EErr
      | _, _, EErr => EErr
      | EValS sv, EVal startv, EVal lenv =>
          EValS (PrimString.sub sv (Uint63.of_Z startv) (Uint63.of_Z lenv))
      | _, _, _ => EErr
      end
    | EBool b => EValB b
    | EBNot a =>
      match eval_expr fuel' visited s a with
      | EValB b => EValB (negb b)
      | EErr    => EErr
      | EFuel   => EFuel
      | _       => EErr
      end
    | EBAnd a b =>
      match eval_expr fuel' visited s a, eval_expr fuel' visited s b with
      | EFuel, _ | _, EFuel => EFuel
      | EErr, _ | _, EErr => EErr
      | EValB ba, EValB bb => EValB (andb ba bb)
      | _, _ => EErr
      end
    | EBOr a b =>
      match eval_expr fuel' visited s a, eval_expr fuel' visited s b with
      | EFuel, _ | _, EFuel => EFuel
      | EErr, _ | _, EErr => EErr
      | EValB ba, EValB bb => EValB (orb ba bb)
      | _, _ => EErr
      end
    end
  end

with eval_at_ref (fuel : nat) (visited : list CellRef) (s : Sheet)
                 (r : CellRef) : EvalResult :=
  match fuel with
  | O => EFuel
  | S fuel' =>
    if mem_cellref r visited then EErr
    else
      match get_cell s r with
      | CEmpty   => EVal 0%Z
      | CLit n   => EVal n
      | CFloat f => EFVal f
      | CStr s'  => EValS s'
      | CBool b  => EValB b
      | CForm e  => eval_expr fuel' (r :: visited) s e
      end
  end

with sum_cols (fuel : nat) (visited : list CellRef) (s : Sheet)
              (col hc : int) (row : int) (acc : Z) : EvalResult :=
  match fuel with
  | O => EFuel
  | S fuel' =>
    if PrimInt63.ltb hc col then EVal acc
    else
      match eval_at_ref fuel' visited s (mkRef col row) with
      | EVal v  => sum_cols fuel' visited s
                     (PrimInt63.add col 1) hc row (Z.add acc v)
      | EFVal _ => EErr
      | EValS _ => EErr
      | EValB _ => EErr
      | EErr    => EErr
      | EFuel   => EFuel
      end
  end

with sum_rows (fuel : nat) (visited : list CellRef) (s : Sheet)
              (lc hc : int) (row hr : int) (acc : Z) : EvalResult :=
  match fuel with
  | O => EFuel
  | S fuel' =>
    if PrimInt63.ltb hr row then EVal acc
    else
      match sum_cols fuel' visited s lc hc row acc with
      | EVal acc' => sum_rows fuel' visited s lc hc
                       (PrimInt63.add row 1) hr acc'
      | EFVal _   => EErr
      | EValS _   => EErr
      | EValB _   => EErr
      | EErr      => EErr
      | EFuel     => EFuel
      end
  end.

Definition eval_cell (fuel : nat) (s : Sheet) (r : CellRef) : EvalResult :=
  match get_cell s r with
  | CEmpty   => EVal 0%Z
  | CLit n   => EVal n
  | CFloat f => EFVal f
  | CStr s'  => EValS s'
  | CBool b  => EValB b
  | CForm e  => eval_expr fuel (r :: nil) s e
  end.

Definition DEFAULT_FUEL : nat := 4000.

Definition smoke : EvalResult :=
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
  get_cell s r = CEmpty -> eval_cell fuel s r = EVal 0%Z.
Proof. intros s r fuel H. unfold eval_cell. rewrite H. reflexivity. Qed.

Theorem eval_lit : forall s r n fuel,
  get_cell s r = CLit n -> eval_cell fuel s r = EVal n.
Proof. intros s r n fuel H. unfold eval_cell. rewrite H. reflexivity. Qed.

Theorem get_set_eq : forall s r c,
  PrimInt63.ltb (cell_index r) (PrimArray.length s) = true ->
  get_cell (set_cell s r c) r = c.
Proof.
  intros s r c Hbound.
  unfold get_cell, set_cell.
  exact (@get_set_same Cell s (cell_index r) c Hbound).
Qed.

Theorem get_set_neq : forall s r1 r2 c,
  cell_index r1 <> cell_index r2 ->
  get_cell (set_cell s r2 c) r1 = get_cell s r1.
Proof.
  intros s r1 r2 c Hneq.
  unfold get_cell, set_cell.
  exact (@get_set_other Cell s (cell_index r2) (cell_index r1) c
    (fun H => Hneq (eq_sym H))).
Qed.

Theorem smoke_computes : smoke = EVal 35%Z.
Proof. vm_compute. reflexivity. Qed.

Theorem eval_self_cycle_diverges :
  let r := mkRef 0 0 in
  let s := set_cell new_sheet r (CForm (ERef r)) in
  eval_cell DEFAULT_FUEL s r = EErr.
Proof. vm_compute. reflexivity. Qed.

Theorem eval_divzero :
  let r := mkRef 0 0 in
  let s := set_cell new_sheet r
    (CForm (EDiv (EInt 1%Z) (EInt 0%Z))) in
  eval_cell DEFAULT_FUEL s r = EErr.
Proof. vm_compute. reflexivity. Qed.

Theorem eval_if_then :
  let r := mkRef 0 0 in
  let s := set_cell new_sheet r
    (CForm (EIf (EInt 1%Z) (EInt 7%Z) (EInt 99%Z))) in
  eval_cell DEFAULT_FUEL s r = EVal 7%Z.
Proof. vm_compute. reflexivity. Qed.

Theorem eval_if_else :
  let r := mkRef 0 0 in
  let s := set_cell new_sheet r
    (CForm (EIf (EInt 0%Z) (EInt 7%Z) (EInt 99%Z))) in
  eval_cell DEFAULT_FUEL s r = EVal 99%Z.
Proof. vm_compute. reflexivity. Qed.

Theorem eval_eq_refl :
  let r := mkRef 0 0 in
  let s := set_cell new_sheet r
    (CForm (EEq (EInt 42%Z) (EInt 42%Z))) in
  eval_cell DEFAULT_FUEL s r = EVal 1%Z.
Proof. vm_compute. reflexivity. Qed.

Theorem eval_eq_distinct :
  let r := mkRef 0 0 in
  let s := set_cell new_sheet r
    (CForm (EEq (EInt 1%Z) (EInt 2%Z))) in
  eval_cell DEFAULT_FUEL s r = EVal 0%Z.
Proof. vm_compute. reflexivity. Qed.

Theorem eval_lt_true :
  let r := mkRef 0 0 in
  let s := set_cell new_sheet r
    (CForm (ELt (EInt 1%Z) (EInt 2%Z))) in
  eval_cell DEFAULT_FUEL s r = EVal 1%Z.
Proof. vm_compute. reflexivity. Qed.

Theorem eval_gt_false :
  let r := mkRef 0 0 in
  let s := set_cell new_sheet r
    (CForm (EGt (EInt 1%Z) (EInt 2%Z))) in
  eval_cell DEFAULT_FUEL s r = EVal 0%Z.
Proof. vm_compute. reflexivity. Qed.

Theorem mem_cellref_eval_ref_err : forall fuel visited s r,
  mem_cellref r visited = true ->
  eval_expr (S fuel) visited s (ERef r) = EErr.
Proof. intros fuel visited s r H. simpl. rewrite H. reflexivity. Qed.

(* --- Friendly preconditions for callers ----------------------------- *)

Definition valid_ref (r : CellRef) : bool :=
  andb (PrimInt63.ltb (ref_col r) NUM_COLS)
       (PrimInt63.ltb (ref_row r) NUM_ROWS).

Lemma length_new_sheet : PrimArray.length new_sheet = GRID_SIZE.
Proof. vm_compute. reflexivity. Qed.

Lemma length_set_cell : forall s r c,
  PrimArray.length (set_cell s r c) = PrimArray.length s.
Proof.
  intros s r c. unfold set_cell.
  apply (@length_set Cell s (cell_index r) c).
Qed.

Lemma cell_index_in_grid_general :
  forall (NC NR : int) (r : CellRef),
    PrimInt63.ltb (ref_col r) NC = true ->
    PrimInt63.ltb (ref_row r) NR = true ->
    (to_Z NC * to_Z NR < wB)%Z ->
    (0 < to_Z NC)%Z ->
    PrimInt63.ltb
      (PrimInt63.add (PrimInt63.mul (ref_row r) NC) (ref_col r))
      (PrimInt63.mul NC NR) = true.
Proof.
  intros NC NR r Hcol Hrow Hfit Hpos.
  rewrite ltb_spec in Hcol, Hrow.
  apply ltb_spec.
  pose proof (to_Z_bounded (ref_col r)).
  pose proof (to_Z_bounded (ref_row r)).
  pose proof (to_Z_bounded NC).
  pose proof (to_Z_bounded NR).
  rewrite add_spec, !mul_spec.
  rewrite (Z.mod_small (to_Z NC * to_Z NR)) by lia.
  rewrite (Z.mod_small (to_Z (ref_row r) * to_Z NC)) by nia.
  rewrite Z.mod_small.
  - nia.
  - split.
    + apply Z.add_nonneg_nonneg; lia.
    + nia.
Qed.

Lemma cell_index_in_grid : forall r,
  valid_ref r = true ->
  PrimInt63.ltb (cell_index r) GRID_SIZE = true.
Proof.
  intros r Hv.
  unfold valid_ref in Hv.
  apply Bool.andb_true_iff in Hv as [Hcol Hrow].
  unfold cell_index, GRID_SIZE.
  apply cell_index_in_grid_general; try assumption.
  - assert (to_Z NUM_COLS = 260%Z) by reflexivity.
    assert (to_Z NUM_ROWS = 200%Z) by reflexivity.
    assert (wB = 9223372036854775808%Z) by reflexivity.
    nia.
  - assert (to_Z NUM_COLS = 260%Z) by reflexivity. lia.
Qed.

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

(* --- Sheet well-formedness ----------------------------------------- *)

Definition well_formed_sheet (s : Sheet) : Prop :=
  PrimArray.length s = GRID_SIZE.

Lemma new_sheet_wf : well_formed_sheet new_sheet.
Proof. unfold well_formed_sheet. apply length_new_sheet. Qed.

Lemma set_cell_preserves_wf : forall s r c,
  well_formed_sheet s -> well_formed_sheet (set_cell s r c).
Proof.
  unfold well_formed_sheet. intros s r c H.
  rewrite length_set_cell. exact H.
Qed.

Theorem get_set_eq_wf : forall s r c,
  well_formed_sheet s ->
  valid_ref r = true ->
  get_cell (set_cell s r c) r = c.
Proof.
  unfold well_formed_sheet. intros s r c H Hv.
  apply get_set_eq_valid; assumption.
Qed.

(* --- cellref_eqb soundness ----------------------------------------- *)

Lemma cellref_eqb_sound : forall r1 r2,
  cellref_eqb r1 r2 = true <-> r1 = r2.
Proof.
  intros [c1 r1] [c2 r2]. unfold cellref_eqb. simpl.
  rewrite Bool.andb_true_iff.
  split.
  - intros [Hc Hr].
    apply eqb_correct in Hc.
    apply eqb_correct in Hr.
    subst. reflexivity.
  - intros Heq. injection Heq as Hc Hr. subst.
    split; apply eqb_refl.
Qed.

Lemma cellref_eqb_refl : forall r,
  cellref_eqb r r = true.
Proof.
  intros r. apply cellref_eqb_sound. reflexivity.
Qed.

Lemma cell_index_inj : forall r1 r2,
  valid_ref r1 = true -> valid_ref r2 = true ->
  cell_index r1 = cell_index r2 ->
  r1 = r2.
Proof.
  intros [c1 rw1] [c2 rw2] Hv1 Hv2 Hidx.
  unfold valid_ref in *. simpl in *.
  apply Bool.andb_true_iff in Hv1 as [Hc1 Hr1].
  apply Bool.andb_true_iff in Hv2 as [Hc2 Hr2].
  rewrite ltb_spec in Hc1, Hr1, Hc2, Hr2.
  unfold cell_index in Hidx. simpl in Hidx.
  pose proof (to_Z_bounded c1).
  pose proof (to_Z_bounded c2).
  pose proof (to_Z_bounded rw1).
  pose proof (to_Z_bounded rw2).
  assert (E1 : to_Z NUM_COLS = 260%Z) by reflexivity.
  assert (E2 : to_Z NUM_ROWS = 200%Z) by reflexivity.
  assert (EwB : wB = 9223372036854775808%Z) by reflexivity.
  rewrite E1 in *. rewrite E2 in *. rewrite EwB in *.
  apply (f_equal to_Z) in Hidx.
  rewrite !add_spec, !mul_spec in Hidx.
  rewrite !(Z.mod_small (to_Z _ * 260)) in Hidx by nia.
  rewrite !Z.mod_small in Hidx by nia.
  assert (Hr_eq : to_Z rw1 = to_Z rw2) by nia.
  assert (Hc_eq : to_Z c1 = to_Z c2) by nia.
  apply to_Z_inj in Hr_eq.
  apply to_Z_inj in Hc_eq.
  subst. reflexivity.
Qed.

(* --- Fuel monotonicity over the three-state result --------------- *)

Lemma combine_bin_left_not_fuel :
  forall op ra rb,
    combine_bin op ra rb <> EFuel ->
    ra <> EFuel.
Proof. intros op ra rb H Heq. subst. simpl in H. congruence. Qed.

Lemma combine_bin_right_not_fuel :
  forall op ra rb,
    combine_bin op ra rb <> EFuel ->
    rb <> EFuel.
Proof.
  intros op ra rb H Heq. subst. destruct ra; simpl in H; congruence.
Qed.

Lemma combine_bin_monotone_eq :
  forall op ra ra' rb rb',
    (ra <> EFuel -> ra' = ra) ->
    (rb <> EFuel -> rb' = rb) ->
    combine_bin op ra rb <> EFuel ->
    combine_bin op ra' rb' = combine_bin op ra rb.
Proof.
  intros op ra ra' rb rb' Ha Hb Hnf.
  rewrite (Ha (combine_bin_left_not_fuel _ _ _ Hnf)).
  rewrite (Hb (combine_bin_right_not_fuel _ _ _ Hnf)).
  reflexivity.
Qed.

Lemma combine_binf_left_not_fuel :
  forall op ra rb,
    combine_binf op ra rb <> EFuel ->
    ra <> EFuel.
Proof. intros op ra rb H Heq. subst. simpl in H. congruence. Qed.

Lemma combine_binf_right_not_fuel :
  forall op ra rb,
    combine_binf op ra rb <> EFuel ->
    rb <> EFuel.
Proof.
  intros op ra rb H Heq. subst. destruct ra; simpl in H; congruence.
Qed.

Lemma combine_binf_monotone_eq :
  forall op ra ra' rb rb',
    (ra <> EFuel -> ra' = ra) ->
    (rb <> EFuel -> rb' = rb) ->
    combine_binf op ra rb <> EFuel ->
    combine_binf op ra' rb' = combine_binf op ra rb.
Proof.
  intros op ra ra' rb rb' Ha Hb Hnf.
  rewrite (Ha (combine_binf_left_not_fuel _ _ _ Hnf)).
  rewrite (Hb (combine_binf_right_not_fuel _ _ _ Hnf)).
  reflexivity.
Qed.

Lemma combine_bins_left_not_fuel :
  forall op ra rb,
    combine_bins op ra rb <> EFuel ->
    ra <> EFuel.
Proof. intros op ra rb H Heq. subst. simpl in H. congruence. Qed.

Lemma combine_bins_right_not_fuel :
  forall op ra rb,
    combine_bins op ra rb <> EFuel ->
    rb <> EFuel.
Proof.
  intros op ra rb H Heq. subst. destruct ra; simpl in H; congruence.
Qed.

Lemma combine_bins_monotone_eq :
  forall op ra ra' rb rb',
    (ra <> EFuel -> ra' = ra) ->
    (rb <> EFuel -> rb' = rb) ->
    combine_bins op ra rb <> EFuel ->
    combine_bins op ra' rb' = combine_bins op ra rb.
Proof.
  intros op ra ra' rb rb' Ha Hb Hnf.
  rewrite (Ha (combine_bins_left_not_fuel _ _ _ Hnf)).
  rewrite (Hb (combine_bins_right_not_fuel _ _ _ Hnf)).
  reflexivity.
Qed.

Lemma fuel_monotone_all : forall fuel,
  (forall e fuel' visited s,
     fuel <= fuel' ->
     eval_expr fuel visited s e <> EFuel ->
     eval_expr fuel' visited s e = eval_expr fuel visited s e) /\
  (forall r fuel' visited s,
     fuel <= fuel' ->
     eval_at_ref fuel visited s r <> EFuel ->
     eval_at_ref fuel' visited s r = eval_at_ref fuel visited s r) /\
  (forall col hc row acc fuel' visited s,
     fuel <= fuel' ->
     sum_cols fuel visited s col hc row acc <> EFuel ->
     sum_cols fuel' visited s col hc row acc =
     sum_cols fuel visited s col hc row acc) /\
  (forall lc hc row hr acc fuel' visited s,
     fuel <= fuel' ->
     sum_rows fuel visited s lc hc row hr acc <> EFuel ->
     sum_rows fuel' visited s lc hc row hr acc =
     sum_rows fuel visited s lc hc row hr acc).
Proof.
  induction fuel as [|fuel IH].
  - split; [|split; [|split]];
      intros until s; intros _ Hnf; simpl in *; congruence.
  - destruct IH as [IHe [IHr [IHc IHs]]].
    split; [|split; [|split]].
    + (* eval_expr *)
      intros e fuel' visited s Hle Hnf.
      destruct fuel' as [|fuel']; [lia|].
      assert (Hle' : fuel <= fuel') by lia.
      simpl in Hnf. simpl.
      destruct e;
        try (apply combine_bin_monotone_eq; try assumption;
             intros Hr; apply IHe; assumption);
        try (apply combine_binf_monotone_eq; try assumption;
             intros Hr; apply IHe; assumption);
        try (apply combine_bins_monotone_eq; try assumption;
             intros Hr; apply IHe; assumption).
      * reflexivity.
      * destruct (mem_cellref c visited); [reflexivity|].
        destruct (get_cell s c); try reflexivity.
        apply IHe; assumption.
      * (* EIf *)
        destruct (eval_expr fuel visited s e1) eqn:Ec; try congruence.
        -- rewrite (IHe e1 fuel' visited s Hle') by congruence.
           rewrite Ec.
           destruct z; apply IHe; assumption.
        -- (* EFVal: nonzero/non-NaN takes the then branch. *)
           rewrite (IHe e1 fuel' visited s Hle') by congruence.
           rewrite Ec.
           apply IHe; assumption.
        -- (* EValS: any string is truthy. *)
           rewrite (IHe e1 fuel' visited s Hle') by congruence.
           rewrite Ec.
           apply IHe; assumption.
        -- (* EValB: dispatch on the literal bool. *)
           rewrite (IHe e1 fuel' visited s Hle') by congruence.
           rewrite Ec.
           destruct b; apply IHe; assumption.
        -- rewrite (IHe e1 fuel' visited s Hle') by congruence.
           rewrite Ec. reflexivity.
      * (* ENot *)
        destruct (eval_expr fuel visited s e) eqn:Ea; try congruence;
          rewrite (IHe e fuel' visited s Hle') by congruence;
          rewrite Ea; reflexivity.
      * (* ESum *)
        apply IHs; assumption.
      * (* EAvg *)
        destruct (orb (PrimInt63.ltb (cell_col_of c0) (cell_col_of c))
                      (PrimInt63.ltb (cell_row_of c0) (cell_row_of c))).
        -- reflexivity.
        -- destruct (Z.eqb _ 0%Z); [reflexivity|].
           destruct (sum_rows fuel _ _ _ _ _ _ _) eqn:Esr; try congruence.
           ++ rewrite (IHs _ _ _ _ _ _ _ _ Hle') by congruence.
              rewrite Esr. reflexivity.
           ++ (* EFVal *)
              rewrite (IHs _ _ _ _ _ _ _ _ Hle') by congruence.
              rewrite Esr. reflexivity.
           ++ (* EValS *)
              rewrite (IHs _ _ _ _ _ _ _ _ Hle') by congruence.
              rewrite Esr. reflexivity.
           ++ (* EValB *)
              rewrite (IHs _ _ _ _ _ _ _ _ Hle') by congruence.
              rewrite Esr. reflexivity.
           ++ rewrite (IHs _ _ _ _ _ _ _ _ Hle') by congruence.
              rewrite Esr. reflexivity.
      * (* ECount *)
        destruct (orb _ _); reflexivity.
      * (* EIfErr *)
        destruct (eval_expr fuel visited s e1) eqn:Ea.
        -- rewrite (IHe e1 fuel' visited s Hle') by congruence.
           rewrite Ea. reflexivity.
        -- (* EFVal: passthrough *)
           rewrite (IHe e1 fuel' visited s Hle') by congruence.
           rewrite Ea. reflexivity.
        -- (* EValS: passthrough *)
           rewrite (IHe e1 fuel' visited s Hle') by congruence.
           rewrite Ea. reflexivity.
        -- (* EValB: passthrough *)
           rewrite (IHe e1 fuel' visited s Hle') by congruence.
           rewrite Ea. reflexivity.
        -- rewrite (IHe e1 fuel' visited s Hle') by congruence.
           rewrite Ea.
           apply IHe; assumption.
        -- congruence.
      * (* EFloat *) reflexivity.
      * (* EStr *) reflexivity.
      * (* ELen *)
        destruct (eval_expr fuel visited s e) eqn:Ea; try congruence;
          rewrite (IHe e fuel' visited s Hle') by congruence;
          rewrite Ea; reflexivity.
      * (* ESubstr *)
        destruct (eval_expr fuel visited s e1) eqn:Es;
        destruct (eval_expr fuel visited s e2) eqn:Estart;
        destruct (eval_expr fuel visited s e3) eqn:Elen;
        try congruence;
        try (rewrite (IHe e1 fuel' visited s Hle') by congruence;
             rewrite (IHe e2 fuel' visited s Hle') by congruence;
             rewrite (IHe e3 fuel' visited s Hle') by congruence;
             rewrite Es, Estart, Elen; reflexivity).
      * (* EBool *) reflexivity.
      * (* EBNot *)
        destruct (eval_expr fuel visited s e) eqn:Ea; try congruence;
          rewrite (IHe e fuel' visited s Hle') by congruence;
          rewrite Ea; reflexivity.
      * (* EBAnd *)
        destruct (eval_expr fuel visited s e1) eqn:Ea;
        destruct (eval_expr fuel visited s e2) eqn:Eb;
        try congruence;
        try (rewrite (IHe e1 fuel' visited s Hle') by congruence;
             rewrite (IHe e2 fuel' visited s Hle') by congruence;
             rewrite Ea, Eb; reflexivity).
      * (* EBOr *)
        destruct (eval_expr fuel visited s e1) eqn:Ea;
        destruct (eval_expr fuel visited s e2) eqn:Eb;
        try congruence;
        try (rewrite (IHe e1 fuel' visited s Hle') by congruence;
             rewrite (IHe e2 fuel' visited s Hle') by congruence;
             rewrite Ea, Eb; reflexivity).
    + (* eval_at_ref *)
      intros r fuel' visited s Hle Hnf.
      destruct fuel' as [|fuel']; [lia|].
      assert (Hle' : fuel <= fuel') by lia.
      simpl in *.
      destruct (mem_cellref r visited); [reflexivity|].
      destruct (get_cell s r); try reflexivity.
      apply IHe; assumption.
    + (* sum_cols *)
      intros col hc row acc fuel' visited s Hle Hnf.
      destruct fuel' as [|fuel']; [lia|].
      assert (Hle' : fuel <= fuel') by lia.
      simpl in Hnf. simpl.
      destruct (PrimInt63.ltb hc col); [reflexivity|].
      destruct (eval_at_ref fuel visited s (mkRef col row)) eqn:Eat;
        try congruence.
      -- rewrite (IHr (mkRef col row) fuel' visited s Hle') by congruence.
         rewrite Eat.
         apply IHc; assumption.
      -- (* EFVal *)
         rewrite (IHr (mkRef col row) fuel' visited s Hle') by congruence.
         rewrite Eat. reflexivity.
      -- (* EValS *)
         rewrite (IHr (mkRef col row) fuel' visited s Hle') by congruence.
         rewrite Eat. reflexivity.
      -- (* EValB *)
         rewrite (IHr (mkRef col row) fuel' visited s Hle') by congruence.
         rewrite Eat. reflexivity.
      -- rewrite (IHr (mkRef col row) fuel' visited s Hle') by congruence.
         rewrite Eat. reflexivity.
    + (* sum_rows *)
      intros lc hc row hr acc fuel' visited s Hle Hnf.
      destruct fuel' as [|fuel']; [lia|].
      assert (Hle' : fuel <= fuel') by lia.
      simpl in Hnf. simpl.
      destruct (PrimInt63.ltb hr row); [reflexivity|].
      destruct (sum_cols fuel visited s lc hc row acc) eqn:Esc;
        try congruence.
      -- rewrite (IHc lc hc row acc fuel' visited s Hle') by congruence.
         rewrite Esc.
         apply IHs; assumption.
      -- (* EFVal *)
         rewrite (IHc lc hc row acc fuel' visited s Hle') by congruence.
         rewrite Esc. reflexivity.
      -- (* EValS *)
         rewrite (IHc lc hc row acc fuel' visited s Hle') by congruence.
         rewrite Esc. reflexivity.
      -- (* EValB *)
         rewrite (IHc lc hc row acc fuel' visited s Hle') by congruence.
         rewrite Esc. reflexivity.
      -- rewrite (IHc lc hc row acc fuel' visited s Hle') by congruence.
         rewrite Esc. reflexivity.
Qed.

Theorem eval_fuel_monotone :
  forall fuel e fuel' visited s v,
    fuel <= fuel' ->
    eval_expr fuel visited s e = EVal v ->
    eval_expr fuel' visited s e = EVal v.
Proof.
  intros fuel e fuel' visited s v Hle Hev.
  rewrite (proj1 (fuel_monotone_all fuel) e fuel' visited s Hle)
    by (rewrite Hev; congruence).
  exact Hev.
Qed.

Theorem eval_fuel_monotone_err :
  forall fuel e fuel' visited s,
    fuel <= fuel' ->
    eval_expr fuel visited s e = EErr ->
    eval_expr fuel' visited s e = EErr.
Proof.
  intros fuel e fuel' visited s Hle Hev.
  rewrite (proj1 (fuel_monotone_all fuel) e fuel' visited s Hle)
    by (rewrite Hev; congruence).
  exact Hev.
Qed.

Theorem eval_at_ref_fuel_monotone :
  forall fuel r fuel' visited s v,
    fuel <= fuel' ->
    eval_at_ref fuel visited s r = EVal v ->
    eval_at_ref fuel' visited s r = EVal v.
Proof.
  intros fuel r fuel' visited s v Hle Hev.
  rewrite (proj1 (proj2 (fuel_monotone_all fuel)) r fuel' visited s Hle)
    by (rewrite Hev; congruence).
  exact Hev.
Qed.

Theorem sum_cols_fuel_monotone :
  forall fuel col hc row acc fuel' visited s v,
    fuel <= fuel' ->
    sum_cols fuel visited s col hc row acc = EVal v ->
    sum_cols fuel' visited s col hc row acc = EVal v.
Proof.
  intros fuel col hc row acc fuel' visited s v Hle Hev.
  rewrite (proj1 (proj2 (proj2 (fuel_monotone_all fuel)))
             col hc row acc fuel' visited s Hle)
    by (rewrite Hev; congruence).
  exact Hev.
Qed.

Theorem sum_rows_fuel_monotone :
  forall fuel lc hc row hr acc fuel' visited s v,
    fuel <= fuel' ->
    sum_rows fuel visited s lc hc row hr acc = EVal v ->
    sum_rows fuel' visited s lc hc row hr acc = EVal v.
Proof.
  intros fuel lc hc row hr acc fuel' visited s v Hle Hev.
  rewrite (proj2 (proj2 (proj2 (fuel_monotone_all fuel)))
             lc hc row hr acc fuel' visited s Hle)
    by (rewrite Hev; congruence).
  exact Hev.
Qed.

(* --- Algebraic lifts from Z --------------------------------------- *)

Theorem eval_add_lit : forall a b fuel visited s,
  eval_expr (S (S fuel)) visited s (EAdd (EInt a) (EInt b)) =
    EVal (Z.add a b).
Proof. reflexivity. Qed.

Theorem eval_sub_lit : forall a b fuel visited s,
  eval_expr (S (S fuel)) visited s (ESub (EInt a) (EInt b)) =
    EVal (Z.sub a b).
Proof. reflexivity. Qed.

Theorem eval_mul_lit : forall a b fuel visited s,
  eval_expr (S (S fuel)) visited s (EMul (EInt a) (EInt b)) =
    EVal (Z.mul a b).
Proof. reflexivity. Qed.

Theorem eval_add_comm : forall a b fuel visited s,
  eval_expr (S (S fuel)) visited s (EAdd (EInt a) (EInt b)) =
  eval_expr (S (S fuel)) visited s (EAdd (EInt b) (EInt a)).
Proof.
  intros. rewrite !eval_add_lit. f_equal. apply Z.add_comm.
Qed.

Theorem eval_mul_comm : forall a b fuel visited s,
  eval_expr (S (S fuel)) visited s (EMul (EInt a) (EInt b)) =
  eval_expr (S (S fuel)) visited s (EMul (EInt b) (EInt a)).
Proof.
  intros. rewrite !eval_mul_lit. f_equal. apply Z.mul_comm.
Qed.

Theorem eval_add_zero_l : forall a fuel visited s,
  eval_expr (S (S fuel)) visited s (EAdd (EInt 0%Z) (EInt a)) = EVal a.
Proof. reflexivity. Qed.

Theorem eval_mul_one_l : forall a fuel visited s,
  eval_expr (S (S fuel)) visited s (EMul (EInt 1%Z) (EInt a)) = EVal a.
Proof.
  intros. rewrite eval_mul_lit. rewrite Z.mul_1_l. reflexivity.
Qed.

Theorem eval_eq_lit : forall a b fuel visited s,
  eval_expr (S (S fuel)) visited s (EEq (EInt a) (EInt b)) =
    EVal (if Z.eqb a b then 1%Z else 0%Z).
Proof. reflexivity. Qed.

Theorem eval_lt_lit : forall a b fuel visited s,
  eval_expr (S (S fuel)) visited s (ELt (EInt a) (EInt b)) =
    EVal (if Z.ltb a b then 1%Z else 0%Z).
Proof. reflexivity. Qed.

(* --- Compositional evaluation over arbitrary subexpressions ------- *)

Lemma eval_expr_compositional_add :
  forall fuel visited s a b va vb,
    eval_expr fuel visited s a = EVal va ->
    eval_expr fuel visited s b = EVal vb ->
    eval_expr (S fuel) visited s (EAdd a b) = EVal (Z.add va vb).
Proof. intros. simpl. rewrite H, H0. reflexivity. Qed.

Lemma eval_expr_compositional_sub :
  forall fuel visited s a b va vb,
    eval_expr fuel visited s a = EVal va ->
    eval_expr fuel visited s b = EVal vb ->
    eval_expr (S fuel) visited s (ESub a b) = EVal (Z.sub va vb).
Proof. intros. simpl. rewrite H, H0. reflexivity. Qed.

Lemma eval_expr_compositional_mul :
  forall fuel visited s a b va vb,
    eval_expr fuel visited s a = EVal va ->
    eval_expr fuel visited s b = EVal vb ->
    eval_expr (S fuel) visited s (EMul a b) = EVal (Z.mul va vb).
Proof. intros. simpl. rewrite H, H0. reflexivity. Qed.

Lemma eval_expr_compositional_div :
  forall fuel visited s a b va vb,
    eval_expr fuel visited s a = EVal va ->
    eval_expr fuel visited s b = EVal vb ->
    Z.eqb vb 0%Z = false ->
    eval_expr (S fuel) visited s (EDiv a b) = EVal (Z.div va vb).
Proof.
  intros fuel visited s a b va vb Ha Hb Hnz.
  simpl. rewrite Ha, Hb. simpl. rewrite Hnz. reflexivity.
Qed.

(* --- Algebraic identities over compound trees -------------------- *)

Lemma eval_add_assoc_tree :
  forall fuel visited s a b c va vb vc,
    eval_expr fuel visited s a = EVal va ->
    eval_expr fuel visited s b = EVal vb ->
    eval_expr fuel visited s c = EVal vc ->
    eval_expr (S (S fuel)) visited s (EAdd (EAdd a b) c)
    = eval_expr (S (S fuel)) visited s (EAdd a (EAdd b c)).
Proof.
  intros fuel visited s a b c va vb vc Ha Hb Hc.
  assert (Hle : (fuel <= S fuel)%nat) by lia.
  pose proof (eval_fuel_monotone _ _ _ _ _ _ Hle Ha) as Ha'.
  pose proof (eval_fuel_monotone _ _ _ _ _ _ Hle Hc) as Hc'.
  pose proof (eval_expr_compositional_add fuel visited s a b va vb Ha Hb) as Hab.
  pose proof (eval_expr_compositional_add fuel visited s b c vb vc Hb Hc) as Hbc.
  rewrite (eval_expr_compositional_add (S fuel) visited s (EAdd a b) c
             (Z.add va vb) vc Hab Hc').
  rewrite (eval_expr_compositional_add (S fuel) visited s a (EAdd b c)
             va (Z.add vb vc) Ha' Hbc).
  f_equal. lia.
Qed.

Lemma eval_mul_assoc_tree :
  forall fuel visited s a b c va vb vc,
    eval_expr fuel visited s a = EVal va ->
    eval_expr fuel visited s b = EVal vb ->
    eval_expr fuel visited s c = EVal vc ->
    eval_expr (S (S fuel)) visited s (EMul (EMul a b) c)
    = eval_expr (S (S fuel)) visited s (EMul a (EMul b c)).
Proof.
  intros fuel visited s a b c va vb vc Ha Hb Hc.
  assert (Hle : (fuel <= S fuel)%nat) by lia.
  pose proof (eval_fuel_monotone _ _ _ _ _ _ Hle Ha) as Ha'.
  pose proof (eval_fuel_monotone _ _ _ _ _ _ Hle Hc) as Hc'.
  pose proof (eval_expr_compositional_mul fuel visited s a b va vb Ha Hb) as Hab.
  pose proof (eval_expr_compositional_mul fuel visited s b c vb vc Hb Hc) as Hbc.
  rewrite (eval_expr_compositional_mul (S fuel) visited s (EMul a b) c
             (Z.mul va vb) vc Hab Hc').
  rewrite (eval_expr_compositional_mul (S fuel) visited s a (EMul b c)
             va (Z.mul vb vc) Ha' Hbc).
  f_equal. lia.
Qed.

Lemma eval_mul_distr_l_tree :
  forall fuel visited s a b c va vb vc,
    eval_expr fuel visited s a = EVal va ->
    eval_expr fuel visited s b = EVal vb ->
    eval_expr fuel visited s c = EVal vc ->
    eval_expr (S (S fuel)) visited s (EMul a (EAdd b c))
    = eval_expr (S (S (S fuel))) visited s
        (EAdd (EMul a b) (EMul a c)).
Proof.
  intros fuel visited s a b c va vb vc Ha Hb Hc.
  assert (Hle : (fuel <= S fuel)%nat) by lia.
  pose proof (eval_fuel_monotone _ _ _ _ _ _ Hle Ha) as Ha1.
  pose proof (eval_fuel_monotone _ _ _ _ _ _ Hle Hb) as Hb1.
  pose proof (eval_fuel_monotone _ _ _ _ _ _ Hle Hc) as Hc1.
  pose proof (eval_expr_compositional_add fuel visited s b c vb vc Hb Hc) as Hbc.
  pose proof (eval_expr_compositional_mul (S fuel) visited s a (EAdd b c)
                va (Z.add vb vc) Ha1 Hbc) as Hlhs.
  pose proof (eval_expr_compositional_mul (S fuel) visited s a b
                va vb Ha1 Hb1) as Hab.
  pose proof (eval_expr_compositional_mul (S fuel) visited s a c
                va vc Ha1 Hc1) as Hac.
  pose proof (eval_expr_compositional_add (S (S fuel)) visited s
                (EMul a b) (EMul a c) (Z.mul va vb) (Z.mul va vc)
                Hab Hac) as Hrhs.
  rewrite Hlhs, Hrhs. f_equal. lia.
Qed.

Lemma eval_mul_distr_r_tree :
  forall fuel visited s a b c va vb vc,
    eval_expr fuel visited s a = EVal va ->
    eval_expr fuel visited s b = EVal vb ->
    eval_expr fuel visited s c = EVal vc ->
    eval_expr (S (S fuel)) visited s (EMul (EAdd a b) c)
    = eval_expr (S (S (S fuel))) visited s
        (EAdd (EMul a c) (EMul b c)).
Proof.
  intros fuel visited s a b c va vb vc Ha Hb Hc.
  assert (Hle : (fuel <= S fuel)%nat) by lia.
  pose proof (eval_fuel_monotone _ _ _ _ _ _ Hle Ha) as Ha1.
  pose proof (eval_fuel_monotone _ _ _ _ _ _ Hle Hb) as Hb1.
  pose proof (eval_fuel_monotone _ _ _ _ _ _ Hle Hc) as Hc1.
  pose proof (eval_expr_compositional_add fuel visited s a b va vb Ha Hb) as Hab.
  pose proof (eval_expr_compositional_mul (S fuel) visited s (EAdd a b) c
                (Z.add va vb) vc Hab Hc1) as Hlhs.
  pose proof (eval_expr_compositional_mul (S fuel) visited s a c
                va vc Ha1 Hc1) as Hac.
  pose proof (eval_expr_compositional_mul (S fuel) visited s b c
                vb vc Hb1 Hc1) as Hbc.
  pose proof (eval_expr_compositional_add (S (S fuel)) visited s
                (EMul a c) (EMul b c) (Z.mul va vc) (Z.mul vb vc)
                Hac Hbc) as Hrhs.
  rewrite Hlhs, Hrhs. f_equal. lia.
Qed.

(* --- IFERROR semantics ------------------------------------------- *)

Lemma eval_iferror_some_eq_first :
  forall fuel visited s a fb va,
    eval_expr fuel visited s a = EVal va ->
    eval_expr (S fuel) visited s (EIfErr a fb) = EVal va.
Proof.
  intros fuel visited s a fb va Ha.
  simpl. rewrite Ha. reflexivity.
Qed.

Lemma eval_iferror_err_eq_fallback :
  forall fuel visited s a fb r,
    eval_expr fuel visited s a = EErr ->
    eval_expr fuel visited s fb = r ->
    eval_expr (S fuel) visited s (EIfErr a fb) = r.
Proof.
  intros fuel visited s a fb r Ha Hfb.
  simpl. rewrite Ha. exact Hfb.
Qed.

Lemma eval_iferror_idempotent_on_val :
  forall fuel visited s a fb va,
    eval_expr fuel visited s a = EVal va ->
    eval_expr (S (S fuel)) visited s (EIfErr (EIfErr a fb) fb)
    = EVal va.
Proof.
  intros fuel visited s a fb va Ha.
  pose proof (eval_iferror_some_eq_first fuel visited s a fb va Ha) as H1.
  apply (eval_iferror_some_eq_first (S fuel) visited s (EIfErr a fb) fb va H1).
Qed.

(* --- Float theorems ----------------------------------------------- *)

Theorem eval_float_lit : forall fuel visited s f,
  eval_expr (S fuel) visited s (EFloat f) = EFVal f.
Proof. reflexivity. Qed.

Theorem eval_fadd_lit : forall fuel visited s a b,
  eval_expr (S (S fuel)) visited s (EFAdd (EFloat a) (EFloat b))
  = EFVal (PrimFloat.add a b).
Proof. reflexivity. Qed.

Theorem eval_fsub_lit : forall fuel visited s a b,
  eval_expr (S (S fuel)) visited s (EFSub (EFloat a) (EFloat b))
  = EFVal (PrimFloat.sub a b).
Proof. reflexivity. Qed.

Theorem eval_fmul_lit : forall fuel visited s a b,
  eval_expr (S (S fuel)) visited s (EFMul (EFloat a) (EFloat b))
  = EFVal (PrimFloat.mul a b).
Proof. reflexivity. Qed.

Theorem eval_fdiv_lit : forall fuel visited s a b,
  eval_expr (S (S fuel)) visited s (EFDiv (EFloat a) (EFloat b))
  = EFVal (PrimFloat.div a b).
Proof. reflexivity. Qed.

(* a + 0 = a, smoke at a finite literal. *)
Theorem eval_float_add_zero_smoke :
  let one_five := PrimFloat.of_uint63 3%uint63 in
  eval_expr 2 nil new_sheet (EFAdd (EFloat one_five) (EFloat (PrimFloat.of_uint63 0%uint63)))
  = EFVal one_five.
Proof. vm_compute. reflexivity. Qed.

(* a * 0 = 0, smoke at a finite literal. *)
Theorem eval_float_mul_zero_smoke :
  eval_expr 2 nil new_sheet
    (EFMul (EFloat (PrimFloat.of_uint63 7%uint63))
           (EFloat (PrimFloat.of_uint63 0%uint63)))
  = EFVal (PrimFloat.of_uint63 0%uint63).
Proof. vm_compute. reflexivity. Qed.

(* NaN propagation: NaN + anything is NaN under PrimFloat. *)
Theorem eval_float_nan_propagates_smoke :
  match eval_expr 2 nil new_sheet
        (EFAdd (EFloat PrimFloat.nan)
               (EFloat (PrimFloat.of_uint63 1%uint63))) with
  | EFVal f => PrimFloat.is_nan f = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

(* Commutativity of float add at concrete values. *)
Theorem eval_float_add_comm_smoke :
  eval_expr 2 nil new_sheet
    (EFAdd (EFloat (PrimFloat.of_uint63 3%uint63))
           (EFloat (PrimFloat.of_uint63 5%uint63)))
  = eval_expr 2 nil new_sheet
    (EFAdd (EFloat (PrimFloat.of_uint63 5%uint63))
           (EFloat (PrimFloat.of_uint63 3%uint63))).
Proof. vm_compute. reflexivity. Qed.

(* Signed-zero equality: +0 and -0 compare equal under PrimFloat.eqb
   (matches IEEE 754, where -0 == +0 evaluates to true). *)
Theorem eval_float_signed_zero_eqb :
  PrimFloat.eqb (PrimFloat.of_uint63 0%uint63)
                (PrimFloat.opp (PrimFloat.of_uint63 0%uint63)) = true.
Proof. vm_compute. reflexivity. Qed.

(* --- String theorems ----------------------------------------------- *)

Theorem eval_str_lit : forall fuel visited s sv,
  eval_expr (S fuel) visited s (EStr sv) = EValS sv.
Proof. reflexivity. Qed.

Theorem eval_concat_lit : forall fuel visited s a b,
  eval_expr (S (S fuel)) visited s (EConcat (EStr a) (EStr b))
  = EValS (PrimString.cat a b).
Proof. reflexivity. Qed.

Theorem eval_len_lit : forall fuel visited s sv,
  eval_expr (S (S fuel)) visited s (ELen (EStr sv))
  = EVal (Uint63.to_Z (PrimString.length sv)).
Proof. reflexivity. Qed.

(* len (concat a b) = len a + len b, smoke. *)
Theorem eval_len_concat_smoke :
  let a := "ab"%pstring in
  let b := "cd"%pstring in
  Uint63.to_Z (PrimString.length (PrimString.cat a b))
  = (Uint63.to_Z (PrimString.length a) + Uint63.to_Z (PrimString.length b))%Z.
Proof. vm_compute. reflexivity. Qed.

(* concat_assoc, smoke. *)
Theorem eval_concat_assoc_smoke :
  let a := "a"%pstring in
  let b := "b"%pstring in
  let c := "c"%pstring in
  PrimString.cat (PrimString.cat a b) c
  = PrimString.cat a (PrimString.cat b c).
Proof. vm_compute. reflexivity. Qed.

(* concat_empty_l, smoke. *)
Theorem eval_concat_empty_l_smoke :
  PrimString.cat ""%pstring "x"%pstring = "x"%pstring.
Proof. vm_compute. reflexivity. Qed.

(* concat_empty_r, smoke. *)
Theorem eval_concat_empty_r_smoke :
  PrimString.cat "x"%pstring ""%pstring = "x"%pstring.
Proof. vm_compute. reflexivity. Qed.

(* substr_full = id, smoke. *)
Theorem eval_substr_full_smoke :
  let s := "hello"%pstring in
  PrimString.sub s 0%uint63 (PrimString.length s) = s.
Proof. vm_compute. reflexivity. Qed.

(* len_substr_le_len, smoke. *)
Theorem eval_len_substr_le_len_smoke :
  (Uint63.to_Z (PrimString.length (PrimString.sub "hello"%pstring
                                                  1%uint63 3%uint63))
   <= Uint63.to_Z (PrimString.length "hello"%pstring))%Z.
Proof. vm_compute. easy. Qed.

(* --- Boolean theorems ---------------------------------------------- *)

Theorem eval_bool_lit : forall fuel visited s b,
  eval_expr (S fuel) visited s (EBool b) = EValB b.
Proof. reflexivity. Qed.

(* not_not b = b *)
Theorem eval_bnot_not : forall fuel visited s b,
  eval_expr (S (S (S fuel))) visited s (EBNot (EBNot (EBool b)))
  = EValB b.
Proof. intros. simpl. rewrite Bool.negb_involutive. reflexivity. Qed.

(* and_comm *)
Theorem eval_band_comm : forall fuel visited s a b,
  eval_expr (S (S fuel)) visited s (EBAnd (EBool a) (EBool b))
  = eval_expr (S (S fuel)) visited s (EBAnd (EBool b) (EBool a)).
Proof. intros. simpl. rewrite Bool.andb_comm. reflexivity. Qed.

(* or_comm *)
Theorem eval_bor_comm : forall fuel visited s a b,
  eval_expr (S (S fuel)) visited s (EBOr (EBool a) (EBool b))
  = eval_expr (S (S fuel)) visited s (EBOr (EBool b) (EBool a)).
Proof. intros. simpl. rewrite Bool.orb_comm. reflexivity. Qed.

(* De Morgan: NOT (a AND b) = (NOT a) OR (NOT b) *)
Theorem eval_de_morgan : forall fuel visited s a b,
  eval_expr (S (S (S fuel))) visited s (EBNot (EBAnd (EBool a) (EBool b)))
  = eval_expr (S (S (S fuel))) visited s
      (EBOr (EBNot (EBool a)) (EBNot (EBool b))).
Proof. intros. simpl. rewrite Bool.negb_andb. reflexivity. Qed.

(* if_true_then *)
Theorem eval_if_true_then : forall fuel visited s t e,
  eval_expr (S (S fuel)) visited s (EIf (EBool true) t e)
  = eval_expr (S fuel) visited s t.
Proof. reflexivity. Qed.

(* if_false_else *)
Theorem eval_if_false_else : forall fuel visited s t e,
  eval_expr (S (S fuel)) visited s (EIf (EBool false) t e)
  = eval_expr (S fuel) visited s e.
Proof. reflexivity. Qed.

End Rocqsheet.

(* Extraction is driven from theories/RocqsheetMain.v. *)
