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

(* Guard the two UB cases for signed integer division: divide-by-zero
   and INT64_MIN / -1 (whose mathematical result overflows int64).
   Both are handled by saturating to INT64_MIN. *)
Crane Extract Inlined Constant Z.div =>
  "((%a1 == 0) ? INT64_C(0) : (((%a0 == INT64_MIN) && (%a1 == -1)) ? INT64_MIN : ((%a0) / (%a1))))".
Crane Extract Inlined Constant Z.modulo =>
  "((%a1 == 0) ? INT64_C(0) : (((%a0 == INT64_MIN) && (%a1 == -1)) ? INT64_C(0) : ((%a0) % (%a1))))".

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
  | EIf  : Expr -> Expr -> Expr -> Expr
  | EMod : Expr -> Expr -> Expr
  | EPow : Expr -> Expr -> Expr
  | ENot : Expr -> Expr
  | EAnd : Expr -> Expr -> Expr
  | EOr  : Expr -> Expr -> Expr.

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
    | EMod a b =>
      match eval_expr fuel' visited s a, eval_expr fuel' visited s b with
      | Some va, Some vb =>
        if Z.eqb vb 0%Z then None else Some (Z.modulo va vb)
      | _, _ => None
      end
    | EPow a b =>
      match eval_expr fuel' visited s a, eval_expr fuel' visited s b with
      | Some va, Some vb =>
        if Z.ltb vb 0%Z then None else Some (Z.pow va vb)
      | _, _ => None
      end
    | ENot a =>
      match eval_expr fuel' visited s a with
      | Some v => Some (if Z.eqb v 0%Z then 1%Z else 0%Z)
      | None => None
      end
    | EAnd a b =>
      match eval_expr fuel' visited s a, eval_expr fuel' visited s b with
      | Some va, Some vb =>
        Some (if andb (negb (Z.eqb va 0%Z)) (negb (Z.eqb vb 0%Z))
              then 1%Z else 0%Z)
      | _, _ => None
      end
    | EOr a b =>
      match eval_expr fuel' visited s a, eval_expr fuel' visited s b with
      | Some va, Some vb =>
        Some (if orb (negb (Z.eqb va 0%Z)) (negb (Z.eqb vb 0%Z))
              then 1%Z else 0%Z)
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

(* --- cell_index injectivity on valid refs -------------------------- *)

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

(* --- Compositional None-propagation ------------------------------ *)

Lemma eval_eadd_none_l : forall fuel visited s a b,
  eval_expr fuel visited s a = None ->
  eval_expr (S fuel) visited s (EAdd a b) = None.
Proof. intros. simpl. rewrite H. reflexivity. Qed.

Lemma eval_esub_none_l : forall fuel visited s a b,
  eval_expr fuel visited s a = None ->
  eval_expr (S fuel) visited s (ESub a b) = None.
Proof. intros. simpl. rewrite H. reflexivity. Qed.

Lemma eval_emul_none_l : forall fuel visited s a b,
  eval_expr fuel visited s a = None ->
  eval_expr (S fuel) visited s (EMul a b) = None.
Proof. intros. simpl. rewrite H. reflexivity. Qed.

Lemma eval_ediv_none_l : forall fuel visited s a b,
  eval_expr fuel visited s a = None ->
  eval_expr (S fuel) visited s (EDiv a b) = None.
Proof. intros. simpl. rewrite H. reflexivity. Qed.

Lemma eval_eif_none_cond : forall fuel visited s c t e,
  eval_expr fuel visited s c = None ->
  eval_expr (S fuel) visited s (EIf c t e) = None.
Proof. intros. simpl. rewrite H. reflexivity. Qed.

(* If the right operand fails after the left succeeded, the whole
   binary op returns None. *)
Lemma eval_eadd_none_r : forall fuel visited s a b va,
  eval_expr fuel visited s a = Some va ->
  eval_expr fuel visited s b = None ->
  eval_expr (S fuel) visited s (EAdd a b) = None.
Proof. intros. simpl. rewrite H, H0. reflexivity. Qed.

(* --- Fuel monotonicity ------------------------------------------- *)

Theorem eval_fuel_monotone :
  forall fuel e fuel' visited s v,
    fuel <= fuel' ->
    eval_expr fuel visited s e = Some v ->
    eval_expr fuel' visited s e = Some v.
Proof.
  induction fuel as [|fuel IH]; intros e fuel' visited s v Hle Hev.
  - simpl in Hev. discriminate.
  - destruct fuel' as [|fuel']; [lia|].
    assert (Hle' : fuel <= fuel') by lia.
    simpl in Hev. simpl.
    destruct e as [n|r|a b|a b|a b|a b|a b|a b|a b|cnd th el|a b|a b|a|a b|a b].
    + exact Hev.
    + destruct (mem_cellref r visited); [discriminate|].
      destruct (get_cell s r) as [|n|e'].
      * exact Hev.
      * exact Hev.
      * apply (IH _ _ _ _ _ Hle' Hev).
    + destruct (eval_expr fuel visited s a) as [va|] eqn:Ea; [|discriminate].
      destruct (eval_expr fuel visited s b) as [vb|] eqn:Eb; [|discriminate].
      rewrite (IH _ _ _ _ _ Hle' Ea).
      rewrite (IH _ _ _ _ _ Hle' Eb).
      exact Hev.
    + destruct (eval_expr fuel visited s a) as [va|] eqn:Ea; [|discriminate].
      destruct (eval_expr fuel visited s b) as [vb|] eqn:Eb; [|discriminate].
      rewrite (IH _ _ _ _ _ Hle' Ea).
      rewrite (IH _ _ _ _ _ Hle' Eb).
      exact Hev.
    + destruct (eval_expr fuel visited s a) as [va|] eqn:Ea; [|discriminate].
      destruct (eval_expr fuel visited s b) as [vb|] eqn:Eb; [|discriminate].
      rewrite (IH _ _ _ _ _ Hle' Ea).
      rewrite (IH _ _ _ _ _ Hle' Eb).
      exact Hev.
    + destruct (eval_expr fuel visited s a) as [va|] eqn:Ea; [|discriminate].
      destruct (eval_expr fuel visited s b) as [vb|] eqn:Eb; [|discriminate].
      rewrite (IH _ _ _ _ _ Hle' Ea).
      rewrite (IH _ _ _ _ _ Hle' Eb).
      exact Hev.
    + destruct (eval_expr fuel visited s a) as [va|] eqn:Ea; [|discriminate].
      destruct (eval_expr fuel visited s b) as [vb|] eqn:Eb; [|discriminate].
      rewrite (IH _ _ _ _ _ Hle' Ea).
      rewrite (IH _ _ _ _ _ Hle' Eb).
      exact Hev.
    + destruct (eval_expr fuel visited s a) as [va|] eqn:Ea; [|discriminate].
      destruct (eval_expr fuel visited s b) as [vb|] eqn:Eb; [|discriminate].
      rewrite (IH _ _ _ _ _ Hle' Ea).
      rewrite (IH _ _ _ _ _ Hle' Eb).
      exact Hev.
    + destruct (eval_expr fuel visited s a) as [va|] eqn:Ea; [|discriminate].
      destruct (eval_expr fuel visited s b) as [vb|] eqn:Eb; [|discriminate].
      rewrite (IH _ _ _ _ _ Hle' Ea).
      rewrite (IH _ _ _ _ _ Hle' Eb).
      exact Hev.
    + destruct (eval_expr fuel visited s cnd) as [vc|] eqn:Ec; [|discriminate].
      rewrite (IH _ _ _ _ _ Hle' Ec).
      destruct vc as [|p|p].
      * apply (IH _ _ _ _ _ Hle' Hev).
      * apply (IH _ _ _ _ _ Hle' Hev).
      * apply (IH _ _ _ _ _ Hle' Hev).
    + (* EMod *)
      destruct (eval_expr fuel visited s a) as [va|] eqn:Ea; [|discriminate].
      destruct (eval_expr fuel visited s b) as [vb|] eqn:Eb; [|discriminate].
      rewrite (IH _ _ _ _ _ Hle' Ea).
      rewrite (IH _ _ _ _ _ Hle' Eb).
      exact Hev.
    + (* EPow *)
      destruct (eval_expr fuel visited s a) as [va|] eqn:Ea; [|discriminate].
      destruct (eval_expr fuel visited s b) as [vb|] eqn:Eb; [|discriminate].
      rewrite (IH _ _ _ _ _ Hle' Ea).
      rewrite (IH _ _ _ _ _ Hle' Eb).
      exact Hev.
    + (* ENot *)
      destruct (eval_expr fuel visited s a) as [va|] eqn:Ea; [|discriminate].
      rewrite (IH _ _ _ _ _ Hle' Ea).
      exact Hev.
    + (* EAnd *)
      destruct (eval_expr fuel visited s a) as [va|] eqn:Ea; [|discriminate].
      destruct (eval_expr fuel visited s b) as [vb|] eqn:Eb; [|discriminate].
      rewrite (IH _ _ _ _ _ Hle' Ea).
      rewrite (IH _ _ _ _ _ Hle' Eb).
      exact Hev.
    + (* EOr *)
      destruct (eval_expr fuel visited s a) as [va|] eqn:Ea; [|discriminate].
      destruct (eval_expr fuel visited s b) as [vb|] eqn:Eb; [|discriminate].
      rewrite (IH _ _ _ _ _ Hle' Ea).
      rewrite (IH _ _ _ _ _ Hle' Eb).
      exact Hev.
Qed.

(* --- Algebraic lifts from Z --------------------------------------- *)

Theorem eval_add_lit : forall a b fuel visited s,
  eval_expr (S (S fuel)) visited s (EAdd (EInt a) (EInt b)) =
    Some (Z.add a b).
Proof. reflexivity. Qed.

Theorem eval_sub_lit : forall a b fuel visited s,
  eval_expr (S (S fuel)) visited s (ESub (EInt a) (EInt b)) =
    Some (Z.sub a b).
Proof. reflexivity. Qed.

Theorem eval_mul_lit : forall a b fuel visited s,
  eval_expr (S (S fuel)) visited s (EMul (EInt a) (EInt b)) =
    Some (Z.mul a b).
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
  eval_expr (S (S fuel)) visited s (EAdd (EInt 0%Z) (EInt a)) = Some a.
Proof. reflexivity. Qed.

Theorem eval_mul_one_l : forall a fuel visited s,
  eval_expr (S (S fuel)) visited s (EMul (EInt 1%Z) (EInt a)) = Some a.
Proof.
  intros. rewrite eval_mul_lit. rewrite Z.mul_1_l. reflexivity.
Qed.

(* Comparison results with literal arguments. *)
Theorem eval_eq_lit : forall a b fuel visited s,
  eval_expr (S (S fuel)) visited s (EEq (EInt a) (EInt b)) =
    Some (if Z.eqb a b then 1%Z else 0%Z).
Proof. reflexivity. Qed.

Theorem eval_lt_lit : forall a b fuel visited s,
  eval_expr (S (S fuel)) visited s (ELt (EInt a) (EInt b)) =
    Some (if Z.ltb a b then 1%Z else 0%Z).
Proof. reflexivity. Qed.

End Rocqsheet.

(* Extraction is driven from theories/RocqsheetMain.v. *)
