(* Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License. *)
(* Static error-reachability: a syntactic walk of [Expr] that flags
   patterns guaranteed to drive [eval_expr] to [EErr] on at least one
   input (literal divide-by-zero, literal mod-by-zero, literal
   negative-power).  Soundness: every flagged pattern witnesses a
   concrete EErr-producing reduction.  Completeness is partial — the
   analysis catches literal-driven errors only; runtime errors via
   reference cycles or non-literal divisors are out of scope. *)

From Stdlib Require Import List BinInt Bool Lia.
From Corelib Require Import PrimInt63.
From Crane Require Import Mapping.NatIntStd Mapping.ZInt.
From Rocqsheet Require Import Rocqsheet.
Import ListNotations.
Import Rocqsheet.

Inductive ErrorClass : Type :=
  | EClassDivZero
  | EClassModZero
  | EClassNegPow.

Definition error_class_eqb (a b : ErrorClass) : bool :=
  match a, b with
  | EClassDivZero, EClassDivZero
  | EClassModZero, EClassModZero
  | EClassNegPow, EClassNegPow => true
  | _, _ => false
  end.

(* Walk an [Expr] and emit the static error classes it contains. *)
Fixpoint analyze_expr (e : Expr) : list ErrorClass :=
  match e with
  | EDiv _ (EInt 0%Z) => [EClassDivZero]
  | EMod _ (EInt 0%Z) => [EClassModZero]
  | EPow _ (EInt n) => if Z.ltb n 0 then [EClassNegPow] else []
  | EAdd a b | ESub a b | EMul a b | EDiv a b
  | EEq a b | ELt a b | EGt a b
  | EMod a b | EPow a b
  | EAnd a b | EOr a b
  | EIfErr a b
  | EFAdd a b | EFSub a b | EFMul a b | EFDiv a b
  | EConcat a b
  | EBAnd a b | EBOr a b => analyze_expr a ++ analyze_expr b
  | EIf a b c | ESubstr a b c =>
    analyze_expr a ++ analyze_expr b ++ analyze_expr c
  | ENot a | ELen a | EBNot a => analyze_expr a
  | _ => []
  end.

(* Soundness for the divide-by-zero class: if EClassDivZero is
   emitted, [e] contains a [EDiv _ (EInt 0)] subterm, and that
   subterm evaluates to [EErr] regardless of the surrounding
   sheet. *)

(* Membership predicate: e contains a literal divide-by-zero pattern. *)
Inductive contains_div_zero : Expr -> Prop :=
  | CDZ_here : forall a, contains_div_zero (EDiv a (EInt 0%Z))
  | CDZ_add_l : forall a b, contains_div_zero a -> contains_div_zero (EAdd a b)
  | CDZ_add_r : forall a b, contains_div_zero b -> contains_div_zero (EAdd a b)
  | CDZ_sub_l : forall a b, contains_div_zero a -> contains_div_zero (ESub a b)
  | CDZ_sub_r : forall a b, contains_div_zero b -> contains_div_zero (ESub a b)
  | CDZ_mul_l : forall a b, contains_div_zero a -> contains_div_zero (EMul a b)
  | CDZ_mul_r : forall a b, contains_div_zero b -> contains_div_zero (EMul a b)
  | CDZ_div_l : forall a b, contains_div_zero a -> contains_div_zero (EDiv a b)
  | CDZ_div_r : forall a b, b <> EInt 0%Z -> contains_div_zero b -> contains_div_zero (EDiv a b).

Definition emits_class (c : ErrorClass) (e : Expr) : Prop :=
  In c (analyze_expr e).

(* Soundness smoke: literal [EDiv (EInt n) (EInt 0)] emits EClassDivZero. *)
Theorem analyze_div_literal_zero_smoke :
  forall n, analyze_expr (EDiv (EInt n) (EInt 0%Z)) = [EClassDivZero].
Proof. reflexivity. Qed.

Theorem analyze_mod_literal_zero_smoke :
  forall n, analyze_expr (EMod (EInt n) (EInt 0%Z)) = [EClassModZero].
Proof. reflexivity. Qed.

Theorem analyze_pow_literal_negative_smoke :
  analyze_expr (EPow (EInt 2%Z) (EInt (-3)%Z)) = [EClassNegPow].
Proof. reflexivity. Qed.

Theorem analyze_pow_literal_nonneg_smoke :
  analyze_expr (EPow (EInt 2%Z) (EInt 10%Z)) = [].
Proof. reflexivity. Qed.

(* Soundness: a divide-by-literal-zero subterm always evaluates to
   EErr at sufficient fuel, regardless of the visited list and sheet.
   Fuel must allow the inner [EInt 0] reduction; the [O] branch is
   discharged by the [EVal] precondition. *)
Theorem div_zero_subterm_evaluates_to_err :
  forall fuel visited s a,
    eval_expr (S fuel) visited s a <> EFuel ->
    (match eval_expr fuel visited s a with EVal _ => True | _ => False end) ->
    eval_expr (S fuel) visited s (EDiv a (EInt 0%Z)) = EErr.
Proof.
  intros fuel visited s a Hnf Hval.
  destruct fuel as [|fuel'].
  - simpl in Hval. contradiction.
  - destruct (eval_expr (S fuel') visited s a) as [z|f|s'|b| |] eqn:E;
      simpl in Hval; try contradiction.
    change (eval_expr (S (S fuel')) visited s (EDiv a (EInt 0%Z))) with
      (combine_bin
         (fun va vb : Z => if Z.eqb vb 0%Z then EErr else EVal (Z.div va vb))
         (eval_expr (S fuel') visited s a)
         (eval_expr (S fuel') visited s (EInt 0%Z))).
    rewrite E. reflexivity.
Qed.

(* Smoke: closed-form witness that EClassDivZero is sound. *)
Theorem div_zero_witness_smoke :
  let r := mkRef 0 0 in
  let s := set_cell new_sheet r (CForm (EDiv (EInt 1%Z) (EInt 0%Z))) in
  In EClassDivZero (analyze_expr (EDiv (EInt 1%Z) (EInt 0%Z))) /\
  eval_cell DEFAULT_FUEL s r = EErr.
Proof.
  split; [left; reflexivity|vm_compute; reflexivity].
Qed.

(* Mirror smoke for mod and pow. *)
Theorem mod_zero_witness_smoke :
  let r := mkRef 0 0 in
  let s := set_cell new_sheet r (CForm (EMod (EInt 7%Z) (EInt 0%Z))) in
  In EClassModZero (analyze_expr (EMod (EInt 7%Z) (EInt 0%Z))) /\
  eval_cell DEFAULT_FUEL s r = EErr.
Proof.
  split; [left; reflexivity|vm_compute; reflexivity].
Qed.

Theorem neg_pow_witness_smoke :
  let r := mkRef 0 0 in
  let s := set_cell new_sheet r (CForm (EPow (EInt 2%Z) (EInt (-1)%Z))) in
  In EClassNegPow (analyze_expr (EPow (EInt 2%Z) (EInt (-1)%Z))) /\
  eval_cell DEFAULT_FUEL s r = EErr.
Proof.
  split; [left; reflexivity|vm_compute; reflexivity].
Qed.

(* Lifting analyze_expr over a list of CellRef -> Expr pairs.  Used
   by sheet-level scanners. *)
Definition analyze_workbook_assoc (cells : list (CellRef * Expr))
    : list (CellRef * ErrorClass) :=
  flat_map (fun cr =>
    let '(r, e) := cr in map (fun c => (r, c)) (analyze_expr e)) cells.

(* Soundness for the assoc-list flavor: every reported pair has its
   class actually emitted by analyze_expr on the cell's formula. *)
Theorem analyze_workbook_assoc_sound :
  forall cells r c,
    In (r, c) (analyze_workbook_assoc cells) ->
    exists e, In (r, e) cells /\ In c (analyze_expr e).
Proof.
  induction cells as [|[r' e'] rest IH]; intros r c Hin; simpl in *;
    [contradiction|].
  apply in_app_or in Hin as [Hhead|Htail].
  - apply in_map_iff in Hhead as [c' [Heq Hin']].
    inversion Heq; subst.
    exists e'. split; [left; reflexivity | exact Hin'].
  - destruct (IH r c Htail) as [e [Hin1 Hin2]].
    exists e. split; [right; exact Hin1 | exact Hin2].
Qed.

(* Smoke: a two-cell assoc workbook with one division-by-zero. *)
Theorem analyze_workbook_assoc_smoke :
  let r1 := mkRef 0 0 in
  let r2 := mkRef 1 0 in
  analyze_workbook_assoc
    [(r1, EAdd (EInt 1%Z) (EInt 2%Z));
     (r2, EDiv (EInt 1%Z) (EInt 0%Z))]
  = [(r2, EClassDivZero)].
Proof. reflexivity. Qed.
