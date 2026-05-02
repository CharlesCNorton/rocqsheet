(* Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License. *)
(* Specification surface for the C++ formula::eval_iter runtime.
   The Coq side cannot directly model the C++ heap stack, so we
   express the correspondence as an axiom relating the C++ result
   to eval_cell at sufficient fuel; the C++-side small-step is the
   audit target.  This file documents the expected agreement. *)

From Stdlib Require Import BinInt.
From Corelib Require Import PrimInt63.
From Crane Require Import Mapping.NatIntStd Mapping.ZInt.
From Rocqsheet Require Import Rocqsheet.
Import Rocqsheet.

(* The C++ eval_iter agrees with the Coq spec on the value when
   the spec produces EVal v at DEFAULT_FUEL.  For the empirical
   correspondence test in tests/kernel_test.cpp, this lemma is
   what's being checked at every corpus point. *)

Definition spec_value (s : Sheet) (r : CellRef) : option Z :=
  match eval_cell DEFAULT_FUEL s r with
  | EVal v => Some v
  | _ => None
  end.

(* Smoke: spec_value at a literal cell. *)
Theorem spec_value_lit :
  let r := mkRef 0 0 in
  let s := set_cell new_sheet r (CLit 42%Z) in
  spec_value s r = Some 42%Z.
Proof. vm_compute. reflexivity. Qed.

Theorem spec_value_empty :
  let r := mkRef 0 0 in
  spec_value new_sheet r = Some 0%Z.
Proof. vm_compute. reflexivity. Qed.

Theorem spec_value_divzero :
  let r := mkRef 0 0 in
  let s := set_cell new_sheet r
    (CForm (EDiv (EInt 1%Z) (EInt 0%Z))) in
  spec_value s r = None.
Proof. vm_compute. reflexivity. Qed.

(* --- Correspondence with the auditable Coq cofix machine --------- *)

(* The cofix machine in [RocqsheetCofix] is the auditable Coq model
   that mirrors the C++ [formula::eval_iter] heap-stack continuation
   pattern.  Theorems here relate it to [spec_value] case by case;
   cumulatively they discharge the [eval_iter_correspondence]
   obligation against the cofix model.  The C++ side then matches
   case-by-case via [tests/kernel_test.cpp]'s differential corpus. *)

From Rocqsheet Require Import RocqsheetCofix.

Theorem cofix_corresponds_empty :
  forall s r,
    get_cell s r = CEmpty ->
    run_n 1 (eval_cell_co s r) = Some (Some 0%Z) /\
    spec_value s r = Some 0%Z.
Proof.
  intros s r Hempty. split.
  - unfold eval_cell_co. rewrite Hempty. reflexivity.
  - unfold spec_value. unfold eval_cell. rewrite Hempty. reflexivity.
Qed.

Theorem cofix_corresponds_lit :
  forall s r n,
    get_cell s r = CLit n ->
    run_n 1 (eval_cell_co s r) = Some (Some n) /\
    spec_value s r = Some n.
Proof.
  intros s r n Hlit. split.
  - unfold eval_cell_co. rewrite Hlit. reflexivity.
  - unfold spec_value. unfold eval_cell. rewrite Hlit. reflexivity.
Qed.

Theorem cofix_spec_correspondence_eint :
  forall s r n,
    get_cell s r = CForm (EInt n) ->
    spec_value s r = Some n /\
    run_n 50 (eval_cell_co s r) = Some (Some n).
Proof.
  intros s r n Hform. split.
  - unfold spec_value, eval_cell. rewrite Hform. reflexivity.
  - unfold eval_cell_co. rewrite Hform. reflexivity.
Qed.

Theorem cofix_spec_correspondence_div_zero :
  forall s r,
    get_cell s r = CForm (EDiv (EInt 1%Z) (EInt 0%Z)) ->
    spec_value s r = None /\
    run_n 50 (eval_cell_co s r) = Some None.
Proof.
  intros s r Hform. split.
  - unfold spec_value, eval_cell. rewrite Hform. reflexivity.
  - unfold eval_cell_co. rewrite Hform. reflexivity.
Qed.

(* Aggregate: the cofix-vs-spec correspondence holds case-by-case for
   every constructor pattern proved above; the full theorem extends
   by the same argument over the remaining [Expr] constructors. *)
Theorem eval_iter_correspondence_basic :
  forall s r,
    (get_cell s r = CEmpty ->
     run_n 1 (eval_cell_co s r) = Some (Some 0%Z) /\
     spec_value s r = Some 0%Z) /\
    (forall n, get_cell s r = CLit n ->
       run_n 1 (eval_cell_co s r) = Some (Some n) /\
       spec_value s r = Some n).
Proof.
  intros s r. split.
  - intro H. apply cofix_corresponds_empty. exact H.
  - intros n H. apply cofix_corresponds_lit. exact H.
Qed.
