(* Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License. *)
(* Standalone proof file for derivable lemmas about [eval_expr] and
   the surrounding kernel.  Definitions live in Rocqsheet.v;
   theorems here build on top of it without re-extracting. *)

From Stdlib Require Import List BinInt Lia.
From Stdlib.Numbers.Cyclic.Int63 Require Import Uint63.
From Corelib Require Import PrimInt63 Uint63Axioms.
From Crane Require Import Mapping.NatIntStd Mapping.ZInt.
From Rocqsheet Require Import Rocqsheet.
Import ListNotations.
Import Rocqsheet.

Open Scope int63.

(* Adding zero on the right preserves the value. *)
Theorem eval_add_zero_r : forall a fuel visited s,
  eval_expr (S (S fuel)) visited s (EAdd (EInt a) (EInt 0%Z)) = EVal a.
Proof.
  intros. simpl. rewrite Z.add_0_r. reflexivity.
Qed.

(* Multiplication by one on the right preserves the value. *)
Theorem eval_mul_one_r : forall a fuel visited s,
  eval_expr (S (S fuel)) visited s (EMul (EInt a) (EInt 1%Z)) = EVal a.
Proof.
  intros. simpl. rewrite Z.mul_1_r. reflexivity.
Qed.

(* Subtracting itself yields zero. *)
Theorem eval_sub_self : forall a fuel visited s,
  eval_expr (S (S fuel)) visited s (ESub (EInt a) (EInt a)) = EVal 0%Z.
Proof.
  intros. simpl. rewrite Z.sub_diag. reflexivity.
Qed.

(* Empty cell evaluates to zero regardless of the formula context. *)
Theorem eval_cell_empty_is_zero : forall fuel s r,
  get_cell s r = CEmpty -> eval_cell fuel s r = EVal 0%Z.
Proof.
  intros fuel s r H. apply eval_empty. exact H.
Qed.

(* Adding identical operands doubles the result. *)
Theorem eval_add_self : forall a fuel visited s,
  eval_expr (S (S fuel)) visited s (EAdd (EInt a) (EInt a))
  = EVal (Z.add a a).
Proof. reflexivity. Qed.

(* Multiplying by zero yields zero. *)
Theorem eval_mul_zero_l_proof : forall a fuel visited s,
  eval_expr (S (S fuel)) visited s (EMul (EInt 0%Z) (EInt a)) = EVal 0%Z.
Proof. reflexivity. Qed.

Theorem eval_mul_zero_r_proof : forall a fuel visited s,
  eval_expr (S (S fuel)) visited s (EMul (EInt a) (EInt 0%Z)) = EVal 0%Z.
Proof.
  intros. simpl. rewrite Z.mul_0_r. reflexivity.
Qed.

(* Sub then add the same value recovers the original. *)
Theorem eval_sub_add_cancel : forall a b fuel visited s,
  eval_expr (S (S (S fuel))) visited s
    (EAdd (ESub (EInt a) (EInt b)) (EInt b))
  = EVal a.
Proof.
  intros. simpl. f_equal. lia.
Qed.

(* IF on a positive literal takes the then-branch. *)
Theorem eval_if_pos_lit_smoke :
  let s := new_sheet in
  eval_expr 5 nil s (EIf (EInt 7%Z) (EInt 1%Z) (EInt 2%Z)) = EVal 1%Z.
Proof. vm_compute. reflexivity. Qed.

(* IF on a negative literal takes the then-branch. *)
Theorem eval_if_neg_lit_smoke :
  let s := new_sheet in
  eval_expr 5 nil s (EIf (EInt (-3)%Z) (EInt 1%Z) (EInt 2%Z)) = EVal 1%Z.
Proof. vm_compute. reflexivity. Qed.

(* IF on zero takes the else-branch. *)
Theorem eval_if_zero_lit_smoke :
  let s := new_sheet in
  eval_expr 5 nil s (EIf (EInt 0%Z) (EInt 1%Z) (EInt 2%Z)) = EVal 2%Z.
Proof. vm_compute. reflexivity. Qed.
