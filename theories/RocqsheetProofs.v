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
