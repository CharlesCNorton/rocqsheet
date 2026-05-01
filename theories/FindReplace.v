(* Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License. *)
From Stdlib Require Import List BinInt.
From Crane Require Import Mapping.NatIntStd Mapping.ZInt.
From Rocqsheet Require Import Rocqsheet.
Import ListNotations.
Import Rocqsheet.

Fixpoint replace_int_in_expr (from to : Z) (e : Expr) : Expr :=
  match e with
  | EInt n => if Z.eqb n from then EInt to else EInt n
  | ERef r => ERef r
  | EAdd a b => EAdd (replace_int_in_expr from to a) (replace_int_in_expr from to b)
  | ESub a b => ESub (replace_int_in_expr from to a) (replace_int_in_expr from to b)
  | EMul a b => EMul (replace_int_in_expr from to a) (replace_int_in_expr from to b)
  | EDiv a b => EDiv (replace_int_in_expr from to a) (replace_int_in_expr from to b)
  | EEq a b => EEq (replace_int_in_expr from to a) (replace_int_in_expr from to b)
  | ELt a b => ELt (replace_int_in_expr from to a) (replace_int_in_expr from to b)
  | EGt a b => EGt (replace_int_in_expr from to a) (replace_int_in_expr from to b)
  | EIf c t f => EIf (replace_int_in_expr from to c)
                     (replace_int_in_expr from to t)
                     (replace_int_in_expr from to f)
  | EMod a b => EMod (replace_int_in_expr from to a) (replace_int_in_expr from to b)
  | EPow a b => EPow (replace_int_in_expr from to a) (replace_int_in_expr from to b)
  | ENot a => ENot (replace_int_in_expr from to a)
  | EAnd a b => EAnd (replace_int_in_expr from to a) (replace_int_in_expr from to b)
  | EOr a b => EOr (replace_int_in_expr from to a) (replace_int_in_expr from to b)
  | ESum tl br => ESum tl br
  | EAvg tl br => EAvg tl br
  | ECount tl br => ECount tl br
  | EIfErr a fb => EIfErr (replace_int_in_expr from to a) (replace_int_in_expr from to fb)
  | EFloat f => EFloat f
  | EFAdd a b => EFAdd (replace_int_in_expr from to a) (replace_int_in_expr from to b)
  | EFSub a b => EFSub (replace_int_in_expr from to a) (replace_int_in_expr from to b)
  | EFMul a b => EFMul (replace_int_in_expr from to a) (replace_int_in_expr from to b)
  | EFDiv a b => EFDiv (replace_int_in_expr from to a) (replace_int_in_expr from to b)
  end.

Theorem replace_idempotent_when_equal :
  forall n e, replace_int_in_expr n n e = e.
Proof.
  intros n e. induction e; simpl; try reflexivity;
    try (rewrite IHe1; rewrite IHe2; reflexivity);
    try (rewrite IHe; reflexivity).
  - destruct (Z.eqb z n) eqn:H.
    + apply Z.eqb_eq in H. subst. reflexivity.
    + reflexivity.
  - rewrite IHe1, IHe2, IHe3. reflexivity.
Qed.

Theorem replace_int_smoke :
  let e := EAdd (EInt 1%Z) (EMul (EInt 2%Z) (EInt 1%Z)) in
  replace_int_in_expr 1%Z 99%Z e =
    EAdd (EInt 99%Z) (EMul (EInt 2%Z) (EInt 99%Z)).
Proof. vm_compute. reflexivity. Qed.
