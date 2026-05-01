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
  | EStr s => EStr s
  | EConcat a b => EConcat (replace_int_in_expr from to a) (replace_int_in_expr from to b)
  | ELen a => ELen (replace_int_in_expr from to a)
  | ESubstr a b c => ESubstr (replace_int_in_expr from to a)
                             (replace_int_in_expr from to b)
                             (replace_int_in_expr from to c)
  | EBool b => EBool b
  | EBNot a => EBNot (replace_int_in_expr from to a)
  | EBAnd a b => EBAnd (replace_int_in_expr from to a) (replace_int_in_expr from to b)
  | EBOr a b => EBOr (replace_int_in_expr from to a) (replace_int_in_expr from to b)
  | EMin tl br => EMin tl br
  | EMax tl br => EMax tl br
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
  - rewrite IHe1, IHe2, IHe3. reflexivity.
Qed.

Theorem replace_int_smoke :
  let e := EAdd (EInt 1%Z) (EMul (EInt 2%Z) (EInt 1%Z)) in
  replace_int_in_expr 1%Z 99%Z e =
    EAdd (EInt 99%Z) (EMul (EInt 2%Z) (EInt 99%Z)).
Proof. vm_compute. reflexivity. Qed.

(* Lift replace_int over an EvalResult: only EVal Z values are
   substituted; other shapes pass through. *)
Definition replace_int_in_result (from to : Z) (r : EvalResult)
    : EvalResult :=
  match r with
  | EVal n => EVal (if Z.eqb n from then to else n)
  | _ => r
  end.

(* Smoke: replace at a concrete EInt literal commutes through eval. *)
Theorem replace_eval_commute_lit_smoke :
  let s := new_sheet in
  let e := EInt 5%Z in
  eval_expr 2 nil s (replace_int_in_expr 5%Z 99%Z e)
  = replace_int_in_result 5%Z 99%Z (eval_expr 2 nil s e).
Proof. vm_compute. reflexivity. Qed.

(* Replacement is idempotent when from = to. *)
Theorem replace_int_idempotent_general :
  forall n e, replace_int_in_expr n n e = e.
Proof. exact replace_idempotent_when_equal. Qed.

(* No-match replacement leaves the tree unchanged. *)
Theorem replace_int_no_match_smoke :
  let e := EAdd (EInt 1%Z) (EInt 2%Z) in
  replace_int_in_expr 99%Z 7%Z e = EAdd (EInt 1%Z) (EInt 2%Z).
Proof. vm_compute. reflexivity. Qed.

(* Replacement distributes through eval at a closed compound input. *)
Theorem replace_eval_commute_compound_smoke :
  let e := EAdd (EInt 1%Z) (EMul (EInt 2%Z) (EInt 1%Z)) in
  eval_expr 5 nil new_sheet (replace_int_in_expr 1%Z 10%Z e)
  = EVal (Z.add 10%Z (Z.mul 2%Z 10%Z)).
Proof. vm_compute. reflexivity. Qed.
