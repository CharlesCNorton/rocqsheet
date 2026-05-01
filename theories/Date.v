(* Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License. *)
From Stdlib Require Import BinInt Lia.

Open Scope Z_scope.

Definition Date : Type := Z.

Definition add_days (d : Date) (n : Z) : Date := d + n.

Definition sub_days (d1 d2 : Date) : Z := d1 - d2.

Definition weekday (d : Date) : Z := d mod 7.

Theorem add_days_zero : forall d, add_days d 0 = d.
Proof. intros. unfold add_days. lia. Qed.

Theorem sub_days_self : forall d, sub_days d d = 0.
Proof. intros. unfold sub_days. lia. Qed.

Theorem weekday_add_seven : forall d,
  weekday (add_days d 7) = weekday d.
Proof.
  intros. unfold weekday, add_days.
  rewrite Z.add_mod by lia.
  replace (7 mod 7) with 0 by reflexivity.
  rewrite Z.add_0_r.
  rewrite Z.mod_mod by lia.
  reflexivity.
Qed.

Theorem add_days_no_overflow_in_range :
  forall d n,
    -1000000 <= d <= 1000000 ->
    -1000000 <= n <= 1000000 ->
    -2000000 <= add_days d n <= 2000000.
Proof. intros. unfold add_days. lia. Qed.

(* A small date sublanguage with its own evaluator, parallel to
   the integer Expr.  The result type carries either a Date or a
   plain Z (for sub_days / weekday). *)

Inductive DateExpr : Type :=
  | DLit     : Date -> DateExpr
  | DAddDays : DateExpr -> Z -> DateExpr.

Inductive DiffExpr : Type :=
  | DSubDays : DateExpr -> DateExpr -> DiffExpr
  | DWeekday : DateExpr -> DiffExpr.

Fixpoint eval_date (e : DateExpr) : Date :=
  match e with
  | DLit d => d
  | DAddDays e' n => add_days (eval_date e') n
  end.

Definition eval_diff (e : DiffExpr) : Z :=
  match e with
  | DSubDays a b => sub_days (eval_date a) (eval_date b)
  | DWeekday a => weekday (eval_date a)
  end.

Theorem eval_add_days_zero : forall e,
  eval_date (DAddDays e 0) = eval_date e.
Proof. intros. simpl. apply add_days_zero. Qed.

Theorem eval_sub_days_self : forall e,
  eval_diff (DSubDays e e) = 0.
Proof. intros. simpl. apply sub_days_self. Qed.

Theorem eval_weekday_add_seven : forall e,
  eval_diff (DWeekday (DAddDays e 7)) = eval_diff (DWeekday e).
Proof. intros. simpl. apply weekday_add_seven. Qed.
