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
