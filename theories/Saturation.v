(* Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License. *)
From Stdlib Require Import BinInt Lia Bool.

Open Scope Z_scope.

Definition INT64_MIN : Z := -9223372036854775808.
Definition INT64_MAX : Z :=  9223372036854775807.

Definition sat_add (a b : Z) : Z :=
  let r := a + b in
  if Z.ltb r INT64_MIN then INT64_MIN
  else if Z.ltb INT64_MAX r then INT64_MAX
  else r.

Definition sat_sub (a b : Z) : Z :=
  let r := a - b in
  if Z.ltb r INT64_MIN then INT64_MIN
  else if Z.ltb INT64_MAX r then INT64_MAX
  else r.

Definition sat_mul (a b : Z) : Z :=
  let r := a * b in
  if Z.ltb r INT64_MIN then INT64_MIN
  else if Z.ltb INT64_MAX r then INT64_MAX
  else r.

Definition div_guard (a b : Z) : Z :=
  if Z.eqb b 0 then 0
  else if Z.eqb a INT64_MIN && Z.eqb b (-1) then INT64_MIN
  else Z.div a b.

Definition mod_guard (a b : Z) : Z :=
  if Z.eqb b 0 then 0
  else if Z.eqb a INT64_MIN && Z.eqb b (-1) then 0
  else Z.modulo a b.

Theorem sat_add_correct : forall a b,
  (INT64_MIN <= a + b <= INT64_MAX -> sat_add a b = a + b) /\
  (a + b > INT64_MAX -> sat_add a b = INT64_MAX) /\
  (a + b < INT64_MIN -> sat_add a b = INT64_MIN).
Proof.
  intros a b. unfold sat_add.
  destruct (Z.ltb (a+b) INT64_MIN) eqn:H1.
  - apply Z.ltb_lt in H1.
    repeat split; intros; unfold INT64_MIN, INT64_MAX in *; lia.
  - apply Z.ltb_ge in H1.
    destruct (Z.ltb INT64_MAX (a+b)) eqn:H2.
    + apply Z.ltb_lt in H2.
      repeat split; intros; unfold INT64_MIN, INT64_MAX in *; lia.
    + apply Z.ltb_ge in H2.
      repeat split; intros; unfold INT64_MIN, INT64_MAX in *; lia.
Qed.

Theorem sat_sub_correct : forall a b,
  (INT64_MIN <= a - b <= INT64_MAX -> sat_sub a b = a - b) /\
  (a - b > INT64_MAX -> sat_sub a b = INT64_MAX) /\
  (a - b < INT64_MIN -> sat_sub a b = INT64_MIN).
Proof.
  intros a b. unfold sat_sub.
  destruct (Z.ltb (a-b) INT64_MIN) eqn:H1.
  - apply Z.ltb_lt in H1. repeat split; intros; unfold INT64_MIN, INT64_MAX in *; lia.
  - apply Z.ltb_ge in H1.
    destruct (Z.ltb INT64_MAX (a-b)) eqn:H2.
    + apply Z.ltb_lt in H2. repeat split; intros; unfold INT64_MIN, INT64_MAX in *; lia.
    + apply Z.ltb_ge in H2. repeat split; intros; unfold INT64_MIN, INT64_MAX in *; lia.
Qed.

Theorem sat_mul_correct : forall a b,
  (INT64_MIN <= a * b <= INT64_MAX -> sat_mul a b = a * b) /\
  (a * b > INT64_MAX -> sat_mul a b = INT64_MAX) /\
  (a * b < INT64_MIN -> sat_mul a b = INT64_MIN).
Proof.
  intros a b. unfold sat_mul.
  destruct (Z.ltb (a*b) INT64_MIN) eqn:H1.
  - apply Z.ltb_lt in H1. repeat split; intros; unfold INT64_MIN, INT64_MAX in *; lia.
  - apply Z.ltb_ge in H1.
    destruct (Z.ltb INT64_MAX (a*b)) eqn:H2.
    + apply Z.ltb_lt in H2. repeat split; intros; unfold INT64_MIN, INT64_MAX in *; lia.
    + apply Z.ltb_ge in H2. repeat split; intros; unfold INT64_MIN, INT64_MAX in *; lia.
Qed.

Theorem div_guard_zero : forall a, div_guard a 0 = 0.
Proof. intros. unfold div_guard. reflexivity. Qed.

Theorem div_guard_int_min : div_guard INT64_MIN (-1) = INT64_MIN.
Proof. unfold div_guard. reflexivity. Qed.

Theorem div_guard_normal : forall a b,
  b <> 0 ->
  ~(a = INT64_MIN /\ b = -1) ->
  div_guard a b = Z.div a b.
Proof.
  intros a b Hne Hno_min.
  unfold div_guard.
  destruct (Z.eqb b 0) eqn:H1.
  - apply Z.eqb_eq in H1. contradiction.
  - destruct (Z.eqb a INT64_MIN && Z.eqb b (-1)) eqn:H2.
    + apply andb_prop in H2 as [H2a H2b].
      apply Z.eqb_eq in H2a, H2b.
      exfalso. apply Hno_min. split; assumption.
    + reflexivity.
Qed.

Theorem mod_guard_zero : forall a, mod_guard a 0 = 0.
Proof. intros. unfold mod_guard. reflexivity. Qed.

Theorem mod_guard_int_min : mod_guard INT64_MIN (-1) = 0.
Proof. unfold mod_guard. reflexivity. Qed.
