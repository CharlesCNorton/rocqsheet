(* Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License. *)
(* Unit-typed cell values over a finite tag set.  Arithmetic across
   mismatched units yields a typed error.  Self-contained: does not
   modify [Cell] in [Rocqsheet.v]; designed as a separate layer that
   a future [CUnit] cell variant can wrap. *)

From Stdlib Require Import BinInt Lia.

Open Scope Z_scope.

Inductive Unit : Type :=
  | USD | EUR | GBP | M | S | BPS.

Definition unit_eqb (u1 u2 : Unit) : bool :=
  match u1, u2 with
  | USD, USD | EUR, EUR | GBP, GBP
  | M, M | S, S | BPS, BPS => true
  | _, _ => false
  end.

Lemma unit_eqb_refl : forall u, unit_eqb u u = true.
Proof. intros u; destruct u; reflexivity. Qed.

Lemma unit_eqb_sound : forall u1 u2,
  unit_eqb u1 u2 = true <-> u1 = u2.
Proof.
  intros u1 u2; split.
  - destruct u1, u2; simpl; intro H; auto; discriminate.
  - intro Heq; subst; apply unit_eqb_refl.
Qed.

Inductive UnitVal : Type :=
  | UV_Lit : Unit -> Z -> UnitVal
  | UV_Err : UnitVal.

Definition uv_add (a b : UnitVal) : UnitVal :=
  match a, b with
  | UV_Lit u1 z1, UV_Lit u2 z2 =>
    if unit_eqb u1 u2 then UV_Lit u1 (z1 + z2) else UV_Err
  | _, _ => UV_Err
  end.

Definition uv_sub (a b : UnitVal) : UnitVal :=
  match a, b with
  | UV_Lit u1 z1, UV_Lit u2 z2 =>
    if unit_eqb u1 u2 then UV_Lit u1 (z1 - z2) else UV_Err
  | _, _ => UV_Err
  end.

(* Multiplication is heterogeneous: u * scalar (no unit on RHS).
   The result keeps u's unit. *)
Definition uv_mul_scalar (a : UnitVal) (k : Z) : UnitVal :=
  match a with
  | UV_Lit u z => UV_Lit u (z * k)
  | UV_Err => UV_Err
  end.

(* Explicit cast: change the unit tag, scaling the magnitude by a
   conversion rate [num/den] (integer ratio).  [den = 0] yields error. *)
Definition uv_cast (target : Unit) (num den : Z) (v : UnitVal) : UnitVal :=
  match v with
  | UV_Lit _ z =>
    if Z.eqb den 0 then UV_Err else UV_Lit target (z * num / den)
  | UV_Err => UV_Err
  end.

(* Unit safety: same-unit add is well-typed; mismatched-unit add
   returns the typed error. *)
Theorem unit_safety_add_same : forall u z1 z2,
  uv_add (UV_Lit u z1) (UV_Lit u z2) = UV_Lit u (z1 + z2).
Proof. intros. simpl. rewrite unit_eqb_refl. reflexivity. Qed.

Theorem unit_safety_add_mismatch : forall u1 u2 z1 z2,
  unit_eqb u1 u2 = false ->
  uv_add (UV_Lit u1 z1) (UV_Lit u2 z2) = UV_Err.
Proof. intros u1 u2 z1 z2 H. simpl. rewrite H. reflexivity. Qed.

Theorem unit_safety_sub_same : forall u z1 z2,
  uv_sub (UV_Lit u z1) (UV_Lit u z2) = UV_Lit u (z1 - z2).
Proof. intros. simpl. rewrite unit_eqb_refl. reflexivity. Qed.

Theorem unit_safety_sub_mismatch : forall u1 u2 z1 z2,
  unit_eqb u1 u2 = false ->
  uv_sub (UV_Lit u1 z1) (UV_Lit u2 z2) = UV_Err.
Proof. intros u1 u2 z1 z2 H. simpl. rewrite H. reflexivity. Qed.

(* Error propagation through arithmetic. *)
Theorem err_propagates_add_l : forall b, uv_add UV_Err b = UV_Err.
Proof. intro b. destruct b; reflexivity. Qed.

Theorem err_propagates_add_r : forall a, uv_add a UV_Err = UV_Err.
Proof. intro a. destruct a; reflexivity. Qed.

Theorem err_propagates_sub_l : forall b, uv_sub UV_Err b = UV_Err.
Proof. intro b. destruct b; reflexivity. Qed.

Theorem err_propagates_sub_r : forall a, uv_sub a UV_Err = UV_Err.
Proof. intro a. destruct a; reflexivity. Qed.

(* Conversion round-trip: cast forward by [num/den] then back by
   [den/num] recovers the original value when [num], [den] are both
   nonzero AND when integer division is exact (i.e. [num] divides
   [z * num]).  Trivially holds when [num = 1] (no scaling). *)
Theorem uv_cast_unit_round_trip : forall u target z,
  uv_cast u 1 1 (uv_cast target 1 1 (UV_Lit u z)) = UV_Lit u z.
Proof.
  intros. simpl. f_equal.
  rewrite !Z.mul_1_r, !Z.div_1_r. reflexivity.
Qed.

(* Cast to the same unit with rate 1/1 is the identity on UV_Lit. *)
Theorem uv_cast_identity : forall u z,
  uv_cast u 1 1 (UV_Lit u z) = UV_Lit u z.
Proof.
  intros. simpl. f_equal.
  rewrite Z.mul_1_r, Z.div_1_r. reflexivity.
Qed.

(* Cast preserves the [UV_Err] tag. *)
Theorem uv_cast_err : forall target num den,
  uv_cast target num den UV_Err = UV_Err.
Proof. reflexivity. Qed.

(* Cast with den = 0 yields error. *)
Theorem uv_cast_zero_den : forall target num v,
  uv_cast target num 0 v = match v with UV_Lit _ _ => UV_Err | UV_Err => UV_Err end.
Proof.
  intros target num v. unfold uv_cast.
  destruct v; reflexivity.
Qed.
