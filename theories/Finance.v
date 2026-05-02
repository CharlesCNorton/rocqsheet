(* Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License. *)
(* Verified financial primitives.

   Cash-flow arithmetic over [Z] (PV / NPV with integer-rate
   discounting).  Algebraic put-call parity defined to hold by
   construction over any commutative ring; the [Z]-instantiation
   yields a checkable identity.

   Black-Scholes Greeks would require a verified normal-CDF
   approximation.  This module captures the parity identity (which
   is independent of CDF) and a value-weighted [pv] / [npv] that the
   sheet kernel can extract directly. *)

From Stdlib Require Import List BinInt Lia.
Import ListNotations.

Open Scope Z_scope.

(* --- Discrete present value over a fixed integer rate ------------- *)

(* Inner accumulator: [d_pow] is the running discount factor
   ([d^i] for cashflow at index [i]).  Recurses with [d_pow * d]. *)
Fixpoint pv_aux (cashflows : list Z) (d_pow : Z) (d : Z) : Z :=
  match cashflows with
  | [] => 0
  | cf :: rest => cf * d_pow + pv_aux rest (d_pow * d) d
  end.

Definition pv (cashflows : list Z) (d : Z) : Z :=
  pv_aux cashflows 1 d.

Theorem pv_empty : forall d, pv [] d = 0.
Proof. reflexivity. Qed.

Theorem pv_singleton : forall cf d, pv [cf] d = cf.
Proof. intros. unfold pv. simpl. nia. Qed.

(* When the discount factor is 1, present value equals undiscounted
   sum of cashflows. *)
Lemma pv_aux_d_one : forall cf p,
  pv_aux cf p 1 = p * fold_right Z.add 0 cf.
Proof.
  induction cf as [|c rest IH]; intros p; simpl; [lia|].
  rewrite Z.mul_1_r. rewrite IH. lia.
Qed.

Theorem pv_d_one : forall cashflows,
  pv cashflows 1 = fold_right Z.add 0 cashflows.
Proof.
  intros. unfold pv. rewrite pv_aux_d_one. lia.
Qed.

(* --- NPV: initial investment is paid at t=0, cashflows at t>=1 --- *)
Definition npv (initial : Z) (cashflows : list Z) (d : Z) : Z :=
  Z.opp initial + pv cashflows d.

Theorem npv_zero_cashflows : forall i d, npv i [] d = - i.
Proof. intros. unfold npv, pv. simpl. lia. Qed.

Theorem npv_breakeven_d_one_smoke :
  npv 100 [50; 30; 20] 1 = 0.
Proof. reflexivity. Qed.

(* --- Algebraic put-call parity ----------------------------------- *)

(* C - P = S - K * disc, by definition of P from C. *)
Section ParityZ.
  Variables S K disc call : Z.

  Definition put_from_call : Z := call + K * disc - S.

  Theorem put_call_parity_z :
    call - put_from_call = S - K * disc.
  Proof. unfold put_from_call. lia. Qed.
End ParityZ.

(* --- Sanity: PV is linear in each cashflow position --------------- *)
Lemma pv_aux_linear_head : forall cf rest p d,
  pv_aux (cf :: rest) p d = cf * p + pv_aux rest (p * d) d.
Proof. reflexivity. Qed.

(* Doubling all cashflows doubles the PV. *)
Lemma pv_aux_scale : forall k cf p d,
  pv_aux (map (Z.mul k) cf) p d = k * pv_aux cf p d.
Proof.
  induction cf as [|c rest IH]; intros p d; simpl; [lia|].
  rewrite IH. lia.
Qed.

Theorem pv_scale : forall k cf d,
  pv (map (Z.mul k) cf) d = k * pv cf d.
Proof. intros. unfold pv. apply pv_aux_scale. Qed.

(* --- Smoke: NPV = 0 detects break-even at unit discount ----------- *)
Theorem npv_breakeven_decomposed_smoke :
  let initial := 100 in
  let cf := [50; 30; 20] in
  npv initial cf 1 = 0
  /\ pv cf 1 = initial.
Proof. split; reflexivity. Qed.
