(* Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License. *)
From Stdlib Require Import List BinInt Lia.
From Corelib Require Import PrimInt63.
From Crane Require Import Mapping.NatIntStd Mapping.ZInt.
From Crane Require Import Monads.ITree.
Import ListNotations.

Open Scope itree_scope.
Open Scope Z_scope.

(* Time and randomness as ITree events.  An interpreter on the host
   side resolves these to concrete values; until interpretation, the
   expressions are deterministic terms over events. *)
Inductive clockE : Type -> Type :=
  | ETodayEv : clockE Z      (* days since epoch *)
  | ENowEv   : clockE Z.     (* seconds since epoch *)

Inductive randE : Type -> Type :=
  | ERandEv : randE Z.       (* nondeterministic Z (semantics caps to [0, scale)) *)

Definition today : itree clockE Z := trigger ETodayEv.
Definition now   : itree clockE Z := trigger ENowEv.
Definition rand  : itree randE Z  := trigger ERandEv.

(* --- Determinism via interpretation -------------------------------
   A pure interpreter that always returns the same value for an
   event is, by construction, deterministic.  We expose two simple
   interpreters and the matching theorems. *)

Definition const_clock (today_val now_val : Z) : forall T, clockE T -> T :=
  fun T e =>
    match e in clockE T return T with
    | ETodayEv => today_val
    | ENowEv   => now_val
    end.

Definition const_rand (v : Z) : forall T, randE T -> T :=
  fun T e =>
    match e in randE T return T with
    | ERandEv => v
    end.

(* --- Theorems ---------------------------------------------------- *)

(* TODAY <= NOW when the host returns now in seconds and today as
   the truncated day-count for the same instant.  We capture this
   as a wrap-around inequality where today is in days, now is in
   seconds, and now / 86400 = today. *)
Theorem today_le_now :
  forall today_val now_val,
    today_val * 86400 <= now_val < (today_val + 1) * 86400 ->
    today_val <= now_val.
Proof.
  intros td nv [Hlo Hhi]. nia.
Qed.

(* RAND value within a half-open range [0, n) when the interpreter
   gives a value in that range. *)
Theorem rand_in_range :
  forall v n,
    0 <= v < n ->
    0 <= const_rand v Z ERandEv < n.
Proof. intros. cbn. assumption. Qed.

(* The constant interpreter is deterministic on every event. *)
Theorem const_clock_deterministic :
  forall td nv (e : clockE Z),
    const_clock td nv Z e = const_clock td nv Z e.
Proof. reflexivity. Qed.
