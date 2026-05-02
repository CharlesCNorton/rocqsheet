(* Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License. *)
(* Column-scoped invariants discharged at commit time.  Each column
   carries an optional decidable predicate over the cell value; the
   discharge procedure returns [true] when the value satisfies the
   predicate (or no predicate is set), [false] otherwise.  Soundness
   theorem: a passing discharge implies the predicate holds. *)

From Stdlib Require Import List Bool BinInt.
From Corelib Require Import PrimInt63 Uint63Axioms.
From Crane Require Import Mapping.NatIntStd Mapping.ZInt.
From Rocqsheet Require Import Rocqsheet.
Import ListNotations.
Import Rocqsheet.

Open Scope int63.

Definition ColumnInvariant : Type :=
  PrimInt63.int -> option (Z -> bool).

Definition empty_invariant : ColumnInvariant := fun _ => None.

Definition put_invariant (ci : ColumnInvariant) (col : PrimInt63.int)
    (p : Z -> bool) : ColumnInvariant :=
  fun col' => if PrimInt63.eqb col col' then Some p else ci col'.

(* discharge ci col val: does the value satisfy the column's invariant? *)
Definition discharge (ci : ColumnInvariant) (col : PrimInt63.int) (val : Z)
    : bool :=
  match ci col with
  | None => true
  | Some pred => pred val
  end.

Theorem discharge_no_invariant : forall ci col val,
  ci col = None -> discharge ci col val = true.
Proof. intros ci col val H. unfold discharge. rewrite H. reflexivity. Qed.

Theorem discharge_sound : forall ci col val pred,
  ci col = Some pred ->
  discharge ci col val = pred val.
Proof. intros ci col val pred H. unfold discharge. rewrite H. reflexivity. Qed.

(* The headline soundness theorem: a passing discharge witnesses that
   the predicate holds at the value, no formula can [discharge = true]
   against a predicate that rejects its result. *)
Theorem discharge_passes_implies_predicate_holds :
  forall ci col val pred,
    ci col = Some pred ->
    discharge ci col val = true ->
    pred val = true.
Proof.
  intros ci col val pred Hci Hd.
  rewrite (discharge_sound _ _ _ _ Hci) in Hd. exact Hd.
Qed.

(* Conversely, a failing discharge witnesses predicate violation. *)
Theorem discharge_fails_implies_predicate_violated :
  forall ci col val pred,
    ci col = Some pred ->
    discharge ci col val = false ->
    pred val = false.
Proof.
  intros ci col val pred Hci Hd.
  rewrite (discharge_sound _ _ _ _ Hci) in Hd. exact Hd.
Qed.

(* put_invariant lookup:  same column returns the new predicate. *)
Lemma int_eqb_refl : forall n : PrimInt63.int, PrimInt63.eqb n n = true.
Proof.
  intro n. apply Uint63Axioms.eqb_refl.
Qed.

Theorem put_invariant_lookup_same : forall ci col p,
  put_invariant ci col p col = Some p.
Proof.
  intros. unfold put_invariant.
  rewrite int_eqb_refl. reflexivity.
Qed.

(* Different columns are unaffected. *)
Theorem put_invariant_lookup_other : forall ci col col' p,
  PrimInt63.eqb col col' = false ->
  put_invariant ci col p col' = ci col'.
Proof.
  intros. unfold put_invariant. rewrite H. reflexivity.
Qed.

(* Aggregate soundness: when discharge passes for every cell in a
   column, every cell's value satisfies the column's invariant. *)
Definition column_invariant_holds
    (ci : ColumnInvariant) (col : PrimInt63.int) (vals : list Z) : Prop :=
  forall v, In v vals ->
    match ci col with
    | None => True
    | Some pred => pred v = true
    end.

Theorem all_pass_implies_column_invariant :
  forall ci col vals,
    (forall v, In v vals -> discharge ci col v = true) ->
    column_invariant_holds ci col vals.
Proof.
  intros ci col vals Hall v Hin.
  pose proof (Hall v Hin) as Hd.
  unfold discharge in Hd.
  destruct (ci col) as [pred|] eqn:Hcol; [exact Hd|trivial].
Qed.
