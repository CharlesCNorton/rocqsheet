(* Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License. *)
(* Abstract dependency-graph propagation depth bound.

   Models the dirty-set propagation as iterated fan-out over a list of
   nodes, where each node yields at most [K] direct dependents.  After
   [N] steps the dirty set contains at most [|initial| * (K+1)^N]
   nodes.  Independent of [Sheet] / [PrimArray] so it compiles fast. *)

From Stdlib Require Import List Lia PeanoNat.
Import ListNotations.

Section AbstractPropagation.
  Variable Node : Type.
  Variable fanout : Node -> list Node.

  (* One propagation step: the new set is the original plus the
     concatenated fan-out of every current node.  Length-only model
     suffices for the depth bound. *)
  Definition step (cur : list Node) : list Node :=
    cur ++ flat_map fanout cur.

  Fixpoint iterate (cur : list Node) (n : nat) : list Node :=
    match n with
    | O => cur
    | S n' => iterate (step cur) n'
    end.

  (* Sparsity invariant: every node has at most [K] direct dependents. *)
  Definition sparsity_bound (K : nat) : Prop :=
    forall x, length (fanout x) <= K.

  Lemma length_flat_map_bounded : forall K xs,
    sparsity_bound K ->
    length (flat_map fanout xs) <= length xs * K.
  Proof.
    intros K xs Hbound. induction xs as [|x rest IH]; simpl; [lia|].
    rewrite length_app. pose proof (Hbound x). lia.
  Qed.

  Lemma length_step_bounded : forall K cur,
    sparsity_bound K ->
    length (step cur) <= length cur * S K.
  Proof.
    intros K cur Hbound. unfold step. rewrite length_app.
    pose proof (length_flat_map_bounded K cur Hbound). lia.
  Qed.

  Theorem iterate_length_bounded : forall K n cur,
    sparsity_bound K ->
    length (iterate cur n) <= length cur * Nat.pow (S K) n.
  Proof.
    induction n as [|n IH]; intros cur Hbound; simpl.
    - lia.
    - pose proof (IH (step cur) Hbound) as Hiter.
      pose proof (length_step_bounded K cur Hbound) as Hstep.
      eapply Nat.le_trans; [exact Hiter|].
      apply (Nat.mul_le_mono_r _ _ (Nat.pow (S K) n)) in Hstep.
      eapply Nat.le_trans; [exact Hstep|].
      lia.
  Qed.

  (* Single-step length bound, exposed as a standalone theorem. *)
  Theorem step_one_bounded : forall K cur,
    sparsity_bound K ->
    length (step cur) <= length cur + length cur * K.
  Proof.
    intros K cur Hbound. unfold step. rewrite length_app.
    pose proof (length_flat_map_bounded K cur Hbound). lia.
  Qed.
End AbstractPropagation.

(* Smoke: a fan-out of constant 0 dependents leaves the set unchanged
   in size after any number of steps. *)
Theorem propagation_no_fanout_smoke :
  forall (Node : Type) cur n,
    length (iterate Node (fun _ => []) cur n) = length cur.
Proof.
  intros Node cur n.
  induction n as [|n IH] in cur |- *; simpl; [reflexivity|].
  rewrite IH. unfold step. rewrite length_app.
  assert (Hflat : length (flat_map (fun _ : Node => @nil Node) cur) = 0).
  { induction cur; simpl; auto. }
  rewrite Hflat. lia.
Qed.

(* Smoke: under constant-singleton fan-out, each step exactly doubles
   the running length. *)
Lemma length_step_const_singleton :
  forall (Node : Type) (default : Node) (l : list Node),
    length (step Node (fun _ => [default]) l) = 2 * length l.
Proof.
  intros Node default l. unfold step. rewrite length_app.
  assert (Hf : length (flat_map (fun _ : Node => [default]) l) = length l).
  { induction l; simpl; auto. }
  rewrite Hf. lia.
Qed.

Lemma iterate_const_singleton_doubles :
  forall (Node : Type) (default : Node) (l : list Node) n,
    length (iterate Node (fun _ => [default]) l n) = length l * Nat.pow 2 n.
Proof.
  intros Node default l n. revert l.
  induction n as [|n IH]; intros l; simpl; [lia|].
  rewrite IH. rewrite length_step_const_singleton. lia.
Qed.

Theorem propagation_one_fanout_doubles_smoke :
  forall (Node : Type) (default : Node) n,
    length (iterate Node (fun _ => [default]) [default] n) = Nat.pow 2 n.
Proof.
  intros Node default n.
  rewrite (iterate_const_singleton_doubles Node default [default] n).
  simpl. lia.
Qed.
