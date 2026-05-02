(* Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License. *)
From Stdlib Require Import List Bool BinInt Lia Sorting.Permutation.
From Corelib Require Import PrimInt63.
From Crane Require Import Mapping.NatIntStd Mapping.ZInt.
From Rocqsheet Require Import Rocqsheet.
Import ListNotations.
Import Rocqsheet.

Open Scope int63.

(* An operation log is a sequence of timestamped writes.  The
   timestamp gives a total order across replicas; later wins.  This
   is the simplest CRDT (Last-Write-Wins register) lifted to a
   sheet of cells. *)

Definition Op : Type := Z * CellRef * Cell.    (* (timestamp, cell, value) *)
Definition OpLog : Type := list Op.

Definition op_ts (o : Op) : Z := let '(t, _, _) := o in t.
Definition op_ref (o : Op) : CellRef := let '(_, r, _) := o in r.
Definition op_val (o : Op) : Cell := let '(_, _, v) := o in v.

(* Merge two logs by concatenation. *)
Definition merge_logs (a b : OpLog) : OpLog := a ++ b.

(* Deliver a log into a sheet: apply each op in timestamp order; the
   highest-timestamp op for each cell wins. *)
Fixpoint apply_op_at (log : OpLog) (r : CellRef) (best_ts : Z) (best_val : Cell)
    : Cell :=
  match log with
  | nil => best_val
  | (t, r', v) :: rest =>
    if cellref_eqb r r' && Z.ltb best_ts t
    then apply_op_at rest r t v
    else apply_op_at rest r best_ts best_val
  end.

Definition deliver (log : OpLog) (r : CellRef) : Cell :=
  apply_op_at log r (-1)%Z CEmpty.

(* --- Theorems --------------------------------------------------- *)

(* Merging an empty log on either side is the identity. *)
Theorem merge_empty_l : forall log, merge_logs [] log = log.
Proof. reflexivity. Qed.

Theorem merge_empty_r : forall log, merge_logs log [] = log.
Proof. intros. unfold merge_logs. apply List.app_nil_r. Qed.

(* Associativity of merge. *)
Theorem merge_assoc :
  forall a b c,
    merge_logs (merge_logs a b) c = merge_logs a (merge_logs b c).
Proof. intros. unfold merge_logs. rewrite List.app_assoc. reflexivity. Qed.

(* Smoke: two replicas making concurrent writes; the higher
   timestamp wins. *)
Theorem lww_higher_ts_wins_smoke :
  let r := mkRef 0 0 in
  let log := [(2%Z, r, CLit 7%Z); (1%Z, r, CLit 99%Z)] in
  deliver log r = CLit 7%Z.
Proof. vm_compute. reflexivity. Qed.

(* Smoke: a write to a different cell does not affect the target
   cell's deliver. *)
Theorem lww_other_cell_unaffected_smoke :
  let r1 := mkRef 0 0 in
  let r2 := mkRef 1 0 in
  let log := [(1%Z, r1, CLit 5%Z); (2%Z, r2, CLit 6%Z)] in
  deliver log r1 = CLit 5%Z.
Proof. vm_compute. reflexivity. Qed.

(* Monotonicity of merge: appending a fresh op to either side does
   not lose any prior delivery, in the sense that the older op's
   value is still observable until a higher-timestamp op arrives. *)
Theorem merge_preserves_existing_smoke :
  let r := mkRef 0 0 in
  let log_a := [(1%Z, r, CLit 5%Z)] in
  let log_b := [(2%Z, mkRef 1 0, CLit 6%Z)] in
  deliver (merge_logs log_a log_b) r = CLit 5%Z.
Proof. vm_compute. reflexivity. Qed.

(* --- CRDT convergence: idempotence and observable commutativity ---- *)

(* Maximum timestamp for [r] in [log], using [low] as the initial
   threshold (returned when [r] never appears). *)
Fixpoint max_ts_for (log : OpLog) (r : CellRef) (low : Z) : Z :=
  match log with
  | nil => low
  | (t, r', _) :: rest =>
    if cellref_eqb r r' && Z.ltb low t
    then max_ts_for rest r t
    else max_ts_for rest r low
  end.

Lemma max_ts_for_lower : forall log r low,
  Z.le low (max_ts_for log r low).
Proof.
  induction log as [|[[t r'] v] rest IH]; intros r low; simpl; [lia|].
  destruct (cellref_eqb r r' && Z.ltb low t) eqn:Hcond.
  - apply Bool.andb_true_iff in Hcond as [_ Hlt].
    apply Z.ltb_lt in Hlt.
    pose proof (IH r t). lia.
  - apply IH.
Qed.

Lemma max_ts_for_dominates : forall log r low t v,
  In (t, r, v) log -> Z.le t (max_ts_for log r low).
Proof.
  induction log as [|[[t' r'] v'] rest IH];
    intros r low t v Hin; simpl in Hin; [contradiction|].
  destruct Hin as [Heq|Hin].
  - inversion Heq; subst. simpl.
    rewrite cellref_eqb_refl. simpl.
    destruct (Z.ltb low t) eqn:Hlt.
    + apply max_ts_for_lower.
    + apply Z.ltb_ge in Hlt.
      pose proof (max_ts_for_lower rest r low). lia.
  - simpl.
    destruct (cellref_eqb r r' && Z.ltb low t') eqn:Hcond.
    + eapply IH. exact Hin.
    + eapply IH. exact Hin.
Qed.

(* If no log entry for [r] strictly exceeds [best_ts], the fold leaves
   [best_val] alone. *)
Lemma apply_op_at_no_update :
  forall log r best_ts best_val,
    (forall t v, In (t, r, v) log -> Z.le t best_ts) ->
    apply_op_at log r best_ts best_val = best_val.
Proof.
  induction log as [|[[t r'] v] rest IH]; intros r best_ts best_val Hbound.
  - reflexivity.
  - simpl. destruct (cellref_eqb r r' && Z.ltb best_ts t) eqn:Hcond.
    + apply Bool.andb_true_iff in Hcond as [Hr Hlt].
      apply cellref_eqb_sound in Hr. subst r'.
      apply Z.ltb_lt in Hlt.
      specialize (Hbound t v (or_introl eq_refl)). lia.
    + apply IH. intros t' v' Hin'.
      apply (Hbound t' v'). right. exact Hin'.
Qed.

(* Splitting the fold across an [app] threads the running state
   through the join. *)
Lemma apply_op_at_app :
  forall l1 l2 r ts v,
    apply_op_at (l1 ++ l2) r ts v
    = apply_op_at l2 r
        (max_ts_for l1 r ts)
        (apply_op_at l1 r ts v).
Proof.
  induction l1 as [|[[t r'] v0] rest IH]; intros l2 r ts v; simpl.
  - reflexivity.
  - destruct (cellref_eqb r r' && Z.ltb ts t); apply IH.
Qed.

Theorem merge_idempotent : forall log r,
  deliver (merge_logs log log) r = deliver log r.
Proof.
  intros log r. unfold deliver, merge_logs.
  rewrite apply_op_at_app.
  apply apply_op_at_no_update.
  intros t v Hin.
  eapply max_ts_for_dominates. exact Hin.
Qed.

(* Two adjacent ops affecting different refs commute under [apply_op_at]. *)
Lemma apply_op_at_swap_diff_refs :
  forall log r best_ts best_val t1 r1 v1 t2 r2 v2,
    r1 <> r2 ->
    apply_op_at ((t1, r1, v1) :: (t2, r2, v2) :: log) r best_ts best_val
    = apply_op_at ((t2, r2, v2) :: (t1, r1, v1) :: log) r best_ts best_val.
Proof.
  intros log r best_ts best_val t1 r1 v1 t2 r2 v2 Hne.
  simpl.
  destruct (cellref_eqb r r1) eqn:Hr1, (cellref_eqb r r2) eqn:Hr2; simpl.
  - apply cellref_eqb_sound in Hr1, Hr2. subst. contradiction.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma cellref_eqb_sym : forall r1 r2,
  cellref_eqb r1 r2 = cellref_eqb r2 r1.
Proof.
  intros r1 r2.
  destruct (cellref_eqb r1 r2) eqn:H1, (cellref_eqb r2 r1) eqn:H2.
  - reflexivity.
  - apply cellref_eqb_sound in H1. subst.
    rewrite cellref_eqb_refl in H2. discriminate.
  - apply cellref_eqb_sound in H2. subst.
    rewrite cellref_eqb_refl in H1. discriminate.
  - reflexivity.
Qed.

(* Boolean predicate: does some op in [log] target reference [r]? *)
Definition ref_in_log (log : OpLog) (r : CellRef) : bool :=
  existsb (fun op => cellref_eqb (op_ref op) r) log.

Lemma ref_in_log_false_no_op : forall log r,
  ref_in_log log r = false ->
  forall op, In op log -> op_ref op <> r.
Proof.
  induction log as [|op rest IH]; intros r Hno op' Hin; simpl in *.
  - contradiction.
  - apply Bool.orb_false_iff in Hno as [Hop Hrest].
    destruct Hin as [Heq|Hin].
    + subst op'. intro Heqr.
      assert (Hrr : cellref_eqb (op_ref op) r = true).
      { apply cellref_eqb_sound. exact Heqr. }
      rewrite Hrr in Hop. discriminate.
    + apply (IH r Hrest op' Hin).
Qed.

Lemma apply_op_at_skip : forall log r best_ts best_val,
  ref_in_log log r = false ->
  apply_op_at log r best_ts best_val = best_val.
Proof.
  intros log r best_ts best_val Hskip.
  apply apply_op_at_no_update.
  intros t v Hin.
  exfalso.
  apply (ref_in_log_false_no_op log r Hskip (t, r, v) Hin). reflexivity.
Qed.

Lemma max_ts_for_skip : forall log r low,
  ref_in_log log r = false -> max_ts_for log r low = low.
Proof.
  induction log as [|[[t r'] v] rest IH]; intros r low Hskip; simpl in *.
  - reflexivity.
  - apply Bool.orb_false_iff in Hskip as [Hop Hrest].
    unfold op_ref in Hop. simpl in Hop.
    rewrite cellref_eqb_sym in Hop.
    rewrite Hop. simpl.
    apply IH. exact Hrest.
Qed.

Lemma disjoint_refs_at_most_one_touches :
  forall a b r,
    (forall op1 op2, In op1 a -> In op2 b -> op_ref op1 <> op_ref op2) ->
    ref_in_log a r = true ->
    ref_in_log b r = false.
Proof.
  intros a b r Hdis Ha.
  apply Bool.not_true_is_false. intro Hb.
  apply existsb_exists in Ha as [op1 [Hop1 Heq1]].
  apply existsb_exists in Hb as [op2 [Hop2 Heq2]].
  apply cellref_eqb_sound in Heq1, Heq2.
  apply (Hdis op1 op2 Hop1 Hop2).
  rewrite Heq1, Heq2. reflexivity.
Qed.

Theorem merge_commutative_disjoint_refs :
  forall a b r,
    (forall op1 op2, In op1 a -> In op2 b -> op_ref op1 <> op_ref op2) ->
    deliver (merge_logs a b) r = deliver (merge_logs b a) r.
Proof.
  intros a b r Hdis.
  unfold deliver, merge_logs.
  rewrite !apply_op_at_app.
  destruct (ref_in_log a r) eqn:Ha; destruct (ref_in_log b r) eqn:Hb.
  - pose proof (disjoint_refs_at_most_one_touches a b r Hdis Ha) as Hcontra.
    rewrite Hcontra in Hb. discriminate.
  - rewrite !(apply_op_at_skip b r _ _ Hb).
    rewrite (max_ts_for_skip b r _ Hb).
    reflexivity.
  - rewrite !(apply_op_at_skip a r _ _ Ha).
    rewrite (max_ts_for_skip a r _ Ha).
    reflexivity.
  - rewrite !(apply_op_at_skip a r _ _ Ha).
    rewrite !(apply_op_at_skip b r _ _ Hb).
    reflexivity.
Qed.
