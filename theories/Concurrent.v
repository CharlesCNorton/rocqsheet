(* Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License. *)
From Stdlib Require Import List Bool BinInt.
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
Proof. intros. unfold merge_logs. apply List.app_assoc. Qed.

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
