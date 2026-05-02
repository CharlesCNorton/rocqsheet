(* Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License. *)
(* Sheet-level dependent typing: column [B] is constrained to have
   the same row count as column [A].  Modeled here over [list Z]
   with the length-equality invariant carried as a separate
   predicate.  Pure edit steps preserve the invariant by
   construction. *)

From Stdlib Require Import List BinInt Lia.
Import ListNotations.

Open Scope Z_scope.

Record TypedSheet : Type := mkTS
  { ts_anchor    : list Z
  ; ts_dependent : list Z }.

Definition well_typed (ts : TypedSheet) : Prop :=
  length (ts_anchor ts) = length (ts_dependent ts).

(* Pure edit operations that preserve the length-equality invariant. *)
Inductive pure_edit_step : TypedSheet -> TypedSheet -> Prop :=
  | PEAppendRow : forall ts a b,
      pure_edit_step ts
        (mkTS (a :: ts_anchor ts) (b :: ts_dependent ts))
  | PEReplaceAnchor : forall ts new_anchor,
      length new_anchor = length (ts_anchor ts) ->
      pure_edit_step ts (mkTS new_anchor (ts_dependent ts))
  | PEReplaceDependent : forall ts new_dep,
      length new_dep = length (ts_dependent ts) ->
      pure_edit_step ts (mkTS (ts_anchor ts) new_dep)
  | PEDropRow : forall ts a rest_a b rest_b,
      ts_anchor ts = a :: rest_a ->
      ts_dependent ts = b :: rest_b ->
      pure_edit_step ts (mkTS rest_a rest_b).

Theorem pure_edit_preserves_well_typed :
  forall ts ts',
    well_typed ts ->
    pure_edit_step ts ts' ->
    well_typed ts'.
Proof.
  intros ts ts' Hwt Hstep.
  destruct Hstep; unfold well_typed in *; simpl in *.
  - lia.
  - rewrite H. exact Hwt.
  - rewrite H. exact Hwt.
  - rewrite H, H0 in Hwt. simpl in Hwt. lia.
Qed.

(* Existence of a well-typed initial sheet. *)
Definition empty_typed_sheet : TypedSheet := mkTS [] [].

Theorem empty_typed_sheet_well_typed : well_typed empty_typed_sheet.
Proof. reflexivity. Qed.

(* A reflexive-transitive trace of pure edits preserves well-typing. *)
Inductive pure_edit_trace : TypedSheet -> TypedSheet -> Prop :=
  | PETraceRefl : forall ts, pure_edit_trace ts ts
  | PETraceStep : forall ts1 ts2 ts3,
      pure_edit_step ts1 ts2 ->
      pure_edit_trace ts2 ts3 ->
      pure_edit_trace ts1 ts3.

Theorem pure_edit_trace_preserves_well_typed :
  forall ts ts',
    well_typed ts ->
    pure_edit_trace ts ts' ->
    well_typed ts'.
Proof.
  intros ts ts' Hwt Htrace. induction Htrace; [exact Hwt|].
  apply IHHtrace. eapply pure_edit_preserves_well_typed; eauto.
Qed.

(* Whole-trace from the empty sheet: every reachable typed sheet is
   well-typed by construction. *)
Theorem reachable_from_empty_well_typed :
  forall ts,
    pure_edit_trace empty_typed_sheet ts ->
    well_typed ts.
Proof.
  intros ts Htrace.
  apply pure_edit_trace_preserves_well_typed with (ts := empty_typed_sheet);
    [apply empty_typed_sheet_well_typed | exact Htrace].
Qed.

(* Smoke: appending three rows from the empty sheet yields a 3-row
   well-typed sheet. *)
Theorem append_three_smoke :
  let ts0 := empty_typed_sheet in
  let ts1 := mkTS [1] [10] in
  let ts2 := mkTS [2; 1] [20; 10] in
  let ts3 := mkTS [3; 2; 1] [30; 20; 10] in
  pure_edit_step ts0 ts1 /\
  pure_edit_step ts1 ts2 /\
  pure_edit_step ts2 ts3 /\
  well_typed ts3.
Proof.
  split; [|split; [|split]].
  - apply (PEAppendRow empty_typed_sheet 1 10).
  - apply (PEAppendRow (mkTS [1] [10]) 2 20).
  - apply (PEAppendRow (mkTS [2; 1] [20; 10]) 3 30).
  - reflexivity.
Qed.
