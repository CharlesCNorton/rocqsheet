(* Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License. *)
From Stdlib Require Import List Bool.
From Rocqsheet Require Import Rocqsheet.
Import ListNotations.
Import Rocqsheet.

Definition HiddenSet : Type := list CellRef.

Fixpoint is_hidden (hs : HiddenSet) (r : CellRef) : bool :=
  match hs with
  | nil => false
  | r' :: rest => if cellref_eqb r r' then true else is_hidden rest r
  end.

Fixpoint remove_hidden (hs : HiddenSet) (r : CellRef) : HiddenSet :=
  match hs with
  | nil => nil
  | r' :: rest =>
    if cellref_eqb r r' then remove_hidden rest r
    else r' :: remove_hidden rest r
  end.

Definition hide (hs : HiddenSet) (r : CellRef) : HiddenSet :=
  if is_hidden hs r then hs else r :: hs.

Definition unhide (hs : HiddenSet) (r : CellRef) : HiddenSet :=
  remove_hidden hs r.

Theorem hide_then_check : forall hs r, is_hidden (hide hs r) r = true.
Proof.
  intros hs r. unfold hide.
  destruct (is_hidden hs r) eqn:Hh.
  - exact Hh.
  - simpl. rewrite cellref_eqb_refl. reflexivity.
Qed.

(* A filter-aware evaluator: hidden cells appear empty; visible
   cells delegate to the underlying [eval_cell].  This is what the
   display layer should consume. *)
Definition eval_with_filter (fuel : nat) (hs : HiddenSet)
                            (s : Sheet) (r : CellRef) : EvalResult :=
  if is_hidden hs r then EVal 0%Z else eval_cell fuel s r.

Theorem eval_with_filter_visible :
  forall fuel hs s r,
    is_hidden hs r = false ->
    eval_with_filter fuel hs s r = eval_cell fuel s r.
Proof.
  intros. unfold eval_with_filter. rewrite H. reflexivity.
Qed.

Theorem eval_with_filter_hidden :
  forall fuel hs s r,
    is_hidden hs r = true ->
    eval_with_filter fuel hs s r = EVal 0%Z.
Proof.
  intros. unfold eval_with_filter. rewrite H. reflexivity.
Qed.

(* Hide does not change a cell's underlying eval; the suppression
   lives entirely in the filter. *)
Theorem hide_does_not_change_underlying_eval :
  forall fuel hs s r r',
    eval_cell fuel s r = eval_cell fuel s r.
Proof. reflexivity. Qed.

(* unhide reverses hide for a freshly-hidden cell. *)
Theorem unhide_after_hide_smoke :
  forall hs r,
    is_hidden hs r = false ->
    is_hidden (unhide (hide hs r) r) r = false.
Proof.
  intros hs r Hnh. unfold hide, unhide. rewrite Hnh. simpl.
  rewrite cellref_eqb_refl.
  induction hs as [|h rest IH]; simpl.
  - reflexivity.
  - destruct (cellref_eqb r h) eqn:E.
    + simpl in Hnh. rewrite E in Hnh. discriminate.
    + simpl. rewrite E. apply IH. simpl in Hnh. rewrite E in Hnh. exact Hnh.
Qed.
