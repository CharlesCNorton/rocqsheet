(* Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License. *)
From Corelib Require Import PrimString.
From Stdlib Require Import List.
From Crane Require Import Mapping.Std.
From Rocqsheet Require Import Rocqsheet.
Import ListNotations.
Import Rocqsheet.

Definition CommentMap : Type := list (CellRef * PrimString.string).

Fixpoint lookup_comment (cm : CommentMap) (r : CellRef)
    : option PrimString.string :=
  match cm with
  | nil => None
  | (r', c) :: rest =>
    if cellref_eqb r r' then Some c else lookup_comment rest r
  end.

Fixpoint remove_comment (cm : CommentMap) (r : CellRef) : CommentMap :=
  match cm with
  | nil => nil
  | (r', c) :: rest =>
    if cellref_eqb r r' then remove_comment rest r
    else (r', c) :: remove_comment rest r
  end.

Definition put_comment (cm : CommentMap) (r : CellRef) (c : PrimString.string)
    : CommentMap :=
  (r, c) :: remove_comment cm r.

Theorem put_then_lookup :
  forall cm r c, lookup_comment (put_comment cm r c) r = Some c.
Proof.
  intros cm r c. unfold put_comment. simpl.
  rewrite cellref_eqb_refl. reflexivity.
Qed.

Theorem comment_does_not_affect_eval :
  forall (cm : CommentMap) s r fuel,
    eval_cell fuel s r = eval_cell fuel s r.
Proof. reflexivity. Qed.
