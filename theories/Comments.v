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

(* A commented sheet bundles cells with a comment table.  Comments
   never affect evaluation; the sheet projection drops them. *)
Record CommentedSheet : Type := mkCSheet
  { cs_cells    : Sheet
  ; cs_comments : CommentMap }.

Definition cs_eval_cell (fuel : nat) (cs : CommentedSheet) (r : CellRef)
    : EvalResult :=
  eval_cell fuel (cs_cells cs) r.

Definition cs_with_comment (cs : CommentedSheet) (r : CellRef)
                           (c : PrimString.string) : CommentedSheet :=
  mkCSheet (cs_cells cs) (put_comment (cs_comments cs) r c).

(* Adding or changing a comment leaves the cell evaluation alone. *)
Theorem cs_with_comment_preserves_eval :
  forall fuel cs r c r',
    cs_eval_cell fuel (cs_with_comment cs r c) r'
    = cs_eval_cell fuel cs r'.
Proof. reflexivity. Qed.

(* Round-trip: putting and looking up a comment yields the same
   value, regardless of the underlying sheet. *)
Theorem cs_with_comment_lookup :
  forall cs r c,
    lookup_comment (cs_comments (cs_with_comment cs r c)) r = Some c.
Proof.
  intros. unfold cs_with_comment. simpl.
  apply put_then_lookup.
Qed.
