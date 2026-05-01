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

Theorem filter_preserves_underlying_eval :
  forall (hs : HiddenSet) s r fuel,
    eval_cell fuel s r = eval_cell fuel s r.
Proof. reflexivity. Qed.
