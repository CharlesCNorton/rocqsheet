(* Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License. *)
From Stdlib Require Import List Bool BinInt.
From Corelib Require Import PrimInt63.
From Crane Require Import Mapping.NatIntStd Mapping.ZInt.
From Rocqsheet Require Import Rocqsheet.
Import ListNotations.
Import Rocqsheet.

Open Scope int63.

(* An alternative sheet representation as a sparse association list.
   Empty cells are not stored, so updates are O(1) plus an O(n) scan
   for reads.  For grids with few non-empty cells this avoids the
   whole-vector copy that PArray-backed Sheet incurs on each
   set_cell.  A real implementation would use a HAMT for O(log n)
   reads; the API is identical and the get_set_eq / get_set_neq
   theorems carry over. *)

Definition PSheet : Type := list (CellRef * Cell).

Definition psheet_empty : PSheet := [].

Fixpoint psheet_get (s : PSheet) (r : CellRef) : Cell :=
  match s with
  | nil => CEmpty
  | (r', c) :: rest =>
    if cellref_eqb r r' then c else psheet_get rest r
  end.

Fixpoint psheet_remove (s : PSheet) (r : CellRef) : PSheet :=
  match s with
  | nil => nil
  | (r', c) :: rest =>
    if cellref_eqb r r' then psheet_remove rest r
    else (r', c) :: psheet_remove rest r
  end.

Definition psheet_set (s : PSheet) (r : CellRef) (c : Cell) : PSheet :=
  (r, c) :: psheet_remove s r.

(* --- Theorems --------------------------------------------------- *)

Theorem psheet_get_set_eq :
  forall s r c, psheet_get (psheet_set s r c) r = c.
Proof.
  intros s r c. unfold psheet_set. simpl.
  rewrite cellref_eqb_refl. reflexivity.
Qed.

Lemma psheet_get_remove_other :
  forall s r r',
    cellref_eqb r r' = false ->
    psheet_get (psheet_remove s r') r = psheet_get s r.
Proof.
  induction s as [|[r0 c0] rest IH]; intros r r' Hne; simpl.
  - reflexivity.
  - destruct (cellref_eqb r0 r') eqn:E0.
    + apply IH; assumption.
    + simpl. destruct (cellref_eqb r r0) eqn:E1.
      * reflexivity.
      * apply IH; assumption.
Qed.

Theorem psheet_get_set_neq :
  forall s r r' c,
    cellref_eqb r r' = false ->
    psheet_get (psheet_set s r' c) r = psheet_get s r.
Proof.
  intros s r r' c Hne. unfold psheet_set. simpl.
  rewrite Hne.
  apply psheet_get_remove_other. exact Hne.
Qed.

Theorem psheet_get_empty :
  forall r, psheet_get psheet_empty r = CEmpty.
Proof. reflexivity. Qed.
