(* Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License. *)
From Stdlib Require Import List Bool BinInt.
From Corelib Require Import PrimInt63.
From Crane Require Import Mapping.NatIntStd Mapping.ZInt.
From Rocqsheet Require Import Rocqsheet.
Import ListNotations.
Import Rocqsheet.

Open Scope int63.

(* True if expression [e] references cell [r] anywhere in its tree. *)
Fixpoint expr_references (r : CellRef) (e : Expr) : bool :=
  match e with
  | EInt _ => false
  | ERef r' => cellref_eqb r r'
  | EAdd a b | ESub a b | EMul a b | EDiv a b
  | EEq a b | ELt a b | EGt a b
  | EMod a b | EPow a b
  | EAnd a b | EOr a b
  | EIfErr a b
  | EFAdd a b | EFSub a b | EFMul a b | EFDiv a b
  | EConcat a b
  | EBAnd a b | EBOr a b =>
    orb (expr_references r a) (expr_references r b)
  | EIf a b c | ESubstr a b c =>
    orb (expr_references r a)
        (orb (expr_references r b) (expr_references r c))
  | ENot a | ELen a | EBNot a => expr_references r a
  | ESum tl br | EAvg tl br | ECount tl br
  | EMin tl br | EMax tl br =>
    orb (cellref_eqb r tl) (cellref_eqb r br)
  | EFloat _ | EStr _ | EBool _ => false
  end.

(* True if cell at [r'] in [s] is a formula that references [r]. *)
Definition cell_references (s : Sheet) (r : CellRef) (r' : CellRef) : bool :=
  match get_cell s r' with
  | CForm e => expr_references r e
  | _ => false
  end.

(* Direct-dependents: walk all cells in the sheet and collect those
   whose formula references [r]. *)
Fixpoint direct_dependents_aux (s : Sheet) (r : CellRef) (idx fuel : nat)
                                (acc : list CellRef) : list CellRef :=
  match fuel with
  | O => acc
  | S fuel' =>
    let r' := mkRef (PrimInt63.mod (Uint63.of_Z (Z.of_nat idx)) NUM_COLS)
                    (PrimInt63.div (Uint63.of_Z (Z.of_nat idx)) NUM_COLS) in
    let acc' := if cell_references s r r' then r' :: acc else acc in
    direct_dependents_aux s r (S idx) fuel' acc'
  end.

Definition direct_dependents (s : Sheet) (r : CellRef) : list CellRef :=
  direct_dependents_aux s r 0 60000 [].

(* DirtySet records cells that need re-evaluation. *)
Definition DirtySet : Type := list CellRef.

Fixpoint mem_dirty (xs : DirtySet) (r : CellRef) : bool :=
  match xs with
  | nil => false
  | y :: rest => orb (cellref_eqb r y) (mem_dirty rest r)
  end.

Definition mark_dirty (ds : DirtySet) (r : CellRef) : DirtySet :=
  if mem_dirty ds r then ds else r :: ds.

Definition clear_dirty : DirtySet := [].

(* When a cell at [r] changes, mark r and its direct dependents dirty. *)
Definition dirty_after_set (s : Sheet) (ds : DirtySet) (r : CellRef) : DirtySet :=
  fold_left mark_dirty (r :: direct_dependents s r) ds.

(* --- Theorems --------------------------------------------------- *)

Theorem mark_dirty_makes_dirty :
  forall ds r, mem_dirty (mark_dirty ds r) r = true.
Proof.
  intros ds r. unfold mark_dirty.
  destruct (mem_dirty ds r) eqn:Hm.
  - exact Hm.
  - simpl. rewrite cellref_eqb_refl. reflexivity.
Qed.

Theorem clean_after_eval :
  forall r, mem_dirty clear_dirty r = false.
Proof. reflexivity. Qed.

(* dirty_after_set marks the changed cell itself dirty. *)
Theorem set_marks_self_dirty :
  forall s ds r, mem_dirty (dirty_after_set s ds r) r = true.
Proof.
  intros s ds r. unfold dirty_after_set. simpl.
  generalize (direct_dependents s r) as deps.
  induction deps as [|d ds_rest IH] in ds |- *.
  - simpl. apply mark_dirty_makes_dirty.
  - simpl. apply IH.
Qed.

(* Smoke: a cell whose formula references A1 ends up in the
   direct_dependents of A1. *)
Theorem dependents_smoke :
  let r := mkRef 0 0 in
  let s := set_cell new_sheet (mkRef 1 0) (CForm (ERef r)) in
  In (mkRef 1 0) (direct_dependents s r).
Proof. vm_compute. left. reflexivity. Qed.
