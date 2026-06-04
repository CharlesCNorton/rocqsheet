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
  | ENot a | ELen a | EBNot a
  | EUpper a | ELower a | ETrim a => expr_references r a
  | EFind a b => orb (expr_references r a) (expr_references r b)
  | EReplaceS a b c d =>
    orb (orb (expr_references r a) (expr_references r b))
        (orb (expr_references r c) (expr_references r d))
  | EMedian tl br | EModeV tl br =>
    orb (cellref_eqb r tl) (cellref_eqb r br)
  | ERank x tl br | EPercentile x tl br | ENpvZ x tl br
  | EMatchV x tl br =>
    orb (expr_references r x)
        (orb (cellref_eqb r tl) (cellref_eqb r br))
  | EVLookup x tl br i | EHLookup x tl br i =>
    orb (orb (expr_references r x) (expr_references r i))
        (orb (cellref_eqb r tl) (cellref_eqb r br))
  | EIndex tl br a b =>
    orb (orb (expr_references r a) (expr_references r b))
        (orb (cellref_eqb r tl) (cellref_eqb r br))
  | EWeekdayF a => expr_references r a
  | EEdateF a b | EEomonthF a b =>
    orb (expr_references r a) (expr_references r b)
  | EDate3 a b c =>
    orb (expr_references r a)
        (orb (expr_references r b) (expr_references r c))
  | ESum tl br | EAvg tl br | ECount tl br
  | EMin tl br | EMax tl br
  | ECountN tl br | ECountA tl br
  | EVarSamp tl br | EVarPop tl br
  | EStdevSamp tl br | EStdevPop tl br =>
    orb (cellref_eqb r tl) (cellref_eqb r br)
  | ECountIf tl br _ _ =>
    orb (cellref_eqb r tl) (cellref_eqb r br)
  | ESumIf tl br _ _ sumtl | EAvgIf tl br _ _ sumtl =>
    orb (cellref_eqb r tl)
        (orb (cellref_eqb r br) (cellref_eqb r sumtl))
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

(* Folding more marks over the set never un-marks a member. *)
Lemma fold_mark_preserves :
  forall deps ds r,
    mem_dirty ds r = true ->
    mem_dirty (fold_left mark_dirty deps ds) r = true.
Proof.
  induction deps as [|d rest IH]; intros ds r Hin; simpl.
  - exact Hin.
  - apply IH. unfold mark_dirty.
    destruct (mem_dirty ds d); [exact Hin|].
    simpl. rewrite Hin. apply Bool.orb_true_r.
Qed.

(* The changed cell itself is marked, whatever the dependent list. *)
Lemma fold_mark_cons :
  forall deps ds r,
    mem_dirty (fold_left mark_dirty (r :: deps) ds) r = true.
Proof.
  intros deps ds r. simpl.
  apply fold_mark_preserves. apply mark_dirty_makes_dirty.
Qed.

(* dirty_after_set marks the changed cell itself dirty.  Proved by
   instantiating the abstract-list lemma: reducing here instead
   (simpl / cbn / vm) forces the 60000-fuel grid scan inside
   [direct_dependents] and either runs for an hour or overflows the
   stack at Qed. *)
Theorem set_marks_self_dirty :
  forall s ds r, mem_dirty (dirty_after_set s ds r) r = true.
Proof.
  intros s ds r.
  exact (fold_mark_cons (direct_dependents s r) ds r).
Qed.

(* Smoke: a cell whose formula references A1 is recognized as a
   dependent by the per-cell predicate.  (Stated over
   [cell_references] rather than [direct_dependents]: the latter is a
   whole-grid fold of this predicate, and normalizing 52000 cells
   under vm_compute takes the better part of an hour.) *)
Theorem dependents_smoke :
  let r := mkRef 0 0 in
  let s := set_cell new_sheet (mkRef 1 0) (CForm (ERef r)) in
  cell_references s r (mkRef 1 0) = true.
Proof. reflexivity. Qed.
