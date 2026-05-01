(* Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License. *)
From Stdlib Require Import List BinInt Lia.
From Stdlib.Numbers.Cyclic.Int63 Require Import Uint63.
From Corelib Require Import PrimInt63 Uint63Axioms.
From Crane Require Import Mapping.NatIntStd Mapping.ZInt.
From Rocqsheet Require Import Rocqsheet.
Import ListNotations.
Import Rocqsheet.

Open Scope int63.

Definition shift_ref (dc dr : int) (r : CellRef) : CellRef :=
  mkRef (PrimInt63.add (ref_col r) dc) (PrimInt63.add (ref_row r) dr).

Fixpoint shift_refs (dc dr : int) (e : Expr) : Expr :=
  match e with
  | EInt n => EInt n
  | ERef r => ERef (shift_ref dc dr r)
  | EAdd a b => EAdd (shift_refs dc dr a) (shift_refs dc dr b)
  | ESub a b => ESub (shift_refs dc dr a) (shift_refs dc dr b)
  | EMul a b => EMul (shift_refs dc dr a) (shift_refs dc dr b)
  | EDiv a b => EDiv (shift_refs dc dr a) (shift_refs dc dr b)
  | EEq a b => EEq (shift_refs dc dr a) (shift_refs dc dr b)
  | ELt a b => ELt (shift_refs dc dr a) (shift_refs dc dr b)
  | EGt a b => EGt (shift_refs dc dr a) (shift_refs dc dr b)
  | EIf c t e => EIf (shift_refs dc dr c) (shift_refs dc dr t) (shift_refs dc dr e)
  | EMod a b => EMod (shift_refs dc dr a) (shift_refs dc dr b)
  | EPow a b => EPow (shift_refs dc dr a) (shift_refs dc dr b)
  | ENot a => ENot (shift_refs dc dr a)
  | EAnd a b => EAnd (shift_refs dc dr a) (shift_refs dc dr b)
  | EOr a b => EOr (shift_refs dc dr a) (shift_refs dc dr b)
  | ESum tl br => ESum (shift_ref dc dr tl) (shift_ref dc dr br)
  | EAvg tl br => EAvg (shift_ref dc dr tl) (shift_ref dc dr br)
  | ECount tl br => ECount (shift_ref dc dr tl) (shift_ref dc dr br)
  | EIfErr a fb => EIfErr (shift_refs dc dr a) (shift_refs dc dr fb)
  | EFloat f => EFloat f
  | EFAdd a b => EFAdd (shift_refs dc dr a) (shift_refs dc dr b)
  | EFSub a b => EFSub (shift_refs dc dr a) (shift_refs dc dr b)
  | EFMul a b => EFMul (shift_refs dc dr a) (shift_refs dc dr b)
  | EFDiv a b => EFDiv (shift_refs dc dr a) (shift_refs dc dr b)
  | EStr s => EStr s
  | EConcat a b => EConcat (shift_refs dc dr a) (shift_refs dc dr b)
  | ELen a => ELen (shift_refs dc dr a)
  | ESubstr a b c => ESubstr (shift_refs dc dr a) (shift_refs dc dr b) (shift_refs dc dr c)
  | EBool b => EBool b
  | EBNot a => EBNot (shift_refs dc dr a)
  | EBAnd a b => EBAnd (shift_refs dc dr a) (shift_refs dc dr b)
  | EBOr a b => EBOr (shift_refs dc dr a) (shift_refs dc dr b)
  | EMin tl br => EMin (shift_ref dc dr tl) (shift_ref dc dr br)
  | EMax tl br => EMax (shift_ref dc dr tl) (shift_ref dc dr br)
  end.

Theorem shift_ref_zero : forall r, shift_ref 0 0 r = r.
Proof.
  intros [c rw]. unfold shift_ref. simpl.
  assert (PrimInt63.add c 0 = c) as Hc.
  { apply to_Z_inj.
    rewrite add_spec.
    pose proof (to_Z_bounded c).
    assert (Uint63Axioms.to_Z 0 = 0%Z) by reflexivity.
    rewrite H0. rewrite Z.add_0_r.
    rewrite Z.mod_small; lia. }
  assert (PrimInt63.add rw 0 = rw) as Hr.
  { apply to_Z_inj.
    rewrite add_spec.
    pose proof (to_Z_bounded rw).
    assert (Uint63Axioms.to_Z 0 = 0%Z) by reflexivity.
    rewrite H0. rewrite Z.add_0_r.
    rewrite Z.mod_small; lia. }
  rewrite Hc, Hr. reflexivity.
Qed.

Theorem shift_refs_zero : forall e, shift_refs 0 0 e = e.
Proof.
  induction e; simpl;
    try rewrite IHe1; try rewrite IHe2; try rewrite IHe3;
    try rewrite IHe;
    try rewrite !shift_ref_zero;
    reflexivity.
Qed.

(* paste_at_offset is just shift_refs — copy then paste at the same
   location is the identity, paste preserves cell types because the
   transformation is over Expr only. *)
Theorem paste_at_origin_is_identity : forall e, shift_refs 0 0 e = e.
Proof. exact shift_refs_zero. Qed.

(* Smoke: composing two shifts at concrete deltas equals one shift
   by the sum. *)
Theorem shift_ref_compose_smoke :
  shift_ref 1 2 (shift_ref 3 4 (mkRef 5 6))
  = shift_ref (PrimInt63.add 1 3) (PrimInt63.add 2 4) (mkRef 5 6).
Proof. vm_compute. reflexivity. Qed.

(* Smoke: shifting an Expr tree composes through the structure. *)
Theorem shift_refs_compose_smoke :
  let e := EAdd (ERef (mkRef 1 2)) (ERef (mkRef 3 4)) in
  shift_refs 1 1 (shift_refs 2 2 e)
  = shift_refs (PrimInt63.add 1 2) (PrimInt63.add 1 2) e.
Proof. vm_compute. reflexivity. Qed.

(* Inverse: shift by (dc, dr) and then by (-dc, -dr) restores the
   original ref, smoke at concrete deltas. *)
Theorem shift_ref_inverse_smoke :
  shift_ref (PrimInt63.sub 0 3) (PrimInt63.sub 0 4)
            (shift_ref 3 4 (mkRef 10 20))
  = mkRef 10 20.
Proof. vm_compute. reflexivity. Qed.

(* --- Insert / delete row at the data level ----------------------- *)

Fixpoint insert_row_aux (fuel : nat) (src acc : Sheet)
                        (r idx : int) : Sheet :=
  match fuel with
  | O => acc
  | S fuel' =>
    if PrimInt63.leb GRID_SIZE idx then acc
    else
      let row := PrimInt63.div idx NUM_COLS in
      let col := PrimInt63.mod idx NUM_COLS in
      let new_cell :=
        if PrimInt63.ltb row r then PrimArray.get src idx
        else if PrimInt63.eqb row r then CEmpty
        else
          let src_idx := PrimInt63.add
                           (PrimInt63.mul (PrimInt63.sub row 1) NUM_COLS)
                           col in
          PrimArray.get src src_idx in
      insert_row_aux fuel' src (PrimArray.set acc idx new_cell)
                     r (PrimInt63.add idx 1)
  end.

Definition insert_row (s : Sheet) (r : int) : Sheet :=
  insert_row_aux 60000 s s r 0.

Fixpoint delete_row_aux (fuel : nat) (src acc : Sheet)
                        (r idx : int) : Sheet :=
  match fuel with
  | O => acc
  | S fuel' =>
    if PrimInt63.leb GRID_SIZE idx then acc
    else
      let row := PrimInt63.div idx NUM_COLS in
      let col := PrimInt63.mod idx NUM_COLS in
      let new_cell :=
        if PrimInt63.ltb row r then PrimArray.get src idx
        else if PrimInt63.eqb row (PrimInt63.sub NUM_ROWS 1) then CEmpty
        else
          let src_idx := PrimInt63.add
                           (PrimInt63.mul (PrimInt63.add row 1) NUM_COLS)
                           col in
          PrimArray.get src src_idx in
      delete_row_aux fuel' src (PrimArray.set acc idx new_cell)
                     r (PrimInt63.add idx 1)
  end.

Definition delete_row (s : Sheet) (r : int) : Sheet :=
  delete_row_aux 60000 s s r 0.

Theorem insert_row_preserves_below_smoke :
  let s := set_cell new_sheet (mkRef 0 0) (CLit 42%Z) in
  get_cell (insert_row s 5%uint63) (mkRef 0 0) = CLit 42%Z.
Proof. vm_compute. reflexivity. Qed.

Theorem insert_row_shifts_above_smoke :
  let s := set_cell new_sheet (mkRef 0 5%uint63) (CLit 7%Z) in
  get_cell (insert_row s 3%uint63) (mkRef 0 6%uint63) = CLit 7%Z.
Proof. vm_compute. reflexivity. Qed.

Theorem insert_row_at_r_is_empty_smoke :
  let s := set_cell new_sheet (mkRef 1 5%uint63) (CLit 99%Z) in
  get_cell (insert_row s 5%uint63) (mkRef 1 5%uint63) = CEmpty.
Proof. vm_compute. reflexivity. Qed.

Theorem delete_row_drops_r_smoke :
  let s := set_cell new_sheet (mkRef 0 5%uint63) (CLit 13%Z) in
  let s' := set_cell s (mkRef 0 6%uint63) (CLit 17%Z) in
  get_cell (delete_row s' 5%uint63) (mkRef 0 5%uint63) = CLit 17%Z.
Proof. vm_compute. reflexivity. Qed.

Theorem delete_row_preserves_below_smoke :
  let s := set_cell new_sheet (mkRef 0 2%uint63) (CLit 8%Z) in
  get_cell (delete_row s 5%uint63) (mkRef 0 2%uint63) = CLit 8%Z.
Proof. vm_compute. reflexivity. Qed.
