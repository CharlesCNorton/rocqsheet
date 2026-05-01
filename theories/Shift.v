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
