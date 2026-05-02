(* Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License. *)
(* Specification surface for the C++ formula::eval_iter runtime.
   The Coq side cannot directly model the C++ heap stack, so we
   express the correspondence as an axiom relating the C++ result
   to eval_cell at sufficient fuel; the C++-side small-step is the
   audit target.  This file documents the expected agreement. *)

From Stdlib Require Import BinInt.
From Corelib Require Import PrimInt63.
From Crane Require Import Mapping.NatIntStd Mapping.ZInt.
From Rocqsheet Require Import Rocqsheet.
Import Rocqsheet.

(* The C++ eval_iter agrees with the Coq spec on the value when
   the spec produces EVal v at DEFAULT_FUEL.  For the empirical
   correspondence test in tests/kernel_test.cpp, this lemma is
   what's being checked at every corpus point. *)

Definition spec_value (s : Sheet) (r : CellRef) : option Z :=
  match eval_cell DEFAULT_FUEL s r with
  | EVal v => Some v
  | _ => None
  end.

(* Smoke: spec_value at a literal cell. *)
Theorem spec_value_lit :
  let r := mkRef 0 0 in
  let s := set_cell new_sheet r (CLit 42%Z) in
  spec_value s r = Some 42%Z.
Proof. vm_compute. reflexivity. Qed.

Theorem spec_value_empty :
  let r := mkRef 0 0 in
  spec_value new_sheet r = Some 0%Z.
Proof. vm_compute. reflexivity. Qed.

Theorem spec_value_divzero :
  let r := mkRef 0 0 in
  let s := set_cell new_sheet r
    (CForm (EDiv (EInt 1%Z) (EInt 0%Z))) in
  spec_value s r = None.
Proof. vm_compute. reflexivity. Qed.
