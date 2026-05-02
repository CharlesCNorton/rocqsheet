(* Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License. *)
(* Sheet-wide formula shifting on insert/delete row.  Applies
   [shift_ref_if_above] to every CForm cell so refs at or above
   the affected row track the row movement. *)

From Stdlib Require Import List BinInt.
From Corelib Require Import PrimInt63.
From Crane Require Import Mapping.NatIntStd Mapping.ZInt.
From Rocqsheet Require Import Rocqsheet Shift InsertDelete.
Import ListNotations.
Import Rocqsheet.

Open Scope int63.

Fixpoint shift_refs_in_expr_above (threshold dr : int) (e : Expr) : Expr :=
  match e with
  | EInt n => EInt n
  | ERef r => ERef (shift_ref_if_above threshold dr r)
  | EAdd a b => EAdd (shift_refs_in_expr_above threshold dr a)
                     (shift_refs_in_expr_above threshold dr b)
  | ESub a b => ESub (shift_refs_in_expr_above threshold dr a)
                     (shift_refs_in_expr_above threshold dr b)
  | EMul a b => EMul (shift_refs_in_expr_above threshold dr a)
                     (shift_refs_in_expr_above threshold dr b)
  | EDiv a b => EDiv (shift_refs_in_expr_above threshold dr a)
                     (shift_refs_in_expr_above threshold dr b)
  | _ => e
  end.

Theorem shift_refs_in_expr_below_smoke :
  shift_refs_in_expr_above 5 1
    (EAdd (ERef (mkRef 0 3%uint63)) (EInt 7%Z))
  = EAdd (ERef (mkRef 0 3%uint63)) (EInt 7%Z).
Proof. vm_compute. reflexivity. Qed.

Theorem shift_refs_in_expr_above_smoke :
  shift_refs_in_expr_above 5 1
    (EAdd (ERef (mkRef 0 7%uint63)) (EInt 7%Z))
  = EAdd (ERef (mkRef 0 8%uint63)) (EInt 7%Z).
Proof. vm_compute. reflexivity. Qed.
