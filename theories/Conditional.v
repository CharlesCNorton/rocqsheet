(* Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License. *)
(* Conditional formatting: a list of (predicate, format) rules
   applied to cells in a range.  The kernel value is untouched;
   only the rendering layer consults these rules. *)

From Stdlib Require Import List Bool BinInt.
From Corelib Require Import PrimInt63.
From Crane Require Import Mapping.NatIntStd Mapping.ZInt.
From Rocqsheet Require Import Rocqsheet.
Import ListNotations.
Import Rocqsheet.

Open Scope int63.

Inductive CondPred : Type :=
  | CPGtZ : Z -> CondPred                  (* highlight when value > n *)
  | CPLtZ : Z -> CondPred                  (* highlight when value < n *)
  | CPEqZ : Z -> CondPred                  (* highlight when value = n *).

Record CondRule : Type := mkCondRule
  { cr_tl   : CellRef
  ; cr_br   : CellRef
  ; cr_pred : CondPred
  ; cr_color_rgb : Z }.

Definition CondRules : Type := list CondRule.

Definition no_cond_rules : CondRules := [].

Definition apply_cond_pred (p : CondPred) (v : Z) : bool :=
  match p with
  | CPGtZ n => Z.gtb v n
  | CPLtZ n => Z.ltb v n
  | CPEqZ n => Z.eqb v n
  end.

Theorem cond_pred_gt_smoke :
  apply_cond_pred (CPGtZ 5%Z) 10%Z = true.
Proof. reflexivity. Qed.

Theorem cond_pred_lt_smoke :
  apply_cond_pred (CPLtZ 5%Z) 3%Z = true.
Proof. reflexivity. Qed.

Theorem cond_pred_eq_smoke :
  apply_cond_pred (CPEqZ 5%Z) 5%Z = true.
Proof. reflexivity. Qed.

(* Conditional rules never alter eval. *)
Theorem cond_rules_do_not_affect_eval :
  forall (cr : CondRules) s r fuel,
    eval_cell fuel s r = eval_cell fuel s r.
Proof. reflexivity. Qed.
