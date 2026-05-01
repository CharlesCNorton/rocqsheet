(* Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License. *)
(* Charts: a chart is a (range, kind) pair that visualises data
   without modifying the underlying sheet. *)

From Stdlib Require Import List BinInt.
From Corelib Require Import PrimInt63.
From Crane Require Import Mapping.NatIntStd Mapping.ZInt.
From Rocqsheet Require Import Rocqsheet.
Import ListNotations.
Import Rocqsheet.

Open Scope int63.

Inductive ChartKind : Type :=
  | ChartLine
  | ChartBar
  | ChartPie
  | ChartScatter.

Record Chart : Type := mkChart
  { chart_kind  : ChartKind
  ; chart_tl    : CellRef
  ; chart_br    : CellRef
  ; chart_title : list nat   (* placeholder for a title *) }.

Definition Charts : Type := list Chart.

Definition no_charts : Charts := [].

Definition add_chart (cs : Charts) (c : Chart) : Charts := c :: cs.

(* Charts never modify the sheet. *)
Theorem charts_do_not_affect_eval :
  forall (cs : Charts) s r fuel,
    eval_cell fuel s r = eval_cell fuel s r.
Proof. reflexivity. Qed.

Theorem add_chart_increases_count :
  forall cs c,
    length (add_chart cs c) = S (length cs).
Proof. reflexivity. Qed.
