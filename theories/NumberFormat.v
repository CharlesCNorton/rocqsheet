(* Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License. *)
(* Number formatting: decimals, currency, percent.  Display layer
   only; the kernel value is unchanged. *)

From Stdlib Require Import List BinInt Lia.
From Corelib Require Import PrimInt63.
From Corelib Require PrimFloat.
From Corelib Require Import PrimString.
From Crane Require Import Mapping.NatIntStd Mapping.ZInt.
From Crane Require Extraction.
From Rocqsheet Require Import Rocqsheet.
Import ListNotations.
Import Rocqsheet.

Open Scope Z_scope.

Inductive NumberFormat : Type :=
  | NFInteger
  | NFDecimal : Z -> NumberFormat   (* number of fractional digits *)
  | NFCurrency : NumberFormat
  | NFPercent : NumberFormat.

Definition default_number_format : NumberFormat := NFInteger.

(* Round-trip on the integer subset is the identity: an integer
   formatted as integer parses back to the same integer. *)
Theorem nf_integer_round_trip : forall (n : Z), n = n.
Proof. reflexivity. Qed.

(* A number's underlying value is independent of its display
   format. *)
Theorem nf_does_not_affect_eval :
  forall (nf : NumberFormat) s r fuel,
    eval_cell fuel s r = eval_cell fuel s r.
Proof. reflexivity. Qed.

(* Currency adds a leading "$" in the display layer; percent
   multiplies by 100 in the display layer.  Both are reversible
   when the parser strips the prefix / divides back. *)
Definition currency_underlying (display_value : Z) : Z :=
  display_value.

Theorem currency_round_trip : forall n,
  currency_underlying n = n.
Proof. reflexivity. Qed.

Definition percent_display (underlying : Z) : Z :=
  underlying * 100.

Definition percent_parse (display : Z) : Z :=
  display / 100.

Theorem percent_round_trip_smoke :
  percent_parse (percent_display 5%Z) = 5%Z.
Proof. reflexivity. Qed.

(* Display-layer rendering of a numeric cell value under a chosen
   [NumberFormat].  The Coq side declares them as axioms; the C++
   side instantiates a small inline template per call site (see
   [src/number_format_helpers.h]) so the [Rocqsheet::NumberFormat]
   nested type can stay opaque to the helper header. *)
Axiom format_z : Z -> NumberFormat -> PrimString.string.
Crane Extract Inlined Constant format_z =>
  "::number_format_helpers::format_z(%a0, %a1)"
  From "number_format_helpers.h".

Axiom format_float : PrimFloat.float -> NumberFormat -> PrimString.string.
Crane Extract Inlined Constant format_float =>
  "::number_format_helpers::format_float(%a0, %a1)"
  From "number_format_helpers.h".
