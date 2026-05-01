(* Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License. *)
From Corelib Require Import PrimString PrimInt63.
From Stdlib Require Import List BinInt.
From Crane Require Import Mapping.NatIntStd Mapping.ZInt.
From Rocqsheet Require Import Rocqsheet.
Import ListNotations.
Import Rocqsheet.

Local Open Scope pstring_scope.

Axiom string_of_z : Z -> PrimString.string.
Axiom newline : PrimString.string.
Definition comma_sep : PrimString.string := ",".

Definition cell_to_csv (c : Cell) : PrimString.string :=
  match c with
  | CEmpty    => ""
  | CLit n    => string_of_z n
  | CFloat _  => ""
  | CForm _   => ""
  end.

Fixpoint row_to_csv (s : Sheet) (row col : nat) (count : nat) : PrimString.string :=
  match count with
  | O => ""
  | S count' =>
    let r := mkRef (Uint63.of_Z (Z.of_nat col)) (Uint63.of_Z (Z.of_nat row)) in
    let v := cell_to_csv (get_cell s r) in
    let sep := if Nat.eqb col 0 then ""%pstring else comma_sep in
    PrimString.cat sep (PrimString.cat v (row_to_csv s row (S col) count'))
  end.

Fixpoint sheet_to_csv (s : Sheet) (row : nat) (count : nat)
                      (num_cols : nat) : PrimString.string :=
  match count with
  | O => ""
  | S count' =>
    PrimString.cat (row_to_csv s row 0 num_cols)
      (PrimString.cat newline
        (sheet_to_csv s (S row) count' num_cols))
  end.

Definition to_csv (s : Sheet) : PrimString.string :=
  sheet_to_csv s 0 200 260.
