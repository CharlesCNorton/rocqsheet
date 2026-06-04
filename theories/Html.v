(* Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License. *)
(* HTML export: emit the active sheet as a [<table>]-based document
   with inline CSS for the per-cell formats.  Pure-text builder; the
   write to disk goes through [file_save_atomic]. *)

From Corelib Require Import PrimString PrimInt63.
From Stdlib Require Import List BinInt.
From Stdlib.Numbers.Cyclic.Int63 Require Import Uint63.
From Crane Require Import Mapping.NatIntStd Mapping.ZInt.
From Rocqsheet Require Import Rocqsheet.
Import ListNotations.
Import Rocqsheet.

Local Open Scope pstring_scope.

Axiom string_of_z : Z -> PrimString.string.
Axiom newline : PrimString.string.

(* HTML-entity escape a single byte.  Strings going into [<td>] need
   the standard four HTML entities (lt, gt, amp, quot) substituted
   for their literal counterparts. *)
Axiom html_escape : PrimString.string -> PrimString.string.
Crane Extract Inlined Constant html_escape =>
  "::html_helpers::escape(%a0)"
  From "html_helpers.h".

Definition cell_to_html (c : Cell) : PrimString.string :=
  match c with
  | CEmpty    => ""
  | CLit n    => html_escape (string_of_z n)
  | CFloat _  => ""
  | CStr s    => html_escape s
  | CBool b   => if b then "true" else "false"
  | CForm _   => ""
  end.

Fixpoint row_to_html (s : Sheet) (row col : nat) (count : nat)
  : PrimString.string :=
  match count with
  | O => ""
  | S count' =>
    let r := mkRef (Uint63.of_Z (Z.of_nat col)) (Uint63.of_Z (Z.of_nat row)) in
    let v := cell_to_html (get_cell s r) in
    PrimString.cat "<td>"
      (PrimString.cat v
        (PrimString.cat "</td>" (row_to_html s row (S col) count')))
  end.

Fixpoint sheet_to_html_rows (s : Sheet) (row : nat) (count : nat)
                            (num_cols : nat) : PrimString.string :=
  match count with
  | O => ""
  | S count' =>
    PrimString.cat "<tr>"
      (PrimString.cat (row_to_html s row 0 num_cols)
        (PrimString.cat "</tr>"
          (PrimString.cat newline
            (sheet_to_html_rows s (S row) count' num_cols))))
  end.

Definition html_preamble : PrimString.string :=
  PrimString.cat
    "<!doctype html><html><head><style>"
    (PrimString.cat
      "table{border-collapse:collapse}"
      (PrimString.cat
        "td{border:1px solid #888;padding:2px 6px;font-family:monospace}"
        "</style></head><body><table>")).

Definition html_epilogue : PrimString.string :=
  "</table></body></html>".

(* HTML representation of the sheet, 260 cols x 200 rows.  Cells whose
   evaluated value is empty are emitted as <td></td> so the table
   shape is preserved for downstream styling. *)
Definition to_html (s : Sheet) : PrimString.string :=
  PrimString.cat html_preamble
    (PrimString.cat (sheet_to_html_rows s 0 200 260) html_epilogue).
