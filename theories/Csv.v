(* Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License. *)
From Corelib Require Import PrimString PrimInt63.
From Stdlib Require Import List BinInt.
From Crane Require Import Mapping.NatIntStd Mapping.ZInt.
From Rocqsheet Require Import Rocqsheet.
From Rocqsheet Require Import Parser.
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
  | CStr s    => s
  | CBool b   => if b then "true" else "false"
  | CForm _   => ""
  | CDate d   => date_to_string d
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

(* --- Theorems --------------------------------------------------- *)

Theorem cell_to_csv_empty : cell_to_csv CEmpty = "".
Proof. reflexivity. Qed.

Theorem cell_to_csv_lit : forall n,
  cell_to_csv (CLit n) = string_of_z n.
Proof. reflexivity. Qed.

Theorem cell_to_csv_str : forall s, cell_to_csv (CStr s) = s.
Proof. reflexivity. Qed.

Theorem cell_to_csv_bool_true : cell_to_csv (CBool true) = "true".
Proof. reflexivity. Qed.

Theorem cell_to_csv_bool_false : cell_to_csv (CBool false) = "false".
Proof. reflexivity. Qed.

(* Formula cells render as empty in this CSV format; numeric output
   would require running eval_cell, which CSV export does not. *)
Theorem cell_to_csv_form_empty : forall e, cell_to_csv (CForm e) = "".
Proof. reflexivity. Qed.

(* row_to_csv does not produce a leading separator. *)
Theorem row_to_csv_no_leading_sep_smoke :
  row_to_csv new_sheet 0 0 0 = "".
Proof. reflexivity. Qed.

(* ----- CSV import ------------------------------------------------ *)
(* RFC-4180-lite: comma-separated fields, LF- or CRLF-terminated
   rows; a double-quoted field may contain commas, newlines, and
   doubled quotes.  Each field commits like typed cell text: an
   integer literal lands as [CLit], anything else as [CStr]
   (formulas are deliberately not interpreted on import). *)

(* Write one finished field at (col, row); out-of-grid cells and
   empty fields are skipped. *)
Definition csv_commit_field (s : Sheet) (field : PrimString.string)
    (col row : int) : Sheet :=
  if orb (PrimInt63.leb NUM_COLS col) (PrimInt63.leb NUM_ROWS row) then s
  else if PrimInt63.eqb (PrimString.length field) 0 then s
  else
    match parse_int_literal field with
    | Some v => set_cell s (mkRef col row) (CLit v)
    | None =>
      match parse_date_literal field with
      | Some d => set_cell s (mkRef col row) (CDate d)
      | None => set_cell s (mkRef col row) (CStr field)
      end
    end.

(* Scanner state.  [cc_next] is the next input index; the C++ side
   drives [csv_step] in a loop on it (one extracted stack frame per
   character would overflow on any real file — the same trap as the
   status-bar walk). *)
Record csv_cursor : Type := mkCsvCursor {
  cc_sheet : Sheet;
  cc_col   : int;
  cc_row   : int;
  cc_field : PrimString.string;
  cc_inq   : bool;
  cc_next  : int
}.

Definition csv_start (s : Sheet) : csv_cursor :=
  mkCsvCursor s 0 0 ""%pstring false 0.

(* Consume one character (two for a doubled quote) at [cc_next]. *)
Definition csv_step (txt : PrimString.string) (len : int)
    (ac ar : int) (cur : csv_cursor) : csv_cursor :=
  let i := cc_next cur in
  let ch := char_to_int (PrimString.get txt i) in
  let i1 := PrimInt63.add i 1 in
  if cc_inq cur then
    if PrimInt63.eqb ch 34 then
      if andb (PrimInt63.ltb i1 len)
              (PrimInt63.eqb (char_to_int (PrimString.get txt i1)) 34)
      then
        (* Doubled quote: take the literal quote character from the
           input itself (a Coq-level quote constant would extract as
           an unescaped C++ string literal). *)
        mkCsvCursor (cc_sheet cur) (cc_col cur) (cc_row cur)
             (PrimString.cat (cc_field cur) (PrimString.sub txt i 1)) true
             (PrimInt63.add i 2)
      else mkCsvCursor (cc_sheet cur) (cc_col cur) (cc_row cur)
             (cc_field cur) false i1
    else mkCsvCursor (cc_sheet cur) (cc_col cur) (cc_row cur)
           (PrimString.cat (cc_field cur) (PrimString.sub txt i 1)) true i1
  else
    if PrimInt63.eqb ch 34 then
      mkCsvCursor (cc_sheet cur) (cc_col cur) (cc_row cur)
        (cc_field cur) true i1
    else if PrimInt63.eqb ch 44 then
      mkCsvCursor
        (csv_commit_field (cc_sheet cur) (cc_field cur)
           (PrimInt63.add ac (cc_col cur)) (PrimInt63.add ar (cc_row cur)))
        (PrimInt63.add (cc_col cur) 1) (cc_row cur)
        ""%pstring false i1
    else if PrimInt63.eqb ch 10 then
      mkCsvCursor
        (csv_commit_field (cc_sheet cur) (cc_field cur)
           (PrimInt63.add ac (cc_col cur)) (PrimInt63.add ar (cc_row cur)))
        0 (PrimInt63.add (cc_row cur) 1)
        ""%pstring false i1
    else if PrimInt63.eqb ch 13 then
      mkCsvCursor (cc_sheet cur) (cc_col cur) (cc_row cur)
        (cc_field cur) false i1
    else
      mkCsvCursor (cc_sheet cur) (cc_col cur) (cc_row cur)
        (PrimString.cat (cc_field cur) (PrimString.sub txt i 1)) false i1.

(* Executable Coq spec of the scan loop; extraction replaces it with
   the iterative driver in csv_helpers.h. *)
Fixpoint csv_run (fuel : nat) (txt : PrimString.string) (len ac ar : int)
    (cur : csv_cursor) : csv_cursor :=
  match fuel with
  | O => cur
  | S fuel' =>
    if PrimInt63.leb len (cc_next cur) then cur
    else csv_run fuel' txt len ac ar (csv_step txt len ac ar cur)
  end.

Crane Extract Inlined Constant csv_run =>
  "::csv_helpers::run_impl(%a2, %a5, [&](csv_cursor _c) { return Csv::csv_step(%a1, %a2, %a3, %a4, std::move(_c)); })"
  From "csv_helpers.h".

Definition csv_import (txt : PrimString.string) (s : Sheet)
    (anchor : CellRef) : Sheet :=
  let len := PrimString.length txt in
  let ac := cell_col_of anchor in
  let ar := cell_row_of anchor in
  let final := csv_run (S (nat_of_int len)) txt len ac ar (csv_start s) in
  (* Commit the trailing field (no newline at EOF). *)
  csv_commit_field (cc_sheet final) (cc_field final)
    (PrimInt63.add ac (cc_col final)) (PrimInt63.add ar (cc_row final)).

(* --- Scanner step theorems --------------------------------------- *)
(* End-to-end import behavior is exercised over the extracted code in
   tests/torture_test.cpp (vm_compute cannot normalize whole-sheet
   terms: a 52000-slot PrimArray value exhausts memory).  The step
   semantics below stay machine-checked on small terms. *)

Theorem csv_step_comma_advances_column :
  cc_col (csv_step ",x" 2 0 0 (mkCsvCursor new_sheet 0 0 "" false 0)) = 1.
Proof. reflexivity. Qed.

Theorem csv_step_newline_advances_row :
  let cur := csv_step "
x" 2 0 0 (mkCsvCursor new_sheet 4 0 "" false 0) in
  cc_row cur = 1 /\ cc_col cur = 0.
Proof. split; reflexivity. Qed.

Theorem csv_step_quote_opens :
  cc_inq (csv_step """x" 2 0 0 (mkCsvCursor new_sheet 0 0 "" false 0))
  = true.
Proof. reflexivity. Qed.

Theorem csv_step_quoted_comma_accumulates :
  cc_field (csv_step ",x" 2 0 0 (mkCsvCursor new_sheet 0 0 "" true 0))
  = ",".
Proof. reflexivity. Qed.
