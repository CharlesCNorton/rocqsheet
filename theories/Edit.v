(* Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License. *)
(* Pure editing operators on [loop_state]: commit, undo/redo/clear,
   sheet-switch, row insert/delete/swap, find/replace, merge. *)

From Corelib Require Import PrimString PrimInt63.
From Stdlib Require Import List BinInt.
From Stdlib.Numbers.Cyclic.Int63 Require Import Uint63.
From Crane Require Extraction.
From Crane Require Import Mapping.NatIntStd Mapping.ZInt.
From Rocqsheet Require Import Rocqsheet.
From Rocqsheet Require Import Parser.
From Rocqsheet Require Import Formatting.
From Rocqsheet Require Import NumberFormat.
From Rocqsheet Require Import Charts.
From Rocqsheet Require Import Merges.
From Rocqsheet Require Import FindReplace.
From Rocqsheet Require Import InsertDelete.
From Rocqsheet Require Import Sorting.
From Rocqsheet Require Import Shift.
From Rocqsheet Require Import State.
Import ListNotations.
Import Rocqsheet.

Open Scope int63_scope.
Local Open Scope pstring_scope.

(* Inspect leading character.  Empty string returns 0. *)
Definition first_char_int (s : PrimString.string) : int :=
  if PrimInt63.ltb 0 (PrimString.length s)
  then char_to_int (PrimString.get s 0)
  else 0.

(* Skip the leading '=' (and any whitespace before it).  Used to feed
   the formula portion of "=A1+B1" into [parse_formula]. *)
Definition strip_leading_eq (s : PrimString.string) : PrimString.string :=
  let len := PrimString.length s in
  let fix find_start (fuel : nat) (i : int) : int :=
    match fuel with
    | O => i
    | S fuel' =>
      if PrimInt63.ltb i len then
        let c := char_to_int (PrimString.get s i) in
        if PrimInt63.eqb c 32 then find_start fuel' (PrimInt63.add i 1)
        else if PrimInt63.eqb c 61 then PrimInt63.add i 1
        else i
      else i
    end in
  let start := find_start (S (nat_of_int len)) 0 in
  PrimString.sub s start (PrimInt63.sub len start).

Fixpoint all_ws_aux (fuel : nat) (s : PrimString.string) (len i : int) : bool :=
  match fuel with
  | O => true
  | S fuel' =>
    if PrimInt63.ltb i len then
      if is_space (PrimString.get s i)
      then all_ws_aux fuel' s len (PrimInt63.add i 1)
      else false
    else true
  end.

Definition all_whitespace (s : PrimString.string) : bool :=
  let len := PrimString.length s in
  all_ws_aux (S (nat_of_int len)) s len 0.

Definition starts_with_eq (s : PrimString.string) : bool :=
  let len := PrimString.length s in
  let fix find_first (fuel : nat) (i : int) : bool :=
    match fuel with
    | O => false
    | S fuel' =>
      if PrimInt63.ltb i len then
        let c := char_to_int (PrimString.get s i) in
        if PrimInt63.eqb c 32 then find_first fuel' (PrimInt63.add i 1)
        else PrimInt63.eqb c 61
      else false
    end in
  find_first (S (nat_of_int len)) 0.

(* Commit the current formula bar text to the selected cell. *)
Definition commit_to (ls : loop_state) (r : CellRef) (txt : PrimString.string)
  : loop_state :=
  let before := ls_sheet ls in
  if all_whitespace txt then
    let new_sheet := set_cell before r CEmpty in
    let new_eb := remove_edit (ls_edit_buf ls) r in
    let new_pe := remove_ref (ls_parse_errs ls) r in
    mkLoop new_sheet (ls_selected ls) (ls_fbar_text ls)
           new_eb new_pe (trim_undo ((before, "edit cell"%pstring) :: ls_undo ls)) nil (ls_formats ls)
           (ls_other_sheets ls) (ls_active ls) (ls_charts ls)
           (ls_merges ls) (ls_sheet_names ls)
  else if starts_with_eq txt then
    let body := strip_leading_eq txt in
    match parse_formula body with
    | Some e =>
      let new_sheet := set_cell before r (CForm e) in
      let new_eb := put_edit (ls_edit_buf ls) r txt in
      let new_pe := remove_ref (ls_parse_errs ls) r in
      mkLoop new_sheet (ls_selected ls) (ls_fbar_text ls)
             new_eb new_pe (trim_undo ((before, "edit cell"%pstring) :: ls_undo ls)) nil (ls_formats ls)
             (ls_other_sheets ls) (ls_active ls) (ls_charts ls)
             (ls_merges ls) (ls_sheet_names ls)
    | None =>
      let new_eb := put_edit (ls_edit_buf ls) r txt in
      let new_pe := add_ref (ls_parse_errs ls) r in
      mkLoop before (ls_selected ls) (ls_fbar_text ls)
             new_eb new_pe (ls_undo ls) (ls_redo ls) (ls_formats ls)
             (ls_other_sheets ls) (ls_active ls) (ls_charts ls)
             (ls_merges ls) (ls_sheet_names ls)
    end
  else
    match parse_int_literal txt with
    | Some v =>
      let new_sheet := set_cell before r (CLit v) in
      let new_eb := put_edit (ls_edit_buf ls) r txt in
      let new_pe := remove_ref (ls_parse_errs ls) r in
      mkLoop new_sheet (ls_selected ls) (ls_fbar_text ls)
             new_eb new_pe (trim_undo ((before, "edit cell"%pstring) :: ls_undo ls)) nil (ls_formats ls)
             (ls_other_sheets ls) (ls_active ls) (ls_charts ls)
             (ls_merges ls) (ls_sheet_names ls)
    | None =>
      let new_eb := put_edit (ls_edit_buf ls) r txt in
      let new_pe := add_ref (ls_parse_errs ls) r in
      mkLoop before (ls_selected ls) (ls_fbar_text ls)
             new_eb new_pe (ls_undo ls) (ls_redo ls) (ls_formats ls)
             (ls_other_sheets ls) (ls_active ls) (ls_charts ls)
             (ls_merges ls) (ls_sheet_names ls)
    end.

Definition do_commit (ls : loop_state) : loop_state :=
  match ls_selected ls with
  | None => ls
  | Some r => commit_to ls r (ls_fbar_text ls)
  end.

Definition do_undo (ls : loop_state) : loop_state :=
  match ls_undo ls with
  | nil => ls
  | (prev, desc) :: rest =>
    mkLoop prev (ls_selected ls) (ls_fbar_text ls)
           (ls_edit_buf ls) (ls_parse_errs ls)
           rest ((ls_sheet ls, desc) :: ls_redo ls) (ls_formats ls)
           (ls_other_sheets ls) (ls_active ls) (ls_charts ls)
           (ls_merges ls) (ls_sheet_names ls)
  end.

Definition do_redo (ls : loop_state) : loop_state :=
  match ls_redo ls with
  | nil => ls
  | (next, desc) :: rest =>
    mkLoop next (ls_selected ls) (ls_fbar_text ls)
           (ls_edit_buf ls) (ls_parse_errs ls)
           (trim_undo ((ls_sheet ls, desc) :: ls_undo ls)) rest
           (ls_formats ls)
           (ls_other_sheets ls) (ls_active ls) (ls_charts ls)
           (ls_merges ls) (ls_sheet_names ls)
  end.

Definition do_clear (ls : loop_state) : loop_state :=
  match ls_undo ls with
  | _ => mkLoop new_sheet None "" nil nil
                (trim_undo
                  ((ls_sheet ls, "clear sheet"%pstring) :: ls_undo ls))
                nil (ls_formats ls)
                (ls_other_sheets ls) (ls_active ls) (ls_charts ls)
                (ls_merges ls) (ls_sheet_names ls)
  end.

Definition lookup_sheet_or_new
    (xs : list (int * Sheet)) (k : int) : Sheet :=
  match assoc_int_lookup xs k with
  | Some sh => sh
  | None => new_sheet
  end.

Definition switch_to_sheet (ls : loop_state) (new_idx : int) : loop_state :=
  if PrimInt63.eqb new_idx (ls_active ls) then ls
  else
    let stored :=
      (ls_active ls, ls_sheet ls)
        :: assoc_int_remove (ls_other_sheets ls) (ls_active ls) in
    let new_sh := lookup_sheet_or_new stored new_idx in
    let new_other := assoc_int_remove stored new_idx in
    mkLoop new_sh None "" nil nil nil nil (ls_formats ls)
           new_other new_idx (ls_charts ls) (ls_merges ls)
           (ls_sheet_names ls).

Definition cond_apply (b : bool) (f : loop_state -> loop_state)
    (ls : loop_state) : loop_state :=
  if b then f ls else ls.

(* Inlining cond_apply at every call site lets the per-do_* Crane
   overrides below see do_undo / do_redo / etc. as direct call
   expressions instead of function values, which is the only form
   Extract Inlined Constant can rewrite. *)
Crane Extract Inlined Constant cond_apply =>
  "(%a0 ? %a1(std::move(%a2)) : (%a2))".

Crane Extract Inlined Constant do_undo =>
  "(::do_op_helpers::do_undo<loop_state, Rocqsheet::Sheet, List<std::pair<Rocqsheet::Sheet, std::string>>>(%a0))"
  From "do_op_helpers.h".

Crane Extract Inlined Constant do_redo =>
  "(::do_op_helpers::do_redo<loop_state, Rocqsheet::Sheet, List<std::pair<Rocqsheet::Sheet, std::string>>>(%a0))"
  From "do_op_helpers.h".

Crane Extract Inlined Constant do_clear =>
  "(::do_op_helpers::do_clear<loop_state, Rocqsheet::Sheet, List<std::pair<Rocqsheet::Sheet, std::string>>, List<std::pair<Rocqsheet::CellRef, std::string>>, List<Rocqsheet::CellRef>>(%a0, Rocqsheet::new_sheet))"
  From "do_op_helpers.h".

Definition do_insert_row (ls : loop_state) : loop_state :=
  match ls_selected ls with
  | None => ls
  | Some r =>
    let before := ls_sheet ls in
    let new_sheet := insert_row before (cell_row_of r) in
    mkLoop new_sheet (ls_selected ls) (ls_fbar_text ls)
           (ls_edit_buf ls) (ls_parse_errs ls)
           (trim_undo ((before, "insert row"%pstring) :: ls_undo ls)) nil
           (ls_formats ls)
           (ls_other_sheets ls) (ls_active ls) (ls_charts ls)
           (ls_merges ls) (ls_sheet_names ls)
  end.

Definition do_delete_row (ls : loop_state) : loop_state :=
  match ls_selected ls with
  | None => ls
  | Some r =>
    let before := ls_sheet ls in
    let new_sheet := delete_row before (cell_row_of r) in
    mkLoop new_sheet (ls_selected ls) (ls_fbar_text ls)
           (ls_edit_buf ls) (ls_parse_errs ls)
           (trim_undo ((before, "delete row"%pstring) :: ls_undo ls)) nil
           (ls_formats ls)
           (ls_other_sheets ls) (ls_active ls) (ls_charts ls)
           (ls_merges ls) (ls_sheet_names ls)
  end.

Definition do_swap_with_next_row (ls : loop_state) : loop_state :=
  match ls_selected ls with
  | None => ls
  | Some r =>
    let row := cell_row_of r in
    let next := PrimInt63.add row 1 in
    if PrimInt63.leb NUM_ROWS next then ls
    else
      let before := ls_sheet ls in
      let new_sheet := swap_rows before row next in
      mkLoop new_sheet (ls_selected ls) (ls_fbar_text ls)
             (ls_edit_buf ls) (ls_parse_errs ls)
             (trim_undo ((before, "swap rows"%pstring) :: ls_undo ls)) nil
             (ls_formats ls)
             (ls_other_sheets ls) (ls_active ls) (ls_charts ls)
             (ls_merges ls) (ls_sheet_names ls)
  end.

Crane Extract Inlined Constant do_insert_row =>
  "(::do_op_helpers::commit_via_selection<loop_state, Rocqsheet::Sheet, List<std::pair<Rocqsheet::Sheet, std::string>>>(%a0, std::string(""insert row""), [](const Rocqsheet::Sheet& __s, const Rocqsheet::CellRef& __r) { return Shift::insert_row(__s, Rocqsheet::cell_row_of(__r)); }))"
  From "do_op_helpers.h".

Crane Extract Inlined Constant do_delete_row =>
  "(::do_op_helpers::commit_via_selection<loop_state, Rocqsheet::Sheet, List<std::pair<Rocqsheet::Sheet, std::string>>>(%a0, std::string(""delete row""), [](const Rocqsheet::Sheet& __s, const Rocqsheet::CellRef& __r) { return Shift::delete_row(__s, Rocqsheet::cell_row_of(__r)); }))"
  From "do_op_helpers.h".

Crane Extract Inlined Constant do_swap_with_next_row =>
  "(::do_op_helpers::commit_via_selection<loop_state, Rocqsheet::Sheet, List<std::pair<Rocqsheet::Sheet, std::string>>>(%a0, std::string(""swap rows""), [](const Rocqsheet::Sheet& __s, const Rocqsheet::CellRef& __r) { int64_t __row = Rocqsheet::cell_row_of(__r); int64_t __next = (__row + 1) & 0x7FFFFFFFFFFFFFFFLL; return (Rocqsheet::NUM_ROWS <= __next) ? __s : Sorting::swap_rows(__s, __row, __next); }))"
  From "do_op_helpers.h".

(* Walk every cell of the sheet by index, lifting [replace_int_in_expr]
   through any [CForm] cell.  The Coq Fixpoint is the executable spec;
   the C++ extraction is overridden to call an iterative macro. *)
Fixpoint replace_in_sheet_aux (from to : Z) (s : Sheet) (idx : int)
    (fuel : nat) : Sheet :=
  match fuel with
  | O => s
  | S fuel' =>
    if PrimInt63.leb GRID_SIZE idx then s
    else
      let s' :=
        match PrimArray.get s idx with
        | CForm e =>
          PrimArray.set s idx (CForm (replace_int_in_expr from to e))
        | _ => s
        end in
      replace_in_sheet_aux from to s' (PrimInt63.add idx 1) fuel'
  end.

Definition replace_in_sheet (from to : Z) (s : Sheet) : Sheet :=
  replace_in_sheet_aux from to s 0 60000.

Crane Extract Inlined Constant replace_in_sheet =>
  "::find_replace_helpers::replace_in_sheet_impl(::Rocqsheet::GRID_SIZE, %a2, [&](const ::Rocqsheet::Expr& _e) { return ::FindReplace::replace_int_in_expr(%a0, %a1, _e); })"
  From "find_replace_helpers.h".

Definition do_replace_zero_one (ls : loop_state) : loop_state :=
  let before := ls_sheet ls in
  let new_sheet := replace_in_sheet 0%Z 1%Z before in
  mkLoop new_sheet (ls_selected ls) (ls_fbar_text ls)
         (ls_edit_buf ls) (ls_parse_errs ls)
         (trim_undo ((before, "replace 0 -> 1"%pstring) :: ls_undo ls)) nil
         (ls_formats ls)
         (ls_other_sheets ls) (ls_active ls) (ls_charts ls)
         (ls_merges ls) (ls_sheet_names ls).

Definition do_merge_right (ls : loop_state) : loop_state :=
  match ls_selected ls with
  | None => ls
  | Some r =>
    let right_c := PrimInt63.add (cell_col_of r) 1 in
    if PrimInt63.leb NUM_COLS right_c then ls
    else
      let br := mkRef right_c (cell_row_of r) in
      mkLoop (ls_sheet ls) (ls_selected ls) (ls_fbar_text ls)
             (ls_edit_buf ls) (ls_parse_errs ls)
             (ls_undo ls) (ls_redo ls) (ls_formats ls)
             (ls_other_sheets ls) (ls_active ls) (ls_charts ls)
             (add_merge (ls_merges ls) r br) (ls_sheet_names ls)
  end.
