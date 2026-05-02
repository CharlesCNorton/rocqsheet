(* Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License. *)
(* Save / load: bespoke text format with [V=], [S=], [N=], [c,r,text]
   directive lines, plus the [do_save / do_save_as / do_load / do_copy
   / do_paste / do_replace_user] effectful operators. *)

From Corelib Require Import PrimString PrimInt63.
From Stdlib Require Import List BinInt.
From Stdlib.Numbers.Cyclic.Int63 Require Import Uint63.
From Crane Require Extraction.
From Crane Require Import Mapping.NatIntStd Mapping.ZInt.
From Crane Require Import Monads.ITree.
From Rocqsheet Require Import Rocqsheet.
From Rocqsheet Require Import Parser.
From Rocqsheet Require Import ImGuiE.
From Rocqsheet Require Import Formatting.
From Rocqsheet Require Import NumberFormat.
From Rocqsheet Require Import State.
From Rocqsheet Require Import Edit.
Import ListNotations.
Import Rocqsheet.

Open Scope itree_scope.
Open Scope int63_scope.
Local Open Scope pstring_scope.

Axiom newline : PrimString.string.
Crane Extract Inlined Constant newline => "std::string(""\n"")".
Definition comma : PrimString.string := ",".

Fixpoint save_row_aux (s : Sheet) (eb : list (CellRef * PrimString.string))
    (r c : nat) (count : nat) (acc : PrimString.string)
  : PrimString.string :=
  match count with
  | O => acc
  | S count' =>
    let ref := ref_at c r in
    let txt :=
      match lookup_edit eb ref with
      | Some t => t
      | None => show_cell (get_cell s ref)
      end in
    let acc' :=
      if all_whitespace txt then acc
      else PrimString.cat acc
            (PrimString.cat (string_of_nat c)
              (PrimString.cat comma
                (PrimString.cat (string_of_nat r)
                  (PrimString.cat comma
                    (PrimString.cat txt newline))))) in
    save_row_aux s eb r (S c) count' acc'
  end.

Fixpoint save_rows_aux (s : Sheet) (eb : list (CellRef * PrimString.string))
    (r : nat) (count : nat) (cols : nat) (acc : PrimString.string)
  : PrimString.string :=
  match count with
  | O => acc
  | S count' =>
    let acc' := save_row_aux s eb r 0 cols acc in
    save_rows_aux s eb (S r) count' cols acc'
  end.

Definition save_path : PrimString.string := "rocqsheet.txt".

Definition sheet_at_slot (ls : loop_state) (idx : int) : Sheet :=
  if PrimInt63.eqb idx (ls_active ls) then ls_sheet ls
  else lookup_sheet_or_new (ls_other_sheets ls) idx.

Fixpoint sheet_is_empty_aux (s : Sheet) (i : int) (fuel : nat) : bool :=
  match fuel with
  | O => true
  | S fuel' =>
    if PrimInt63.leb GRID_SIZE i then true
    else
      match PrimArray.get s i with
      | CEmpty => sheet_is_empty_aux s (PrimInt63.add i 1) fuel'
      | _ => false
      end
  end.

Definition sheet_is_empty (s : Sheet) : bool :=
  sheet_is_empty_aux s 0 60000.

Definition save_sheet_block (ls : loop_state) (idx : int)
  : PrimString.string :=
  let s := sheet_at_slot ls idx in
  if sheet_is_empty s then ""
  else
    let header :=
      PrimString.cat "S=" (
      PrimString.cat (string_of_z (Uint63.to_Z idx)) newline) in
    let name := list_nth_string (ls_sheet_names ls)
                                (nat_of_int idx) "" in
    let name_line :=
      PrimString.cat "N=" (PrimString.cat name newline) in
    let body :=
      save_rows_aux s (ls_edit_buf ls) 0 200 260 "" in
    PrimString.cat header (PrimString.cat name_line body).

Fixpoint save_all_sheets_aux (ls : loop_state) (i : nat) (count : nat)
                             (acc : PrimString.string)
  : PrimString.string :=
  match count with
  | O => acc
  | S count' =>
    let acc' := PrimString.cat acc
                  (save_sheet_block ls (int_of_nat i)) in
    save_all_sheets_aux ls (S i) count' acc'
  end.

(* Encode a NumberFormat as a save-file token: "I" for integer,
   "D<digits>" for decimal, "C" for currency, "P" for percent. *)
Definition save_nf_token (nf : NumberFormat) : PrimString.string :=
  match nf with
  | NFInteger     => "I"
  | NFDecimal n   => PrimString.cat "D" (string_of_z n)
  | NFCurrency    => "C"
  | NFPercent     => "P"
  end.

Definition save_align_token (a : Align) : PrimString.string :=
  match a with
  | AlignLeft   => "0"
  | AlignCenter => "1"
  | AlignRight  => "2"
  end.

Definition save_bool_token (b : bool) : PrimString.string :=
  if b then "1" else "0".

(* Emit one F=col,row,bold,color,border,align,nf line per FormatMap
   entry.  Persists every per-cell formatting choice across save /
   load. *)
Definition save_format_line (e : CellRef * CellFormat) : PrimString.string :=
  let r := fst e in
  let f := snd e in
  PrimString.cat "F=" (
  PrimString.cat (string_of_z (Uint63.to_Z (cell_col_of r))) (
  PrimString.cat comma (
  PrimString.cat (string_of_z (Uint63.to_Z (cell_row_of r))) (
  PrimString.cat comma (
  PrimString.cat (save_bool_token (fmt_bold f)) (
  PrimString.cat comma (
  PrimString.cat (string_of_z (fmt_color_rgb f)) (
  PrimString.cat comma (
  PrimString.cat (save_bool_token (fmt_border f)) (
  PrimString.cat comma (
  PrimString.cat (save_align_token (fmt_align f)) (
  PrimString.cat comma (
  PrimString.cat (save_nf_token (fmt_number f)) newline))))))))))))).

Fixpoint save_all_formats_aux (fm : FormatMap) (acc : PrimString.string)
  : PrimString.string :=
  match fm with
  | nil => acc
  | e :: rest =>
    save_all_formats_aux rest (PrimString.cat acc (save_format_line e))
  end.

Definition build_save_string (ls : loop_state) : PrimString.string :=
  PrimString.cat "# Rocqsheet save file" (
  PrimString.cat newline (
  PrimString.cat (save_all_formats_aux (ls_formats ls) "")
  (save_all_sheets_aux ls 0 16 ""))).

Definition do_save (ls : loop_state) : itree imguiE loop_state :=
  let _ := tt in
  _ <- file_write save_path (build_save_string ls) ;;
  Ret ls.

Definition do_save_as (ls : loop_state) : itree imguiE loop_state :=
  let path :=
    if all_whitespace (ls_fbar_text ls)
    then save_path
    else ls_fbar_text ls in
  _ <- file_write path (build_save_string ls) ;;
  Ret ls.

(* Find/Replace driven by the formula bar.  Expects [ls_fbar_text] of
   the form "FROM|TO" with integer literals on both sides. *)
Fixpoint split_pipe_aux (s : PrimString.string) (len i : int) (fuel : nat)
  : option int :=
  match fuel with
  | O => None
  | S fuel' =>
    if PrimInt63.ltb i len then
      if PrimInt63.eqb (char_to_int (PrimString.get s i)) 124 (* '|' *)
      then Some i
      else split_pipe_aux s len (PrimInt63.add i 1) fuel'
    else None
  end.

Definition parse_replace_pair (s : PrimString.string)
  : option (Z * Z) :=
  let len := PrimString.length s in
  match split_pipe_aux s len 0 (S (nat_of_int len)) with
  | None => None
  | Some pipe =>
    let from_str := PrimString.sub s 0 pipe in
    let to_str := PrimString.sub s
                   (PrimInt63.add pipe 1)
                   (PrimInt63.sub len (PrimInt63.add pipe 1)) in
    match parse_int_literal from_str, parse_int_literal to_str with
    | Some f, Some t => Some (f, t)
    | _, _ => None
    end
  end.

Definition do_replace_user (ls : loop_state) : loop_state :=
  match ls_undo ls with
  | _ =>
    let before := ls_sheet ls in
    let pair :=
      match parse_replace_pair (ls_fbar_text ls) with
      | Some (f, t) => (f, t)
      | None => (0%Z, 1%Z)
      end in
    let new_sheet := replace_in_sheet (fst pair) (snd pair) before in
    mkLoop new_sheet (ls_selected ls) (ls_fbar_text ls)
           (ls_edit_buf ls) (ls_parse_errs ls)
           (trim_undo ((before, "replace"%pstring) :: ls_undo ls)) nil
           (ls_formats ls)
           (ls_other_sheets ls) (ls_active ls) (ls_charts ls)
           (ls_merges ls) (ls_sheet_names ls)
  end.

Fixpoint parse_uint_aux (fuel : nat) (s : PrimString.string) (len i : int)
    (acc : Z) (any : bool) : option (Z * int) :=
  match fuel with
  | O => if any then Some (acc, i) else None
  | S fuel' =>
    if PrimInt63.ltb i len then
      let c := PrimString.get s i in
      if is_digit c then
        let d := digit_value c in
        parse_uint_aux fuel' s len (PrimInt63.add i 1)
          (Z.add (Z.mul acc 10) d) true
      else
        if any then Some (acc, i) else None
    else
      if any then Some (acc, i) else None
  end.

Fixpoint find_eol_aux (txt : PrimString.string) (len i : int) (fuel : nat)
  : int :=
  match fuel with
  | O => i
  | S fuel' =>
    if PrimInt63.ltb i len then
      if PrimInt63.eqb (char_to_int (PrimString.get txt i)) 10
      then i else find_eol_aux txt len (PrimInt63.add i 1) fuel'
    else i
  end.

Definition apply_sheet_switch
    (ls : loop_state) (txt : PrimString.string) (len i : int) (fuel : nat)
  : loop_state * int :=
  let eq_pos := PrimInt63.add i 1 in
  if PrimInt63.leb len eq_pos then (ls, len)
  else if negb (PrimInt63.eqb (char_to_int (PrimString.get txt eq_pos)) 61)
  then (ls, PrimInt63.add (find_eol_aux txt len i fuel) 1)
  else
    let n_start := PrimInt63.add eq_pos 1 in
    match parse_uint_aux fuel txt len n_start 0%Z false with
    | None => (ls, PrimInt63.add (find_eol_aux txt len i fuel) 1)
    | Some (idx_z, _) =>
      let eol := find_eol_aux txt len n_start fuel in
      let next_i := if PrimInt63.ltb eol len
                    then PrimInt63.add eol 1 else eol in
      let in_bounds :=
        andb (Z.leb 0 idx_z) (Z.ltb idx_z 16) in
      if in_bounds then
        (switch_to_sheet ls (Uint63.of_Z idx_z), next_i)
      else (ls, next_i)
    end.

Definition apply_sheet_rename
    (ls : loop_state) (txt : PrimString.string) (len i : int) (fuel : nat)
  : loop_state * int :=
  let eq_pos := PrimInt63.add i 1 in
  if PrimInt63.leb len eq_pos then (ls, len)
  else if negb (PrimInt63.eqb (char_to_int (PrimString.get txt eq_pos)) 61)
  then (ls, PrimInt63.add (find_eol_aux txt len i fuel) 1)
  else
    let name_start := PrimInt63.add eq_pos 1 in
    let eol := find_eol_aux txt len name_start fuel in
    let name := PrimString.sub txt name_start (PrimInt63.sub eol name_start) in
    let next_i := if PrimInt63.ltb eol len
                  then PrimInt63.add eol 1 else eol in
    let new_names :=
      list_set_nth_string (ls_sheet_names ls)
                          (nat_of_int (ls_active ls)) name in
    let ls' := mkLoop (ls_sheet ls) (ls_selected ls) (ls_fbar_text ls)
                      (ls_edit_buf ls) (ls_parse_errs ls)
                      (ls_undo ls) (ls_redo ls) (ls_formats ls)
                      (ls_other_sheets ls) (ls_active ls)
                      (ls_charts ls) (ls_merges ls) new_names in
    (ls', next_i).

(* Parse a single uint terminated by [stop_char] starting at [i].
   Returns (value, next-position) on success.  Used by the load-side
   format-line parser to keep its body manageable. *)
Definition parse_uint_field (txt : PrimString.string) (len i : int)
                            (stop_char : int) (fuel : nat)
  : option (Z * int) :=
  match parse_uint_aux fuel txt len i 0%Z false with
  | None => None
  | Some (v, k) =>
    if PrimInt63.leb len k then None
    else if PrimInt63.eqb (char_to_int (PrimString.get txt k)) stop_char
    then Some (v, PrimInt63.add k 1)
    else None
  end.

(* Parse the NumberFormat tail of an F= line: "I", "D<digits>",
   "C", or "P".  [start] is the offset of the leading char; returns
   the parsed format and the eol position. *)
Definition parse_nf_token (txt : PrimString.string) (len start : int)
                          (fuel : nat)
  : option (NumberFormat * int) :=
  if PrimInt63.leb len start then None
  else
    let c := char_to_int (PrimString.get txt start) in
    let eol := find_eol_aux txt len start fuel in
    if PrimInt63.eqb c 73 (* 'I' *)
    then Some (NFInteger, eol)
    else if PrimInt63.eqb c 67 (* 'C' *)
    then Some (NFCurrency, eol)
    else if PrimInt63.eqb c 80 (* 'P' *)
    then Some (NFPercent, eol)
    else if PrimInt63.eqb c 68 (* 'D' *)
    then
      match parse_uint_aux fuel txt len (PrimInt63.add start 1) 0%Z false with
      | None => None
      | Some (digits, _) => Some (NFDecimal digits, eol)
      end
    else None.

(* Apply an F=col,row,bold,color,border,align,nf line starting at
   [i] (where 'F' has just been seen).  Returns the updated
   loop_state and the next-line offset. *)
Definition apply_format_line
    (ls : loop_state) (txt : PrimString.string) (len i : int) (fuel : nat)
  : loop_state * int :=
  let eq_pos := PrimInt63.add i 1 in
  if PrimInt63.leb len eq_pos then (ls, len)
  else if negb (PrimInt63.eqb (char_to_int (PrimString.get txt eq_pos)) 61)
  then (ls, PrimInt63.add (find_eol_aux txt len i fuel) 1)
  else
    let p0 := PrimInt63.add eq_pos 1 in
    match parse_uint_field txt len p0 44 fuel with
    | None => (ls, PrimInt63.add (find_eol_aux txt len i fuel) 1)
    | Some (col_z, p1) =>
    match parse_uint_field txt len p1 44 fuel with
    | None => (ls, PrimInt63.add (find_eol_aux txt len i fuel) 1)
    | Some (row_z, p2) =>
    match parse_uint_field txt len p2 44 fuel with
    | None => (ls, PrimInt63.add (find_eol_aux txt len i fuel) 1)
    | Some (bold_z, p3) =>
    match parse_uint_field txt len p3 44 fuel with
    | None => (ls, PrimInt63.add (find_eol_aux txt len i fuel) 1)
    | Some (color_z, p4) =>
    match parse_uint_field txt len p4 44 fuel with
    | None => (ls, PrimInt63.add (find_eol_aux txt len i fuel) 1)
    | Some (border_z, p5) =>
    match parse_uint_field txt len p5 44 fuel with
    | None => (ls, PrimInt63.add (find_eol_aux txt len i fuel) 1)
    | Some (align_z, p6) =>
    match parse_nf_token txt len p6 fuel with
    | None => (ls, PrimInt63.add (find_eol_aux txt len i fuel) 1)
    | Some (nf, eol) =>
      let next_i := if PrimInt63.ltb eol len
                    then PrimInt63.add eol 1 else eol in
      let r := mkRef (Uint63.of_Z col_z) (Uint63.of_Z row_z) in
      let bold := if Z.eqb bold_z 0%Z then false else true in
      let border := if Z.eqb border_z 0%Z then false else true in
      let align :=
        if Z.eqb align_z 0%Z then AlignLeft
        else if Z.eqb align_z 1%Z then AlignCenter
        else AlignRight in
      let f := mkFormat bold color_z border align nf in
      let new_fmts := put_format (ls_formats ls) r f in
      let ls' :=
        mkLoop (ls_sheet ls) (ls_selected ls) (ls_fbar_text ls)
               (ls_edit_buf ls) (ls_parse_errs ls)
               (ls_undo ls) (ls_redo ls)
               new_fmts
               (ls_other_sheets ls) (ls_active ls) (ls_charts ls)
               (ls_merges ls) (ls_sheet_names ls) in
      (ls', next_i)
    end end end end end end end.

Fixpoint apply_load_lines
    (ls : loop_state) (txt : PrimString.string) (len i : int) (fuel : nat)
  : loop_state :=
  match fuel with
  | O => ls
  | S fuel' =>
    if PrimInt63.leb len i then ls
    else
      let c := char_to_int (PrimString.get txt i) in
      if PrimInt63.eqb c 35 then
        let next := PrimInt63.add (find_eol_aux txt len i fuel') 1 in
        apply_load_lines ls txt len next fuel'
      else if PrimInt63.eqb c 10 then
        apply_load_lines ls txt len (PrimInt63.add i 1) fuel'
      else if PrimInt63.eqb c 83 (* 'S' *) then
        let '(ls', next) := apply_sheet_switch ls txt len i fuel' in
        apply_load_lines ls' txt len next fuel'
      else if PrimInt63.eqb c 78 (* 'N' *) then
        let '(ls', next) := apply_sheet_rename ls txt len i fuel' in
        apply_load_lines ls' txt len next fuel'
      else if PrimInt63.eqb c 70 (* 'F' *) then
        let '(ls', next) := apply_format_line ls txt len i fuel' in
        apply_load_lines ls' txt len next fuel'
      else
        match parse_uint_aux fuel' txt len i 0%Z false with
        | None => apply_load_lines ls txt len (PrimInt63.add i 1) fuel'
        | Some (col_z, j) =>
          if PrimInt63.leb len j then ls
          else if PrimInt63.eqb (char_to_int (PrimString.get txt j)) 44 then
            let j1 := PrimInt63.add j 1 in
            match parse_uint_aux fuel' txt len j1 0%Z false with
            | None => apply_load_lines ls txt len (PrimInt63.add i 1) fuel'
            | Some (row_z, k) =>
              if PrimInt63.leb len k then ls
              else if PrimInt63.eqb (char_to_int (PrimString.get txt k)) 44 then
                let k1 := PrimInt63.add k 1 in
                let eol := find_eol_aux txt len k1 fuel' in
                let line := PrimString.sub txt k1 (PrimInt63.sub eol k1) in
                let r := mkRef (Uint63.of_Z col_z) (Uint63.of_Z row_z) in
                let in_bounds :=
                  andb (Z.leb 0 col_z)
                       (andb (Z.ltb col_z 260)
                             (andb (Z.leb 0 row_z) (Z.ltb row_z 200))) in
                let next_i :=
                  if PrimInt63.ltb eol len
                  then PrimInt63.add eol 1 else eol in
                if in_bounds then
                  apply_load_lines (commit_to ls r line) txt len next_i fuel'
                else
                  apply_load_lines ls txt len next_i fuel'
              else apply_load_lines ls txt len (PrimInt63.add i 1) fuel'
            end
          else apply_load_lines ls txt len (PrimInt63.add i 1) fuel'
        end
  end.

Definition do_load (ls : loop_state) : itree imguiE loop_state :=
  res <- file_read save_path ;;
  let '(content, ok) := res in
  if ok then
    let cleared := mkLoop new_sheet None "" nil nil
                          (trim_undo
                            ((ls_sheet ls, "load file"%pstring) :: ls_undo ls))
                          nil
                          (ls_formats ls)
                          (ls_other_sheets ls) (ls_active ls)
                          (ls_charts ls) (ls_merges ls) (ls_sheet_names ls) in
    let len := PrimString.length content in
    Ret (apply_load_lines cleared content len 0
                          (S (S (nat_of_int len))))
  else Ret ls.

Definition do_copy (ls : loop_state) : itree imguiE unit :=
  match ls_selected ls with
  | None => Ret tt
  | Some r =>
    clipboard_set (fbar_for_cell (ls_edit_buf ls) (ls_sheet ls) r)
  end.

Definition do_paste (ls : loop_state) : itree imguiE loop_state :=
  s <- clipboard_get ;;
  Ret (update_fbar ls s).
