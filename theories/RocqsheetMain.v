(* Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License. *)
(* Rocqsheet runtime: per-frame procedure, frame loop, and entry
   point invoked by [src/main.cpp] after GLFW + ImGui setup. *)

From Corelib Require Import PrimString PrimInt63.
From Stdlib Require Import List BinInt.
From Stdlib.Numbers.Cyclic.Int63 Require Import Uint63.
From Crane Require Extraction.
From Crane Require Import Mapping.NatIntStd Mapping.ZInt.
From Crane Require Import Monads.ITree.
From Rocqsheet Require Import Rocqsheet.
From Rocqsheet Require Import ImGuiE.
From Rocqsheet Require Import Parser.
Import ListNotations.
Import Rocqsheet.

Open Scope itree_scope.
Open Scope int63_scope.
Local Open Scope pstring_scope.

(* Coercions used by the rendering layer. *)
Axiom int_of_nat : nat -> int.
Crane Extract Inlined Constant int_of_nat =>
  "static_cast<int64_t>(%a0)".

Axiom string_of_z : Z -> PrimString.string.
Crane Extract Inlined Constant string_of_z =>
  "std::to_string(%a0)".

(* Column-header label generation: A..Z then AA..IZ. *)
Definition letters : list PrimString.string :=
  ["A"; "B"; "C"; "D"; "E"; "F"; "G"; "H"; "I"; "J"; "K"; "L"; "M";
   "N"; "O"; "P"; "Q"; "R"; "S"; "T"; "U"; "V"; "W"; "X"; "Y"; "Z"].

Definition letter_at (n : nat) : PrimString.string :=
  nth n letters "?".

Definition col_label_nat (n : nat) : PrimString.string :=
  if Nat.ltb n 26 then letter_at n
  else PrimString.cat (letter_at (Nat.pred (Nat.div n 26)))
                     (letter_at (Nat.modulo n 26)).

Definition col_label_int (n : int) : PrimString.string :=
  col_label_nat (nat_of_int n).

(* Row and column accessors for [CellRef] computed via [cell_index]
   so the extracted C++ does not emit a base-class-qualified
   projection (which Crane would do for direct [ref_col r] /
   [ref_row r] outside the [Rocqsheet] module). *)
Definition cell_col_of (r : CellRef) : int :=
  PrimInt63.mod (cell_index r) NUM_COLS.

Definition cell_row_of (r : CellRef) : int :=
  PrimInt63.div (cell_index r) NUM_COLS.

Definition cell_label (r : CellRef) : PrimString.string :=
  PrimString.cat (col_label_int (cell_col_of r))
                 (string_of_z (Z.add (Uint63.to_Z (cell_row_of r)) 1)).

(* Demo state: arithmetic, IF, comparison, and error branches. *)
Definition put_lit (s : Sheet) (c r : nat) (v : Z) : Sheet :=
  set_cell s (mkRef (int_of_nat c) (int_of_nat r)) (CLit v).

Definition put_form (s : Sheet) (c r : nat) (e : Expr) : Sheet :=
  set_cell s (mkRef (int_of_nat c) (int_of_nat r)) (CForm e).

Definition ref_at (c r : nat) : CellRef :=
  mkRef (int_of_nat c) (int_of_nat r).

Definition demo_sheet : Sheet :=
  let s := new_sheet in
  let s := put_lit s 0 0 2%Z in
  let s := put_lit s 1 0 3%Z in
  let s := put_form s 2 0
             (EAdd (ERef (ref_at 0 0)) (ERef (ref_at 1 0))) in
  let s := put_form s 3 0
             (EMul (EAdd (ERef (ref_at 0 0)) (ERef (ref_at 1 0)))
                   (EInt 7%Z)) in
  let s := put_lit s 0 2 12%Z in
  let s := put_lit s 1 2 5%Z in
  let s := put_form s 2 2
             (EMul (ERef (ref_at 0 2)) (ERef (ref_at 1 2))) in
  let s := put_form s 3 2
             (EDiv (ERef (ref_at 0 2)) (ERef (ref_at 1 2))) in
  let s := put_lit s 0 4 100%Z in
  let s := put_lit s 1 4 50%Z in
  let s := put_form s 2 4
             (ESub (ERef (ref_at 0 4)) (ERef (ref_at 1 4))) in
  let s := put_lit s 0 6 7%Z in
  let s := put_lit s 1 6 3%Z in
  let s := put_form s 2 6
             (EIf (EGt (ERef (ref_at 0 6)) (ERef (ref_at 1 6)))
                  (ERef (ref_at 0 6)) (ERef (ref_at 1 6))) in
  let s := put_form s 3 6
             (EEq (ERef (ref_at 0 6)) (ERef (ref_at 1 6))) in
  let s := put_lit s 0 8 10%Z in
  let s := put_form s 2 8
             (EIf (ELt (ERef (ref_at 0 8)) (EInt 5%Z))
                  (EMul (ERef (ref_at 0 8)) (EInt 2%Z))
                  (ESub (ERef (ref_at 0 8)) (EInt 5%Z))) in
  let s := put_lit s 0 10 8%Z in
  let s := put_form s 2 10
             (EDiv (ERef (ref_at 0 10)) (EInt 0%Z)) in
  let s := put_form s 0 12 (ERef (ref_at 0 12)) in
  let s := put_form s 1 12 (ERef (ref_at 0 12)) in
  s.

(* ----- Pretty printer (Cell -> source text) ----------------------- *)

Fixpoint show_expr (e : Expr) : PrimString.string :=
  match e with
  | EInt n => string_of_z n
  | ERef r => cell_label r
  | EAdd a b => PrimString.cat
                 (PrimString.cat
                   (PrimString.cat "(" (show_expr a))
                   ")+(")
                 (PrimString.cat (show_expr b) ")")
  | ESub a b => PrimString.cat
                 (PrimString.cat
                   (PrimString.cat "(" (show_expr a))
                   ")-(")
                 (PrimString.cat (show_expr b) ")")
  | EMul a b => PrimString.cat
                 (PrimString.cat
                   (PrimString.cat "(" (show_expr a))
                   ")*(")
                 (PrimString.cat (show_expr b) ")")
  | EDiv a b => PrimString.cat
                 (PrimString.cat
                   (PrimString.cat "(" (show_expr a))
                   ")/(")
                 (PrimString.cat (show_expr b) ")")
  | EEq a b => PrimString.cat
                 (PrimString.cat
                   (PrimString.cat "(" (show_expr a))
                   ")=(")
                 (PrimString.cat (show_expr b) ")")
  | ELt a b => PrimString.cat
                 (PrimString.cat
                   (PrimString.cat "(" (show_expr a))
                   ")<(")
                 (PrimString.cat (show_expr b) ")")
  | EGt a b => PrimString.cat
                 (PrimString.cat
                   (PrimString.cat "(" (show_expr a))
                   ")>(")
                 (PrimString.cat (show_expr b) ")")
  | EIf c t e =>
    PrimString.cat "IF("
      (PrimString.cat (show_expr c)
        (PrimString.cat ","
          (PrimString.cat (show_expr t)
            (PrimString.cat ","
              (PrimString.cat (show_expr e) ")")))))
  | EMod a b => PrimString.cat
                 (PrimString.cat
                   (PrimString.cat "(" (show_expr a))
                   ")%(")
                 (PrimString.cat (show_expr b) ")")
  | EPow a b => PrimString.cat
                 (PrimString.cat
                   (PrimString.cat "(" (show_expr a))
                   ")^(")
                 (PrimString.cat (show_expr b) ")")
  end.

Definition show_cell (c : Cell) : PrimString.string :=
  match c with
  | CEmpty => ""
  | CLit n => string_of_z n
  | CForm e => PrimString.cat "=" (show_expr e)
  end.

(* ----- Loop state --------------------------------------------- *)

Record loop_state : Type := mkLoop {
  ls_sheet      : Sheet;
  ls_selected   : option CellRef;
  ls_fbar_text  : PrimString.string;
  ls_edit_buf   : list (CellRef * PrimString.string);
  ls_parse_errs : list CellRef;
  ls_undo       : list Sheet;
  ls_redo       : list Sheet
}.

Definition initial_loop_state : loop_state :=
  mkLoop demo_sheet None "" nil nil nil nil.

(* ----- Edit-buffer / parse-error helpers -------------------- *)

Fixpoint lookup_edit (eb : list (CellRef * PrimString.string)) (r : CellRef)
  : option PrimString.string :=
  match eb with
  | nil => None
  | (r', s) :: rest =>
    if cellref_eqb r r' then Some s else lookup_edit rest r
  end.

Fixpoint remove_edit (eb : list (CellRef * PrimString.string)) (r : CellRef)
  : list (CellRef * PrimString.string) :=
  match eb with
  | nil => nil
  | (r', s) :: rest =>
    if cellref_eqb r r' then rest else (r', s) :: remove_edit rest r
  end.

Definition put_edit (eb : list (CellRef * PrimString.string))
    (r : CellRef) (s : PrimString.string)
  : list (CellRef * PrimString.string) :=
  (r, s) :: remove_edit eb r.

Fixpoint mem_ref (xs : list CellRef) (r : CellRef) : bool :=
  match xs with
  | nil => false
  | r' :: rest => if cellref_eqb r r' then true else mem_ref rest r
  end.

Fixpoint remove_ref (xs : list CellRef) (r : CellRef) : list CellRef :=
  match xs with
  | nil => nil
  | r' :: rest =>
    if cellref_eqb r r' then rest else r' :: remove_ref rest r
  end.

Definition add_ref (xs : list CellRef) (r : CellRef) : list CellRef :=
  if mem_ref xs r then xs else r :: xs.

(* ----- Cell display ----------------------------------------- *)

Definition err_marker : PrimString.string := "#ERR".
Definition parse_marker : PrimString.string := "#PARSE".

(* The string shown inside a cell for the user. *)
Definition cell_display (s : Sheet) (errs : list CellRef) (r : CellRef)
  : PrimString.string * bool :=
  if mem_ref errs r then (parse_marker, true)
  else
    match get_cell s r with
    | CEmpty => ("", false)
    | CLit n => (string_of_z n, false)
    | CForm e =>
      match eval_expr DEFAULT_FUEL (cons r nil) s e with
      | Some v => (string_of_z v, false)
      | None => (err_marker, true)
      end
    end.

(* What text to show in the formula bar for a given cell. *)
Definition fbar_for_cell
    (eb : list (CellRef * PrimString.string)) (s : Sheet) (r : CellRef)
  : PrimString.string :=
  match lookup_edit eb r with
  | Some t => t
  | None => show_cell (get_cell s r)
  end.

(* ----- Pure event handlers --------------------------------- *)

Definition push_undo (ls : loop_state) (before : Sheet) : loop_state :=
  mkLoop (ls_sheet ls) (ls_selected ls) (ls_fbar_text ls)
         (ls_edit_buf ls) (ls_parse_errs ls)
         (before :: ls_undo ls) nil.

Definition select_cell (ls : loop_state) (r : CellRef) : loop_state :=
  mkLoop (ls_sheet ls) (Some r)
         (fbar_for_cell (ls_edit_buf ls) (ls_sheet ls) r)
         (ls_edit_buf ls) (ls_parse_errs ls)
         (ls_undo ls) (ls_redo ls).

Definition update_fbar (ls : loop_state) (s : PrimString.string) : loop_state :=
  mkLoop (ls_sheet ls) (ls_selected ls) s
         (ls_edit_buf ls) (ls_parse_errs ls)
         (ls_undo ls) (ls_redo ls).

(* Inspect leading character.  Empty string returns 0. *)
Definition first_char_int (s : PrimString.string) : int :=
  if PrimInt63.ltb 0 (PrimString.length s)
  then char_to_int (PrimString.get s 0)
  else 0.

(* Skip the leading '=' (and any whitespace before it).  Used to
   feed the formula portion of "=A1+B1" into [parse_formula]. *)
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

(* True if [s] is empty or contains only whitespace. *)
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
           new_eb new_pe (before :: ls_undo ls) nil
  else if starts_with_eq txt then
    let body := strip_leading_eq txt in
    match parse_formula body with
    | Some e =>
      let new_sheet := set_cell before r (CForm e) in
      let new_eb := put_edit (ls_edit_buf ls) r txt in
      let new_pe := remove_ref (ls_parse_errs ls) r in
      mkLoop new_sheet (ls_selected ls) (ls_fbar_text ls)
             new_eb new_pe (before :: ls_undo ls) nil
    | None =>
      let new_eb := put_edit (ls_edit_buf ls) r txt in
      let new_pe := add_ref (ls_parse_errs ls) r in
      mkLoop before (ls_selected ls) (ls_fbar_text ls)
             new_eb new_pe (ls_undo ls) (ls_redo ls)
    end
  else
    match parse_int_literal txt with
    | Some v =>
      let new_sheet := set_cell before r (CLit v) in
      let new_eb := put_edit (ls_edit_buf ls) r txt in
      let new_pe := remove_ref (ls_parse_errs ls) r in
      mkLoop new_sheet (ls_selected ls) (ls_fbar_text ls)
             new_eb new_pe (before :: ls_undo ls) nil
    | None =>
      let new_eb := put_edit (ls_edit_buf ls) r txt in
      let new_pe := add_ref (ls_parse_errs ls) r in
      mkLoop before (ls_selected ls) (ls_fbar_text ls)
             new_eb new_pe (ls_undo ls) (ls_redo ls)
    end.

Definition do_commit (ls : loop_state) : loop_state :=
  match ls_selected ls with
  | None => ls
  | Some r => commit_to ls r (ls_fbar_text ls)
  end.

Definition do_undo (ls : loop_state) : loop_state :=
  match ls_undo ls with
  | nil => ls
  | prev :: rest =>
    mkLoop prev (ls_selected ls) (ls_fbar_text ls)
           (ls_edit_buf ls) (ls_parse_errs ls)
           rest (ls_sheet ls :: ls_redo ls)
  end.

Definition do_redo (ls : loop_state) : loop_state :=
  match ls_redo ls with
  | nil => ls
  | next :: rest =>
    mkLoop next (ls_selected ls) (ls_fbar_text ls)
           (ls_edit_buf ls) (ls_parse_errs ls)
           (ls_sheet ls :: ls_undo ls) rest
  end.

Definition do_clear (ls : loop_state) : loop_state :=
  mkLoop new_sheet None "" nil nil
         (ls_sheet ls :: ls_undo ls) nil.

(* Conditional apply.  Used in handler chains to avoid extracting a
   declare-then-assign pattern that would require a default
   constructor on [loop_state]. *)
Definition cond_apply (b : bool) (f : loop_state -> loop_state)
    (ls : loop_state) : loop_state :=
  if b then f ls else ls.

(* ----- Save / load -------------------------------------------------
   On-disk format: one line per non-empty cell, "<col>,<row>,<text>",
   with optional leading "# ..." comments.  The text on each line is
   what the user typed (or, for demo cells, the [show_cell] output). *)

Axiom newline : PrimString.string.
Crane Extract Inlined Constant newline => "std::string(""\n"")".
Definition comma : PrimString.string := ",".

(* Build a save string by walking all NUM_COLS x NUM_ROWS cells. *)

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

Definition build_save_string (ls : loop_state) : PrimString.string :=
  PrimString.cat "# Rocqsheet save file" (
  PrimString.cat newline (
  save_rows_aux (ls_sheet ls) (ls_edit_buf ls) 0 200 260 "")).

Definition do_save (ls : loop_state) : itree imguiE loop_state :=
  let _ := tt in
  _ <- file_write save_path (build_save_string ls) ;;
  Ret ls.

(* Parse one save-file line: "c,r,text" -> Some (c, r, text). *)

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

(* Walk the save string, splitting on newlines, and dispatch each line
   through [commit_to] on a fresh sheet. *)
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
        (* skip comment line *)
        let fix skip (j : int) (g : nat) : int :=
          match g with
          | O => j
          | S g' =>
            if PrimInt63.ltb j len then
              if PrimInt63.eqb
                   (char_to_int (PrimString.get txt j)) 10
              then PrimInt63.add j 1
              else skip (PrimInt63.add j 1) g'
            else j
          end in
        apply_load_lines ls txt len (skip i fuel') fuel'
      else if PrimInt63.eqb c 10 then
        apply_load_lines ls txt len (PrimInt63.add i 1) fuel'
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
                let fix find_eol (j : int) (g : nat) : int :=
                  match g with
                  | O => j
                  | S g' =>
                    if PrimInt63.ltb j len then
                      if PrimInt63.eqb
                           (char_to_int (PrimString.get txt j)) 10
                      then j else find_eol (PrimInt63.add j 1) g'
                    else j
                  end in
                let eol := find_eol k1 fuel' in
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
                          (ls_sheet ls :: ls_undo ls) nil in
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

(* ----- Cell rendering with selection state ------------------ *)

Definition render_one_cell
    (ls : loop_state) (c r : nat) : itree imguiE loop_state :=
  let ref := ref_at c r in
  let '(disp, is_err) := cell_display (ls_sheet ls) (ls_parse_errs ls) ref in
  let selected :=
    match ls_selected ls with
    | None => false
    | Some sr => cellref_eqb sr ref
    end in
  ev <- imgui_selectable_cell (int_of_nat c) (int_of_nat r)
                               selected is_err disp ;;
  match ev with
  | CellNone => Ret ls
  | _ => Ret (select_cell ls ref)
  end.

Fixpoint render_cells_in_row
    (ls : loop_state) (r : nat) (c : nat) (count : nat)
  : itree imguiE loop_state :=
  match count with
  | O => Ret ls
  | S count' =>
    imgui_table_set_column_index (int_of_nat (S c)) ;;
    ls' <- render_one_cell ls c r ;;
    render_cells_in_row ls' r (S c) count'
  end.

Fixpoint render_rows_in_range
    (ls : loop_state) (start : nat) (count : nat) (num_cols : nat)
  : itree imguiE loop_state :=
  match count with
  | O => Ret ls
  | S count' =>
    imgui_table_next_row ;;
    imgui_table_set_column_index 0 ;;
    imgui_text (string_of_nat (S start)) ;;
    ls' <- render_cells_in_row ls start 0 num_cols ;;
    render_rows_in_range ls' (S start) count' num_cols
  end.

Fixpoint clipper_loop
    (fuel : nat) (ls : loop_state) (num_cols : nat)
  : itree imguiE loop_state :=
  match fuel with
  | O => Ret ls
  | S fuel' =>
    cont <- imgui_clipper_step ;;
    if cont then
      start_i <- imgui_clipper_get_start ;;
      end_i <- imgui_clipper_get_end ;;
      let count := nat_of_int (PrimInt63.sub end_i start_i) in
      let s_idx := nat_of_int start_i in
      ls' <- render_rows_in_range ls s_idx count num_cols ;;
      clipper_loop fuel' ls' num_cols
    else
      Ret ls
  end.

Fixpoint setup_columns (c : nat) (count : nat) : itree imguiE unit :=
  match count with
  | O => Ret tt
  | S count' =>
    imgui_table_setup_column (col_label_nat c) 80 ;;
    setup_columns (S c) count'
  end.

Definition num_cols_nat : nat := 260.
Definition num_rows_nat : nat := 200.

Definition render_grid (ls : loop_state) : itree imguiE loop_state :=
  ok <- imgui_begin_table "grid" (int_of_nat (S num_cols_nat)) ;;
  if ok then
    imgui_table_setup_freeze 1 1 ;;
    imgui_table_setup_column "" 32 ;;
    setup_columns 0 num_cols_nat ;;
    imgui_table_headers_row ;;
    imgui_clipper_begin (int_of_nat num_rows_nat) ;;
    ls' <- clipper_loop 8 ls num_cols_nat ;;
    imgui_clipper_end ;;
    imgui_end_table ;;
    Ret ls'
  else
    Ret ls.

(* ----- Formula bar and menu bar --------------------------- *)

Definition render_formula_bar (ls : loop_state) : itree imguiE loop_state :=
  let label :=
    match ls_selected ls with
    | None => ""
    | Some r => cell_label r
    end in
  fbar_ref_label label ;;
  imgui_same_line ;;
  res <- imgui_input_text "##fbar" (ls_fbar_text ls) ;;
  let '(new_text, enter) := res in
  let ls1 := update_fbar ls new_text in
  Ret (if enter then do_commit ls1 else ls1).

Definition file_menu (ls : loop_state) : itree imguiE loop_state :=
  new_clicked <- imgui_menu_item "New" true ;;
  let ls0 := cond_apply new_clicked do_clear ls in
  save_clicked <- imgui_menu_item "Save" true ;;
  ls1 <- (if save_clicked then do_save ls0 else Ret ls0) ;;
  load_clicked <- imgui_menu_item "Open" true ;;
  ls2 <- (if load_clicked then do_load ls1 else Ret ls1) ;;
  Ret ls2.

Definition edit_menu (ls : loop_state) : itree imguiE loop_state :=
  u_clicked <- imgui_menu_item "Undo"
                 (negb (Nat.eqb (length (ls_undo ls)) 0)) ;;
  let ls_u := cond_apply u_clicked do_undo ls in
  r_clicked <- imgui_menu_item "Redo"
                 (negb (Nat.eqb (length (ls_redo ls_u)) 0)) ;;
  let ls_r := cond_apply r_clicked do_redo ls_u in
  let has_sel :=
    match ls_selected ls_r with Some _ => true | _ => false end in
  c_clicked <- imgui_menu_item "Copy" has_sel ;;
  _ <- (if c_clicked then do_copy ls_r else Ret tt) ;;
  v_clicked <- imgui_menu_item "Paste" has_sel ;;
  ls_p <- (if v_clicked then do_paste ls_r else Ret ls_r) ;;
  Ret ls_p.

Definition render_menu_bar (ls : loop_state) : itree imguiE loop_state :=
  open <- imgui_begin_menu_bar ;;
  if open then
    file_open <- imgui_begin_menu "File" ;;
    ls1 <- (if file_open then
              ls' <- file_menu ls ;; imgui_end_menu ;; Ret ls'
            else Ret ls) ;;
    edit_open <- imgui_begin_menu "Edit" ;;
    ls2 <- (if edit_open then
              ls'' <- edit_menu ls1 ;; imgui_end_menu ;; Ret ls''
            else Ret ls1) ;;
    imgui_end_menu_bar ;;
    Ret ls2
  else Ret ls.

Definition handle_shortcuts (ls : loop_state) : itree imguiE loop_state :=
  z <- ctrl_key_pressed "z" ;;
  let ls1 := cond_apply z do_undo ls in
  y <- ctrl_key_pressed "y" ;;
  let ls2 := cond_apply y do_redo ls1 in
  n <- ctrl_key_pressed "n" ;;
  let ls3 := cond_apply n do_clear ls2 in
  Ret ls3.

(* ----- Per-frame procedure -------------------------------- *)

Definition process_frame (ls : loop_state) : itree imguiE (bool * loop_state) :=
  glfw_poll_events ;;
  closing <- glfw_should_close ;;
  if closing then Ret (true, ls)
  else
    imgui_new_frame ;;
    imgui_full_viewport ;;
    imgui_next_window_menu_bar ;;
    imgui_begin_window "Rocqsheet" ;;
    ls1 <- render_menu_bar ls ;;
    ls2 <- render_formula_bar ls1 ;;
    imgui_separator ;;
    ls3 <- render_grid ls2 ;;
    imgui_end_window ;;
    ls4 <- handle_shortcuts ls3 ;;
    imgui_render_frame ;;
    Ret (false, ls4).

(* ----- Top-level loop ----------------------------------- *)

Axiom c_int : Type.
Axiom c_zero : c_int.
Crane Extract Inlined Constant c_int => "int".
Crane Extract Inlined Constant c_zero => "0".

CoFixpoint run_app (ls : loop_state) : itree imguiE c_int :=
  res <- process_frame ls ;;
  let '(quit, ls') := res in
  if quit then Ret c_zero
  else Tau (run_app ls').

Definition rocqsheet_run : itree imguiE c_int :=
  run_app initial_loop_state.

Crane Extraction "rocqsheet" rocqsheet_run smoke eval_cell
  parse_formula parse_int_literal.
