(* Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License. *)
(* Cursor movement and keyboard-shortcut dispatch. *)

From Corelib Require Import PrimString PrimInt63.
From Stdlib Require Import List BinInt.
From Stdlib.Numbers.Cyclic.Int63 Require Import Uint63.
From Crane Require Extraction.
From Crane Require Import Mapping.NatIntStd Mapping.ZInt.
From Crane Require Import Monads.ITree.
From Rocqsheet Require Import Rocqsheet.
From Rocqsheet Require Import ImGuiE.
From Rocqsheet Require Import State.
From Rocqsheet Require Import Edit.
From Rocqsheet Require Import SaveLoad.
From Rocqsheet Require Import Render.
Import ListNotations.
Import Rocqsheet.

Open Scope itree_scope.
Open Scope int63_scope.
Local Open Scope pstring_scope.

Definition move_selection (dc dr : int) (ls : loop_state) : loop_state :=
  match ls_selected ls with
  | None => ls
  | Some r =>
    let new_c :=
      let c1 := PrimInt63.add (cell_col_of r) dc in
      if PrimInt63.ltb c1 0 then 0
      else if PrimInt63.leb (int_of_nat num_cols_nat) c1
      then PrimInt63.sub (int_of_nat num_cols_nat) 1
      else c1 in
    let new_r :=
      let r1 := PrimInt63.add (cell_row_of r) dr in
      if PrimInt63.ltb r1 0 then 0
      else if PrimInt63.leb (int_of_nat num_rows_nat) r1
      then PrimInt63.sub (int_of_nat num_rows_nat) 1
      else r1 in
    select_cell ls (mkRef new_c new_r)
  end.

Definition do_left  (ls : loop_state) : loop_state :=
  move_selection (PrimInt63.sub 0 1) 0 ls.
Definition do_right (ls : loop_state) : loop_state :=
  move_selection 1 0 ls.
Definition do_up    (ls : loop_state) : loop_state :=
  move_selection 0 (PrimInt63.sub 0 1) ls.
Definition do_down  (ls : loop_state) : loop_state :=
  move_selection 0 1 ls.

(* PageUp / PageDown move 25 rows at a time. *)
Definition do_page_up (ls : loop_state) : loop_state :=
  move_selection 0 (PrimInt63.sub 0 25) ls.
Definition do_page_down (ls : loop_state) : loop_state :=
  move_selection 0 25 ls.

(* Home moves to column 0 of the current row. *)
Definition do_home (ls : loop_state) : loop_state :=
  match ls_selected ls with
  | None => ls
  | Some r => select_cell ls (mkRef 0 (cell_row_of r))
  end.

(* End moves to the last non-empty column of the current row.  Falls
   back to column 0 when the entire row is empty. *)
Fixpoint last_nonempty_in_row
    (s : Sheet) (row col : int) (fuel : nat) (best : int) : int :=
  match fuel with
  | O => best
  | S fuel' =>
    if PrimInt63.leb (int_of_nat num_cols_nat) col then best
    else
      let cell := get_cell s (mkRef col row) in
      let best' :=
        match cell with
        | CEmpty => best
        | _ => col
        end in
      last_nonempty_in_row s row (PrimInt63.add col 1) fuel' best'
  end.

Definition do_end (ls : loop_state) : loop_state :=
  match ls_selected ls with
  | None => ls
  | Some r =>
    let row := cell_row_of r in
    let last := last_nonempty_in_row (ls_sheet ls) row 0 270 0 in
    select_cell ls (mkRef last row)
  end.

(* Ctrl+arrow jumps to the next non-empty cell in the direction,
   stopping at the grid edge.  Empty cells are stepped over. *)
Fixpoint scan_until_nonempty
    (s : Sheet) (col row dc dr : int) (fuel : nat) : int * int :=
  match fuel with
  | O => (col, row)
  | S fuel' =>
    let nc := PrimInt63.add col dc in
    let nr := PrimInt63.add row dr in
    if PrimInt63.ltb nc 0 then (col, row)
    else if PrimInt63.leb (int_of_nat num_cols_nat) nc then (col, row)
    else if PrimInt63.ltb nr 0 then (col, row)
    else if PrimInt63.leb (int_of_nat num_rows_nat) nr then (col, row)
    else
      match get_cell s (mkRef nc nr) with
      | CEmpty => scan_until_nonempty s nc nr dc dr fuel'
      | _ => (nc, nr)
      end
  end.

Definition do_ctrl_arrow (dc dr : int) (ls : loop_state) : loop_state :=
  match ls_selected ls with
  | None => ls
  | Some r =>
    let '(nc, nr) :=
      scan_until_nonempty (ls_sheet ls) (cell_col_of r) (cell_row_of r)
                          dc dr 300 in
    select_cell ls (mkRef nc nr)
  end.

Definition do_ctrl_up    : loop_state -> loop_state :=
  do_ctrl_arrow 0 (PrimInt63.sub 0 1).
Definition do_ctrl_down  : loop_state -> loop_state := do_ctrl_arrow 0 1.
Definition do_ctrl_left  : loop_state -> loop_state :=
  do_ctrl_arrow (PrimInt63.sub 0 1) 0.
Definition do_ctrl_right : loop_state -> loop_state := do_ctrl_arrow 1 0.

(* Delete clears the selected cell without writing to clipboard. *)
Definition do_clear_cell (ls : loop_state) : loop_state :=
  match ls_selected ls with
  | None => ls
  | Some r => commit_to ls r ""
  end.

(* Ctrl+X cuts: copy to OS clipboard, then clear. *)
Definition do_cut (ls : loop_state) : itree imguiE loop_state :=
  match ls_selected ls with
  | None => Ret ls
  | Some r =>
    _ <- clipboard_set (fbar_for_cell (ls_edit_buf ls) (ls_sheet ls) r) ;;
    Ret (commit_to ls r "")
  end.

(* Item 68: toggle Show Formulas render mode. *)
Definition do_toggle_show_formulas (ls : loop_state) : loop_state :=
  mkLoop (ls_sheet ls) (ls_selected ls) (ls_fbar_text ls)
         (ls_edit_buf ls) (ls_parse_errs ls)
         (ls_undo ls) (ls_redo ls) (ls_formats ls)
         (ls_other_sheets ls) (ls_active ls) (ls_charts ls)
         (ls_merges ls) (ls_sheet_names ls)
         (negb (ls_show_formulas ls)) (ls_zoom ls) (ls_auto_recalc ls) (ls_dirty ls).

(* Item 73: toggle Auto-Recalc. *)
Definition do_toggle_auto_recalc (ls : loop_state) : loop_state :=
  mkLoop (ls_sheet ls) (ls_selected ls) (ls_fbar_text ls)
         (ls_edit_buf ls) (ls_parse_errs ls)
         (ls_undo ls) (ls_redo ls) (ls_formats ls)
         (ls_other_sheets ls) (ls_active ls) (ls_charts ls)
         (ls_merges ls) (ls_sheet_names ls)
         (ls_show_formulas ls) (ls_zoom ls) (negb (ls_auto_recalc ls))
         (ls_dirty ls).

(* Item 60: zoom helpers.  Clamp to [50, 300] in steps of 10. *)
Definition zoom_min : Z := 50%Z.
Definition zoom_max : Z := 300%Z.
Definition zoom_step : Z := 10%Z.

Definition clamp_zoom (z : Z) : Z :=
  if Z.ltb z zoom_min then zoom_min
  else if Z.ltb zoom_max z then zoom_max
  else z.

Definition do_zoom_in (ls : loop_state) : loop_state :=
  mkLoop (ls_sheet ls) (ls_selected ls) (ls_fbar_text ls)
         (ls_edit_buf ls) (ls_parse_errs ls)
         (ls_undo ls) (ls_redo ls) (ls_formats ls)
         (ls_other_sheets ls) (ls_active ls) (ls_charts ls)
         (ls_merges ls) (ls_sheet_names ls)
         (ls_show_formulas ls)
         (clamp_zoom (Z.add (ls_zoom ls) zoom_step))
         (ls_auto_recalc ls) (ls_dirty ls).

Definition do_zoom_out (ls : loop_state) : loop_state :=
  mkLoop (ls_sheet ls) (ls_selected ls) (ls_fbar_text ls)
         (ls_edit_buf ls) (ls_parse_errs ls)
         (ls_undo ls) (ls_redo ls) (ls_formats ls)
         (ls_other_sheets ls) (ls_active ls) (ls_charts ls)
         (ls_merges ls) (ls_sheet_names ls)
         (ls_show_formulas ls)
         (clamp_zoom (Z.sub (ls_zoom ls) zoom_step))
         (ls_auto_recalc ls) (ls_dirty ls).

Definition do_zoom_reset (ls : loop_state) : loop_state :=
  mkLoop (ls_sheet ls) (ls_selected ls) (ls_fbar_text ls)
         (ls_edit_buf ls) (ls_parse_errs ls)
         (ls_undo ls) (ls_redo ls) (ls_formats ls)
         (ls_other_sheets ls) (ls_active ls) (ls_charts ls)
         (ls_merges ls) (ls_sheet_names ls)
         (ls_show_formulas ls) 100%Z (ls_auto_recalc ls) (ls_dirty ls).

(* Item 53 (Tab half) helper: commit the current edit, then advance
   the selection one column right.  See [handle_shortcuts] below. *)
Definition tab_commit_advance (ls : loop_state) : loop_state :=
  advance_after_tab (do_commit ls).

Definition handle_shortcuts (ls : loop_state) : itree imguiE loop_state :=
  z <- ctrl_key_pressed "z" ;;
  let ls1 := cond_apply z do_undo ls in
  y <- ctrl_key_pressed "y" ;;
  let ls2 := cond_apply y do_redo ls1 in
  n <- ctrl_key_pressed "n" ;;
  let ls3 := cond_apply n do_clear ls2 in
  up <- key_pressed "Up" ;;
  let ls4 := cond_apply up do_up ls3 in
  dn <- key_pressed "Down" ;;
  let ls5 := cond_apply dn do_down ls4 in
  lf <- key_pressed "Left" ;;
  let ls6 := cond_apply lf do_left ls5 in
  rt <- key_pressed "Right" ;;
  let ls7 := cond_apply rt do_right ls6 in
  i <- ctrl_key_pressed "i" ;;
  let ls8 := cond_apply i do_insert_row ls7 in
  d <- ctrl_key_pressed "d" ;;
  let ls9 := cond_apply d do_delete_row ls8 in
  t <- ctrl_key_pressed "t" ;;
  let ls10 := cond_apply t do_swap_with_next_row ls9 in
  m <- ctrl_key_pressed "m" ;;
  let ls11 := cond_apply m do_merge_right ls10 in
  (* Item 39: Ctrl+H opens the Find / Replace modal; the per-frame
     modal pump in process_frame applies the committed pair. *)
  h <- ctrl_key_pressed "h" ;;
  (if h then modal_open "Find / Replace" else Ret tt) ;;
  let ls12 := ls11 in
  p <- ctrl_key_pressed "p" ;;
  ls13 <- (if p then do_pdf_export ls12 else Ret ls12) ;;
  shift_s <- ctrl_shift_key_pressed "s" ;;
  ls14 <- (if shift_s then do_save_as ls13 else Ret ls13) ;;
  (* Item 64 — Home / End / PageUp / PageDown. *)
  pu <- key_pressed "PageUp" ;;
  let ls15 := cond_apply pu do_page_up ls14 in
  pd <- key_pressed "PageDown" ;;
  let ls16 := cond_apply pd do_page_down ls15 in
  hk <- key_pressed "Home" ;;
  let ls17 := cond_apply hk do_home ls16 in
  ek <- key_pressed "End" ;;
  let ls18 := cond_apply ek do_end ls17 in
  (* Item 62 — Ctrl+arrow jumps to next non-empty cell. *)
  cu <- ctrl_arrow_pressed "Up" ;;
  let ls19 := cond_apply cu do_ctrl_up ls18 in
  cd <- ctrl_arrow_pressed "Down" ;;
  let ls20 := cond_apply cd do_ctrl_down ls19 in
  cl <- ctrl_arrow_pressed "Left" ;;
  let ls21 := cond_apply cl do_ctrl_left ls20 in
  cr <- ctrl_arrow_pressed "Right" ;;
  let ls22 := cond_apply cr do_ctrl_right ls21 in
  (* Item 73 — Delete clears the selected cell; Ctrl+X copies then clears. *)
  del <- key_pressed "Delete" ;;
  let ls23 := cond_apply del do_clear_cell ls22 in
  x <- ctrl_key_pressed "x" ;;
  ls24 <- (if x then do_cut ls23 else Ret ls23) ;;
  (* Item 68 — Ctrl+` toggles Show Formulas mode. *)
  tilde <- ctrl_key_pressed "`" ;;
  let ls25 := cond_apply tilde do_toggle_show_formulas ls24 in
  (* Item 60 — Ctrl+= zoom in, Ctrl+- zoom out, Ctrl+0 reset. *)
  zin <- ctrl_key_pressed "=" ;;
  let ls26 := cond_apply zin do_zoom_in ls25 in
  zout <- ctrl_key_pressed "-" ;;
  let ls27 := cond_apply zout do_zoom_out ls26 in
  zres <- ctrl_key_pressed "0" ;;
  let ls28 := cond_apply zres do_zoom_reset ls27 in
  (* Item 53 (Tab half) — commit, then move selection one column right.
     Wrapped as one pure step so cond_apply can hand the extracted
     C++ a function pointer (loop_state has no default ctor, so a raw
     [if .. then .. else ..] won't extract cleanly). *)
  tab <- key_pressed "Tab" ;;
  let ls29 := cond_apply tab tab_commit_advance ls28 in
  (* Item 61 — Ctrl+Shift+I inserts a column, Ctrl+Shift+D deletes one. *)
  ins_col <- ctrl_shift_key_pressed "i" ;;
  let ls30 := cond_apply ins_col do_insert_col ls29 in
  del_col <- ctrl_shift_key_pressed "d" ;;
  let ls31 := cond_apply del_col do_delete_col ls30 in
  Ret ls31.
