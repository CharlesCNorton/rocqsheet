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
  h <- ctrl_key_pressed "h" ;;
  let ls12 := cond_apply h do_replace_user ls11 in
  p <- ctrl_key_pressed "p" ;;
  ls13 <- (if p then do_pdf_export ls12 else Ret ls12) ;;
  shift_s <- ctrl_shift_key_pressed "s" ;;
  ls14 <- (if shift_s then do_save_as ls13 else Ret ls13) ;;
  Ret ls14.
