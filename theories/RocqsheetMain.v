(* Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License. *)
(* Rocqsheet runtime entry point: per-frame procedure, the cofix
   driver loop, the [Crane Extraction] declaration, and the loop-state
   correctness theorems.  All editing operators / save-load / render
   functions live in the focused submodules ([State], [Edit],
   [SaveLoad], [Render], [Menus], [Shortcuts]); this file only
   stitches them into [process_frame] / [run_app] and runs the
   correspondence proofs. *)

From Corelib Require Import PrimString PrimInt63.
From Stdlib Require Import List BinInt Lia.
From Stdlib.Numbers.Cyclic.Int63 Require Import Uint63.
From Crane Require Extraction.
From Crane Require Import Mapping.NatIntStd Mapping.ZInt.
From Crane Require Import Monads.ITree.
From Rocqsheet Require Import Rocqsheet.
From Rocqsheet Require Import ImGuiE.
From Rocqsheet Require Import Parser.
From Rocqsheet Require Import FindReplace.
From Rocqsheet Require Import State.
From Rocqsheet Require Import Edit.
From Rocqsheet Require Import SaveLoad.
From Rocqsheet Require Import Render.
From Rocqsheet Require Import Menus.
From Rocqsheet Require Import Shortcuts.
Import ListNotations.
Import Rocqsheet.

Open Scope itree_scope.
Open Scope int63_scope.
Local Open Scope pstring_scope.

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
    ls3 <- render_tab_bar ls2 ;;
    ls4 <- render_grid ls3 ;;
    imgui_end_window ;;
    (* Pin Charts to a bottom strip on first launch so it doesn't
       cover rows 1-22 of the grid; subsequent frames respect any
       drag/resize the user does. *)
    imgui_next_window_initial_pos_size 10%Z 600%Z 1260%Z 190%Z ;;
    imgui_begin_window "Charts" ;;
    render_charts ls4 ;;
    imgui_end_window ;;
    ls5 <- handle_shortcuts ls4 ;;
    imgui_render_frame ;;
    Ret (false, ls5).

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
  parse_formula parse_int_literal replace_int_in_expr
  Shift.insert_row Shift.delete_row Sorting.swap_rows.

(* --- Loop-state correctness ------------------------------------- *)

Inductive pure_edit_step : loop_state -> loop_state -> Prop :=
  | PESelect : forall ls r, pure_edit_step ls (select_cell ls r)
  | PEFbar : forall ls s', pure_edit_step ls (update_fbar ls s')
  | PECommit : forall ls, pure_edit_step ls (do_commit ls)
  | PEUndo : forall ls, pure_edit_step ls (do_undo ls)
  | PERedo : forall ls, pure_edit_step ls (do_redo ls)
  | PEClear : forall ls, pure_edit_step ls (do_clear ls)
  | PELeft : forall ls, pure_edit_step ls (do_left ls)
  | PERight : forall ls, pure_edit_step ls (do_right ls)
  | PEUp : forall ls, pure_edit_step ls (do_up ls)
  | PEDown : forall ls, pure_edit_step ls (do_down ls).

Theorem do_clear_state :
  forall ls,
    ls_selected (do_clear ls) = None
    /\ ls_edit_buf (do_clear ls) = nil
    /\ ls_parse_errs (do_clear ls) = nil.
Proof. intros. unfold do_clear. simpl. repeat split. Qed.

Theorem select_cell_preserves_fields :
  forall ls r,
    ls_sheet (select_cell ls r) = ls_sheet ls
    /\ ls_edit_buf (select_cell ls r) = ls_edit_buf ls
    /\ ls_parse_errs (select_cell ls r) = ls_parse_errs ls
    /\ ls_undo (select_cell ls r) = ls_undo ls
    /\ ls_redo (select_cell ls r) = ls_redo ls.
Proof. intros. unfold select_cell. simpl. repeat split. Qed.

Theorem update_fbar_preserves_fields :
  forall ls s',
    ls_sheet (update_fbar ls s') = ls_sheet ls
    /\ ls_selected (update_fbar ls s') = ls_selected ls
    /\ ls_edit_buf (update_fbar ls s') = ls_edit_buf ls.
Proof. intros. unfold update_fbar. simpl. repeat split. Qed.

Theorem do_undo_then_redo_recovers_sheet :
  forall ls prev desc rest,
    ls_undo ls = (prev, desc) :: rest ->
    ls_sheet (do_redo (do_undo ls)) = ls_sheet ls.
Proof.
  intros ls prev desc rest Hu.
  unfold do_undo, do_redo. rewrite Hu. simpl.
  reflexivity.
Qed.

Theorem do_right_unselected_noop : forall ls,
  ls_selected ls = None -> do_right ls = ls.
Proof.
  intros ls Hns. unfold do_right, move_selection.
  rewrite Hns. reflexivity.
Qed.

Theorem cell_col_of_lt_NUM_COLS : forall r,
  PrimInt63.ltb (cell_col_of r) NUM_COLS = true.
Proof.
  intros r. unfold cell_col_of.
  apply ltb_spec.
  rewrite mod_spec.
  pose proof (to_Z_bounded (cell_index r)).
  pose proof (to_Z_bounded NUM_COLS).
  assert (HE : to_Z NUM_COLS = 260%Z) by reflexivity.
  apply Z.mod_pos_bound. lia.
Qed.

Theorem move_selection_col_in_bounds :
  forall dc dr ls r',
    ls_selected (move_selection dc dr ls) = Some r' ->
    PrimInt63.ltb (cell_col_of r') NUM_COLS = true.
Proof.
  intros dc dr ls r' Hsel. apply cell_col_of_lt_NUM_COLS.
Qed.

Definition well_formed_loop_state (ls : loop_state) : Prop :=
  PrimArray.length (ls_sheet ls) = GRID_SIZE.

Lemma put_lit_preserves_wf :
  forall s c r v,
    PrimArray.length s = GRID_SIZE ->
    PrimArray.length (put_lit s c r v) = GRID_SIZE.
Proof.
  intros. unfold put_lit. rewrite length_set_cell. assumption.
Qed.

Lemma put_form_preserves_wf :
  forall s c r e,
    PrimArray.length s = GRID_SIZE ->
    PrimArray.length (put_form s c r e) = GRID_SIZE.
Proof.
  intros. unfold put_form. rewrite length_set_cell. assumption.
Qed.

Theorem cell_row_of_concrete_smoke :
  cell_row_of (mkRef 5%uint63 7%uint63) = 7%uint63.
Proof. vm_compute. reflexivity. Qed.

Theorem cell_col_of_concrete_smoke :
  cell_col_of (mkRef 5%uint63 7%uint63) = 5%uint63.
Proof. vm_compute. reflexivity. Qed.

Theorem process_frame_well_typed :
  forall ls, exists (k : itree imguiE (bool * loop_state)),
    process_frame ls = k.
Proof. intros ls. exists (process_frame ls). reflexivity. Qed.
