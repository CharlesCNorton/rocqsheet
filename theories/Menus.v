(* Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License. *)
(* File / Edit menu wiring + menu-bar dispatcher. *)

From Corelib Require Import PrimString PrimInt63.
From Stdlib Require Import List BinInt.
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
Local Open Scope pstring_scope.

Definition file_menu (ls : loop_state) : itree imguiE loop_state :=
  new_clicked <- imgui_menu_item "New" true ;;
  let ls0 := cond_apply new_clicked do_clear ls in
  save_clicked <- imgui_menu_item "Save" true ;;
  ls1 <- (if save_clicked then do_save ls0 else Ret ls0) ;;
  save_as_clicked <- imgui_menu_item "Save As (formula bar = path)" true ;;
  ls1a <- (if save_as_clicked then do_save_as ls1 else Ret ls1) ;;
  load_clicked <- imgui_menu_item "Open" true ;;
  ls2 <- (if load_clicked then do_load ls1a else Ret ls1a) ;;
  pdf_clicked <- imgui_menu_item "Export to PDF" true ;;
  ls3 <- (if pdf_clicked then do_pdf_export ls2 else Ret ls2) ;;
  Ret ls3.

Definition edit_menu (ls : loop_state) : itree imguiE loop_state :=
  let undo_label :=
    if Nat.eqb (length (ls_undo ls)) 0 then "Undo"%pstring
    else PrimString.cat "Undo: "%pstring (next_undo_desc ls) in
  u_clicked <- imgui_menu_item undo_label
                 (negb (Nat.eqb (length (ls_undo ls)) 0)) ;;
  let ls_u := cond_apply u_clicked do_undo ls in
  let redo_label :=
    if Nat.eqb (length (ls_redo ls_u)) 0 then "Redo"%pstring
    else PrimString.cat "Redo: "%pstring (next_redo_desc ls_u) in
  r_clicked <- imgui_menu_item redo_label
                 (negb (Nat.eqb (length (ls_redo ls_u)) 0)) ;;
  let ls_r := cond_apply r_clicked do_redo ls_u in
  let has_sel :=
    match ls_selected ls_r with Some _ => true | _ => false end in
  c_clicked <- imgui_menu_item "Copy" has_sel ;;
  _ <- (if c_clicked then do_copy ls_r else Ret tt) ;;
  v_clicked <- imgui_menu_item "Paste" has_sel ;;
  ls_p <- (if v_clicked then do_paste ls_r else Ret ls_r) ;;
  ins_clicked <- imgui_menu_item "Insert Row" has_sel ;;
  let ls_i := cond_apply ins_clicked do_insert_row ls_p in
  del_clicked <- imgui_menu_item "Delete Row" has_sel ;;
  let ls_d := cond_apply del_clicked do_delete_row ls_i in
  swp_clicked <- imgui_menu_item "Swap With Row Below" has_sel ;;
  let ls_s := cond_apply swp_clicked do_swap_with_next_row ls_d in
  mrg_clicked <- imgui_menu_item "Merge Cell Right" has_sel ;;
  let ls_m := cond_apply mrg_clicked do_merge_right ls_s in
  rep_clicked <- imgui_menu_item "Replace (formula bar = FROM|TO)" true ;;
  let ls_x := cond_apply rep_clicked do_replace_user ls_m in
  Ret ls_x.

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
