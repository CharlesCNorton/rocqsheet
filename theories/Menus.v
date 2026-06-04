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
From Rocqsheet Require Import Shortcuts.
Import ListNotations.
Import Rocqsheet.

Open Scope itree_scope.
Local Open Scope pstring_scope.

(* Item 86: walk the recent-paths list and render one menu item per
   entry, dispatching to [do_load_recent] on click. *)
Fixpoint recent_menu_items
    (ls : loop_state) (xs : list PrimString.string)
  : itree imguiE loop_state :=
  match xs with
  | nil => Ret ls
  | p :: rest =>
    clicked <- imgui_menu_item p true ;;
    ls' <- (if clicked then do_load_recent ls p else Ret ls) ;;
    recent_menu_items ls' rest
  end.

Definition file_menu (ls : loop_state) : itree imguiE loop_state :=
  new_clicked <- imgui_menu_item "New" true ;;
  let ls0 := cond_apply new_clicked do_clear ls in
  save_clicked <- imgui_menu_item "Save" true ;;
  ls1 <- (if save_clicked then do_save ls0 else Ret ls0) ;;
  save_as_clicked <- imgui_menu_item "Save As (formula bar = path)" true ;;
  ls1a <- (if save_as_clicked then do_save_as ls1 else Ret ls1) ;;
  load_clicked <- imgui_menu_item "Open" true ;;
  ls2 <- (if load_clicked then do_load ls1a else Ret ls1a) ;;
  (* Open Recent submenu. *)
  recent_open <- imgui_begin_menu "Open Recent" ;;
  ls2a <- (if recent_open then
             paths <- recent_list ;;
             ls' <- recent_menu_items ls2 paths ;;
             imgui_end_menu ;;
             Ret ls'
           else Ret ls2) ;;
  (* Item 4: CSV import at the selected anchor. *)
  import_csv_clicked <- imgui_menu_item
    "Import CSV (formula bar = path)" true ;;
  ls2b <- (if import_csv_clicked then do_import_csv ls2a else Ret ls2a) ;;
  pdf_clicked <- imgui_menu_item "Export to PDF" true ;;
  ls3 <- (if pdf_clicked then do_pdf_export ls2b else Ret ls2b) ;;
  csv_clicked <- imgui_menu_item "Export to CSV (formula bar = path)" true ;;
  ls4 <- (if csv_clicked then do_export_csv ls3 else Ret ls3) ;;
  html_clicked <- imgui_menu_item "Export to HTML (formula bar = path)" true ;;
  ls5 <- (if html_clicked then do_export_html ls4 else Ret ls4) ;;
  Ret ls5.

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
  ins_col_clicked <- imgui_menu_item "Insert Column" has_sel ;;
  let ls_ic := cond_apply ins_col_clicked do_insert_col ls_d in
  del_col_clicked <- imgui_menu_item "Delete Column" has_sel ;;
  let ls_dc := cond_apply del_col_clicked do_delete_col ls_ic in
  swp_clicked <- imgui_menu_item "Swap With Row Below" has_sel ;;
  let ls_s := cond_apply swp_clicked do_swap_with_next_row ls_dc in
  mrg_clicked <- imgui_menu_item "Merge Cell Right" has_sel ;;
  let ls_m := cond_apply mrg_clicked do_merge_right ls_s in
  (* Item 39: the menu entry opens the Find / Replace modal; the
     per-frame modal pump applies the committed pair. *)
  rep_clicked <- imgui_menu_item "Find / Replace... (Ctrl+H)" true ;;
  (if rep_clicked then modal_open "Find / Replace" else Ret tt) ;;
  Ret ls_m.

(* View menu: Show Formulas + Auto-Recalc toggles, Zoom controls.
   Implements item 60 (Zoom) + item 68 (Show Formulas) +
   item 73 (Auto-Recalc) at the menu level. *)
Definition view_menu (ls : loop_state) : itree imguiE loop_state :=
  let sf_label :=
    if ls_show_formulas ls
    then "[x] Show Formulas (Ctrl+`)"%pstring
    else "[ ] Show Formulas (Ctrl+`)"%pstring in
  sf_clicked <- imgui_menu_item sf_label true ;;
  let ls1 := cond_apply sf_clicked do_toggle_show_formulas ls in
  let ar_label :=
    if ls_auto_recalc ls1
    then "[x] Auto-Recalc"%pstring
    else "[ ] Auto-Recalc"%pstring in
  ar_clicked <- imgui_menu_item ar_label true ;;
  let ls2 := cond_apply ar_clicked do_toggle_auto_recalc ls1 in
  let z_label :=
    PrimString.cat "Zoom: "%pstring
      (PrimString.cat (string_of_z (ls_zoom ls2)) "%"%pstring) in
  _ <- imgui_menu_item z_label false ;;
  zi_clicked <- imgui_menu_item "Zoom In  (Ctrl+=)"%pstring true ;;
  let ls3 := cond_apply zi_clicked do_zoom_in ls2 in
  zo_clicked <- imgui_menu_item "Zoom Out (Ctrl+-)"%pstring true ;;
  let ls4 := cond_apply zo_clicked do_zoom_out ls3 in
  zr_clicked <- imgui_menu_item "Reset Zoom (Ctrl+0)"%pstring true ;;
  let ls5 := cond_apply zr_clicked do_zoom_reset ls4 in
  Ret ls5.

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
    view_open <- imgui_begin_menu "View" ;;
    ls3 <- (if view_open then
              ls''' <- view_menu ls2 ;; imgui_end_menu ;; Ret ls'''
            else Ret ls2) ;;
    imgui_end_menu_bar ;;
    Ret ls3
  else Ret ls.
