(* Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License. *)
(* Effect interface for the ImGui front-end.  Each constructor of
   [imguiE] corresponds one-to-one with a function in
   [src/imgui_helpers.h]. *)

From Corelib Require Import PrimString PrimInt63.
From Stdlib Require Import BinInt.
From Crane Require Extraction.
From Crane Require Import Mapping.NatIntStd Mapping.ZInt.
From Crane Require Import Monads.ITree.

Open Scope itree_scope.

(* Outcome of a cell selectable for one frame. *)
Inductive cell_event : Type :=
  | CellNone
  | CellSelected
  | CellDoubleClicked.

Inductive imguiE : Type -> Type :=
  | EShouldClose      : imguiE bool
  | EPollEvents       : imguiE unit
  | ENewFrame         : imguiE unit
  | ERenderFrame      : imguiE unit
  | EFullViewport     : imguiE unit
  | EBeginWindow      : PrimString.string -> imguiE unit
  | EEndWindow        : imguiE unit
  | EText             : PrimString.string -> imguiE unit
  | ETextErr          : PrimString.string -> imguiE unit
  | ESeparator        : imguiE unit
  | EBeginTable       : PrimString.string -> int -> imguiE bool
  | EEndTable         : imguiE unit
  | ETableSetupFreeze : int -> int -> imguiE unit
  | ETableSetupColumn : PrimString.string -> int -> imguiE unit
  | ETableHeadersRow  : imguiE unit
  | ETableNextRow     : imguiE unit
  | ETableSetCol      : int -> imguiE unit
  | EClipperBegin     : int -> imguiE unit
  | EClipperStep      : imguiE bool
  | EClipperGetStart  : imguiE int
  | EClipperGetEnd    : imguiE int
  | EClipperEnd       : imguiE unit
  | ESelectable       : int -> int -> bool -> bool -> PrimString.string ->
                        imguiE cell_event
  (* Same as ESelectable plus formatting: bold, packed RGB foreground
     colour, border, alignment encoded as Z (0=left,1=center,2=right). *)
  | ESelectableFmt    : int -> int -> bool -> bool -> PrimString.string ->
                        bool -> Z -> bool -> Z -> imguiE cell_event
  (* InputText returns (current_buffer, enter_pressed). *)
  | EInputText        : PrimString.string -> PrimString.string ->
                        imguiE (PrimString.string * bool)
  | EBeginMenuBar     : imguiE bool
  | EEndMenuBar       : imguiE unit
  | EBeginMenu        : PrimString.string -> imguiE bool
  | EEndMenu          : imguiE unit
  | EMenuItem         : PrimString.string -> bool -> imguiE bool
  (* Sets the next-window flag so the upcoming begin_window opens
     a menu-bar-enabled window. *)
  | ENextWindowMenuBar : imguiE unit
  | EFileRead         : PrimString.string -> imguiE (PrimString.string * bool)
  | EFileWrite        : PrimString.string -> PrimString.string -> imguiE bool
  | EClipboardGet     : imguiE PrimString.string
  | EClipboardSet     : PrimString.string -> imguiE unit
  | ECtrlKeyPressed   : PrimString.string -> imguiE bool
  | EKeyPressed       : PrimString.string -> imguiE bool
  | ESameLine         : imguiE unit
  | EFbarRefLabel     : PrimString.string -> imguiE unit
  (* Renders a tab bar with [num] tabs labelled "Sheet 1".."Sheet N".
     Returns the active tab index (the one whose body is currently
     displayed by ImGui).  [current] is supplied for future programmatic
     switching but is not yet honoured by the helper. *)
  | ETabBarSelect     : PrimString.string -> int -> int -> imguiE int.

(* Smart constructors. *)
Definition glfw_should_close : itree imguiE bool := trigger EShouldClose.
Definition glfw_poll_events : itree imguiE unit := trigger EPollEvents.
Definition imgui_new_frame : itree imguiE unit := trigger ENewFrame.
Definition imgui_render_frame : itree imguiE unit := trigger ERenderFrame.
Definition imgui_full_viewport : itree imguiE unit := trigger EFullViewport.
Definition imgui_begin_window (name : PrimString.string) : itree imguiE unit :=
  trigger (EBeginWindow name).
Definition imgui_end_window : itree imguiE unit := trigger EEndWindow.
Definition imgui_text (s : PrimString.string) : itree imguiE unit :=
  trigger (EText s).
Definition imgui_text_err (s : PrimString.string) : itree imguiE unit :=
  trigger (ETextErr s).
Definition imgui_separator : itree imguiE unit := trigger ESeparator.
Definition imgui_begin_table (id : PrimString.string) (cols : int)
  : itree imguiE bool := trigger (EBeginTable id cols).
Definition imgui_end_table : itree imguiE unit := trigger EEndTable.
Definition imgui_table_setup_freeze (cols rows : int) : itree imguiE unit :=
  trigger (ETableSetupFreeze cols rows).
Definition imgui_table_setup_column (label : PrimString.string) (width : int)
  : itree imguiE unit := trigger (ETableSetupColumn label width).
Definition imgui_table_headers_row : itree imguiE unit :=
  trigger ETableHeadersRow.
Definition imgui_table_next_row : itree imguiE unit :=
  trigger ETableNextRow.
Definition imgui_table_set_column_index (i : int) : itree imguiE unit :=
  trigger (ETableSetCol i).
Definition imgui_clipper_begin (n : int) : itree imguiE unit :=
  trigger (EClipperBegin n).
Definition imgui_clipper_step : itree imguiE bool := trigger EClipperStep.
Definition imgui_clipper_get_start : itree imguiE int := trigger EClipperGetStart.
Definition imgui_clipper_get_end : itree imguiE int := trigger EClipperGetEnd.
Definition imgui_clipper_end : itree imguiE unit := trigger EClipperEnd.
Definition imgui_selectable_cell
    (c r : int) (selected : bool) (is_error : bool)
    (display : PrimString.string)
  : itree imguiE cell_event :=
  trigger (ESelectable c r selected is_error display).
Definition imgui_selectable_cell_fmt
    (c r : int) (selected : bool) (is_error : bool)
    (display : PrimString.string)
    (bold : bool) (color_rgb : Z) (border : bool) (align : Z)
  : itree imguiE cell_event :=
  trigger (ESelectableFmt c r selected is_error display
                          bold color_rgb border align).
Definition imgui_input_text (id : PrimString.string) (cur : PrimString.string)
  : itree imguiE (PrimString.string * bool) :=
  trigger (EInputText id cur).
Definition imgui_begin_menu_bar : itree imguiE bool := trigger EBeginMenuBar.
Definition imgui_end_menu_bar : itree imguiE unit := trigger EEndMenuBar.
Definition imgui_begin_menu (label : PrimString.string) : itree imguiE bool :=
  trigger (EBeginMenu label).
Definition imgui_end_menu : itree imguiE unit := trigger EEndMenu.
Definition imgui_menu_item (label : PrimString.string) (enabled : bool)
  : itree imguiE bool := trigger (EMenuItem label enabled).
Definition imgui_next_window_menu_bar : itree imguiE unit :=
  trigger ENextWindowMenuBar.
Definition file_read (path : PrimString.string)
  : itree imguiE (PrimString.string * bool) := trigger (EFileRead path).
Definition file_write (path : PrimString.string) (content : PrimString.string)
  : itree imguiE bool := trigger (EFileWrite path content).
Definition clipboard_get : itree imguiE PrimString.string :=
  trigger EClipboardGet.
Definition clipboard_set (s : PrimString.string) : itree imguiE unit :=
  trigger (EClipboardSet s).
Definition ctrl_key_pressed (k : PrimString.string) : itree imguiE bool :=
  trigger (ECtrlKeyPressed k).
Definition key_pressed (k : PrimString.string) : itree imguiE bool :=
  trigger (EKeyPressed k).
Definition imgui_same_line : itree imguiE unit := trigger ESameLine.
Definition fbar_ref_label (s : PrimString.string) : itree imguiE unit :=
  trigger (EFbarRefLabel s).
Definition imgui_tab_bar_select (id : PrimString.string) (num current : int)
  : itree imguiE int := trigger (ETabBarSelect id num current).

(* Erased-itree extraction: each constructor inlines to its C++
   helper at the call site; the inductive itself maps to the empty
   string and disappears. *)
Crane Extract Inductive cell_event =>
  "imgui_helpers::cell_event"
  [ "imgui_helpers::cell_event::None"
    "imgui_helpers::cell_event::Selected"
    "imgui_helpers::cell_event::DoubleClicked" ]
  "switch (%scrut) { case imgui_helpers::cell_event::None: { %br0 } break; case imgui_helpers::cell_event::Selected: { %br1 } break; default: { %br2 } break; }"
  From "imgui_helpers.h".

Crane Extract Inductive imguiE => ""
  [ "imgui_helpers::should_close()"
    "imgui_helpers::poll_events()"
    "imgui_helpers::new_frame()"
    "imgui_helpers::render_frame()"
    "imgui_helpers::full_viewport()"
    "imgui_helpers::begin_window(%a0)"
    "imgui_helpers::end_window()"
    "imgui_helpers::text(%a0)"
    "imgui_helpers::text_err(%a0)"
    "imgui_helpers::separator()"
    "imgui_helpers::begin_table(%a0, %a1)"
    "imgui_helpers::end_table()"
    "imgui_helpers::table_setup_freeze(%a0, %a1)"
    "imgui_helpers::table_setup_column(%a0, %a1)"
    "imgui_helpers::table_headers_row()"
    "imgui_helpers::table_next_row()"
    "imgui_helpers::table_set_column_index(%a0)"
    "imgui_helpers::clipper_begin(%a0)"
    "imgui_helpers::clipper_step()"
    "imgui_helpers::clipper_get_start()"
    "imgui_helpers::clipper_get_end()"
    "imgui_helpers::clipper_end()"
    "imgui_helpers::selectable_cell(%a0, %a1, %a2, %a3, %a4)"
    "imgui_helpers::selectable_cell_formatted(%a0, %a1, %a2, %a3, %a4, %a5, %a6, %a7, %a8)"
    "imgui_helpers::input_text(%a0, %a1)"
    "imgui_helpers::begin_menu_bar()"
    "imgui_helpers::end_menu_bar()"
    "imgui_helpers::begin_menu(%a0)"
    "imgui_helpers::end_menu()"
    "imgui_helpers::menu_item(%a0, %a1)"
    "imgui_helpers::next_window_menu_bar()"
    "imgui_helpers::file_read(%a0)"
    "imgui_helpers::file_write(%a0, %a1)"
    "imgui_helpers::clipboard_get()"
    "imgui_helpers::clipboard_set(%a0)"
    "imgui_helpers::ctrl_key_pressed(%a0)"
    "imgui_helpers::key_pressed(%a0)"
    "imgui_helpers::same_line()"
    "imgui_helpers::fbar_ref_label(%a0)"
    "imgui_helpers::tab_bar_select(%a0, %a1, %a2)" ]
  From "imgui_helpers.h".

Crane Extract Inlined Constant glfw_should_close =>
  "imgui_helpers::should_close()" From "imgui_helpers.h".
Crane Extract Inlined Constant glfw_poll_events =>
  "imgui_helpers::poll_events()" From "imgui_helpers.h".
Crane Extract Inlined Constant imgui_new_frame =>
  "imgui_helpers::new_frame()" From "imgui_helpers.h".
Crane Extract Inlined Constant imgui_render_frame =>
  "imgui_helpers::render_frame()" From "imgui_helpers.h".
Crane Extract Inlined Constant imgui_full_viewport =>
  "imgui_helpers::full_viewport()" From "imgui_helpers.h".
Crane Extract Inlined Constant imgui_begin_window =>
  "imgui_helpers::begin_window(%a0)" From "imgui_helpers.h".
Crane Extract Inlined Constant imgui_end_window =>
  "imgui_helpers::end_window()" From "imgui_helpers.h".
Crane Extract Inlined Constant imgui_text =>
  "imgui_helpers::text(%a0)" From "imgui_helpers.h".
Crane Extract Inlined Constant imgui_text_err =>
  "imgui_helpers::text_err(%a0)" From "imgui_helpers.h".
Crane Extract Inlined Constant imgui_separator =>
  "imgui_helpers::separator()" From "imgui_helpers.h".
Crane Extract Inlined Constant imgui_begin_table =>
  "imgui_helpers::begin_table(%a0, %a1)" From "imgui_helpers.h".
Crane Extract Inlined Constant imgui_end_table =>
  "imgui_helpers::end_table()" From "imgui_helpers.h".
Crane Extract Inlined Constant imgui_table_setup_freeze =>
  "imgui_helpers::table_setup_freeze(%a0, %a1)" From "imgui_helpers.h".
Crane Extract Inlined Constant imgui_table_setup_column =>
  "imgui_helpers::table_setup_column(%a0, %a1)" From "imgui_helpers.h".
Crane Extract Inlined Constant imgui_table_headers_row =>
  "imgui_helpers::table_headers_row()" From "imgui_helpers.h".
Crane Extract Inlined Constant imgui_table_next_row =>
  "imgui_helpers::table_next_row()" From "imgui_helpers.h".
Crane Extract Inlined Constant imgui_table_set_column_index =>
  "imgui_helpers::table_set_column_index(%a0)" From "imgui_helpers.h".
Crane Extract Inlined Constant imgui_clipper_begin =>
  "imgui_helpers::clipper_begin(%a0)" From "imgui_helpers.h".
Crane Extract Inlined Constant imgui_clipper_step =>
  "imgui_helpers::clipper_step()" From "imgui_helpers.h".
Crane Extract Inlined Constant imgui_clipper_get_start =>
  "imgui_helpers::clipper_get_start()" From "imgui_helpers.h".
Crane Extract Inlined Constant imgui_clipper_get_end =>
  "imgui_helpers::clipper_get_end()" From "imgui_helpers.h".
Crane Extract Inlined Constant imgui_clipper_end =>
  "imgui_helpers::clipper_end()" From "imgui_helpers.h".
Crane Extract Inlined Constant imgui_selectable_cell =>
  "imgui_helpers::selectable_cell(%a0, %a1, %a2, %a3, %a4)" From "imgui_helpers.h".
Crane Extract Inlined Constant imgui_selectable_cell_fmt =>
  "imgui_helpers::selectable_cell_formatted(%a0, %a1, %a2, %a3, %a4, %a5, %a6, %a7, %a8)"
  From "imgui_helpers.h".
Crane Extract Inlined Constant imgui_input_text =>
  "imgui_helpers::input_text(%a0, %a1)" From "imgui_helpers.h".
Crane Extract Inlined Constant imgui_begin_menu_bar =>
  "imgui_helpers::begin_menu_bar()" From "imgui_helpers.h".
Crane Extract Inlined Constant imgui_end_menu_bar =>
  "imgui_helpers::end_menu_bar()" From "imgui_helpers.h".
Crane Extract Inlined Constant imgui_begin_menu =>
  "imgui_helpers::begin_menu(%a0)" From "imgui_helpers.h".
Crane Extract Inlined Constant imgui_end_menu =>
  "imgui_helpers::end_menu()" From "imgui_helpers.h".
Crane Extract Inlined Constant imgui_menu_item =>
  "imgui_helpers::menu_item(%a0, %a1)" From "imgui_helpers.h".
Crane Extract Inlined Constant imgui_next_window_menu_bar =>
  "imgui_helpers::next_window_menu_bar()" From "imgui_helpers.h".
Crane Extract Inlined Constant file_read =>
  "imgui_helpers::file_read(%a0)" From "imgui_helpers.h".
Crane Extract Inlined Constant file_write =>
  "imgui_helpers::file_write(%a0, %a1)" From "imgui_helpers.h".
Crane Extract Inlined Constant clipboard_get =>
  "imgui_helpers::clipboard_get()" From "imgui_helpers.h".
Crane Extract Inlined Constant clipboard_set =>
  "imgui_helpers::clipboard_set(%a0)" From "imgui_helpers.h".
Crane Extract Inlined Constant ctrl_key_pressed =>
  "imgui_helpers::ctrl_key_pressed(%a0)" From "imgui_helpers.h".
Crane Extract Inlined Constant key_pressed =>
  "imgui_helpers::key_pressed(%a0)" From "imgui_helpers.h".
Crane Extract Inlined Constant imgui_same_line =>
  "imgui_helpers::same_line()" From "imgui_helpers.h".
Crane Extract Inlined Constant fbar_ref_label =>
  "imgui_helpers::fbar_ref_label(%a0)" From "imgui_helpers.h".
Crane Extract Inlined Constant imgui_tab_bar_select =>
  "imgui_helpers::tab_bar_select(%a0, %a1, %a2)" From "imgui_helpers.h".
