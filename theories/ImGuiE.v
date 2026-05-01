(* Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License. *)
(* Effect interface for the ImGui front-end.  Each constructor of
   [imguiE] corresponds one-to-one with a function in
   [src/imgui_helpers.h]. *)

From Corelib Require Import PrimString PrimInt63.
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
  | EClipperEnd       : imguiE unit.

(* Smart constructors.  Each one is a one-liner [trigger E*] that
   the [Crane Extract Inlined Constant] directives below resolve to
   the matching C++ helper call. *)
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
    "imgui_helpers::clipper_end()" ]
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
