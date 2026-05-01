(* Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License. *)
(* Rocqsheet runtime: per-frame procedure, frame loop, and entry
   point invoked by [src/main.cpp] after GLFW + ImGui setup. *)

From Corelib Require Import PrimString PrimInt63.
From Stdlib Require Import List BinInt.
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

(* ----- Loop state --------------------------------------------- *)

(* For #1 the only persistent state is the [Sheet].  Editing,
   selection, undo/redo, and the formula bar move into this record
   in #3. *)
(* Per-frame state.  Selection, edit buffers, undo/redo, and the
   formula bar will join this record once their handlers move into
   Rocq. *)
Record loop_state : Type := mkLoop {
  ls_sheet : Sheet
}.

Definition initial_loop_state : loop_state :=
  mkLoop demo_sheet.

(* ----- Cell rendering ----------------------------------------- *)

Definition err_marker : PrimString.string := "#ERR".

Definition render_one_cell (s : Sheet) (c r : nat) : itree imguiE unit :=
  let ref := ref_at c r in
  match get_cell s ref with
  | CEmpty => Ret tt
  | CLit n => imgui_text (string_of_z n)
  | CForm e =>
    match eval_expr DEFAULT_FUEL (cons ref nil) s e with
    | Some v => imgui_text (string_of_z v)
    | None => imgui_text_err err_marker
    end
  end.

Fixpoint render_cells_in_row
    (s : Sheet) (r : nat) (c : nat) (count : nat) : itree imguiE unit :=
  match count with
  | O => Ret tt
  | S count' =>
    imgui_table_set_column_index (int_of_nat (S c)) ;;
    render_one_cell s c r ;;
    render_cells_in_row s r (S c) count'
  end.

Fixpoint render_rows_in_range
    (s : Sheet) (start : nat) (count : nat) (num_cols : nat) : itree imguiE unit :=
  match count with
  | O => Ret tt
  | S count' =>
    imgui_table_next_row ;;
    imgui_table_set_column_index 0 ;;
    imgui_text (string_of_nat (S start)) ;;
    render_cells_in_row s start 0 num_cols ;;
    render_rows_in_range s (S start) count' num_cols
  end.

(* Drive the ImGui list clipper.  [fuel] caps the number of step
   iterations per frame; the live clipper takes one to three
   steps in steady state. *)
Fixpoint clipper_loop
    (fuel : nat) (s : Sheet) (num_cols : nat) : itree imguiE unit :=
  match fuel with
  | O => Ret tt
  | S fuel' =>
    cont <- imgui_clipper_step ;;
    if cont then
      start_i <- imgui_clipper_get_start ;;
      end_i <- imgui_clipper_get_end ;;
      let count := nat_of_int (PrimInt63.sub end_i start_i) in
      let s_idx := nat_of_int start_i in
      render_rows_in_range s s_idx count num_cols ;;
      clipper_loop fuel' s num_cols
    else
      Ret tt
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

Definition render_grid (s : Sheet) : itree imguiE unit :=
  ok <- imgui_begin_table "grid" (int_of_nat (S num_cols_nat)) ;;
  if ok then
    imgui_table_setup_freeze 1 1 ;;
    imgui_table_setup_column "" 32 ;;
    setup_columns 0 num_cols_nat ;;
    imgui_table_headers_row ;;
    imgui_clipper_begin (int_of_nat num_rows_nat) ;;
    clipper_loop 8 s num_cols_nat ;;
    imgui_clipper_end ;;
    imgui_end_table ;;
    (* Trailing [Ret tt] retains [imgui_end_table] in extraction;
       Crane's erased-itree mode otherwise drops the tail effect of
       a unit-typed [;;]-chain. *)
    Ret tt
  else
    Ret tt.

Definition process_frame (ls : loop_state) : itree imguiE (bool * loop_state) :=
  glfw_poll_events ;;
  closing <- glfw_should_close ;;
  if closing then Ret (true, ls)
  else
    imgui_new_frame ;;
    imgui_full_viewport ;;
    imgui_begin_window "Rocqsheet" ;;
    render_grid (ls_sheet ls) ;;
    imgui_end_window ;;
    imgui_render_frame ;;
    Ret (false, ls).

(* ----- Top-level loop ---------------------------------------- *)

Axiom c_int : Type.
Axiom c_zero : c_int.
Crane Extract Inlined Constant c_int => "int".
Crane Extract Inlined Constant c_zero => "0".

CoFixpoint run_app (ls : loop_state) : itree imguiE c_int :=
  res <- process_frame ls ;;
  let '(quit, ls') := res in
  if quit then Ret c_zero
  else Tau (run_app ls').

(* Extracted entry point.  Named [rocqsheet_run] rather than [main]
   so the C++ entry point can perform GLFW/ImGui setup around a
   single call into the Rocq runtime. *)
Definition rocqsheet_run : itree imguiE c_int :=
  run_app initial_loop_state.

(* Extract the runtime entry point alongside [smoke], [eval_cell],
   [parse_formula], and [parse_int_literal] so the test targets and
   the future C++ commit path can see them. *)
Crane Extraction "rocqsheet" rocqsheet_run smoke eval_cell
  parse_formula parse_int_literal.
