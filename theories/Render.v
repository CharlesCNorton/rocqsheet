(* Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License. *)
(* Per-frame render functions: cell grid, formula bar, tab bar,
   inline charts, and the PDF emission helper. *)

From Corelib Require Import PrimString PrimInt63.
From Stdlib Require Import List BinInt.
From Stdlib.Numbers.Cyclic.Int63 Require Import Uint63.
From Crane Require Extraction.
From Crane Require Import Mapping.NatIntStd Mapping.ZInt.
From Crane Require Import Monads.ITree.
From Rocqsheet Require Import Rocqsheet.
From Rocqsheet Require Import ImGuiE.
From Rocqsheet Require Import Formatting.
From Rocqsheet Require Import Charts.
From Rocqsheet Require Import Pdf.
From Rocqsheet Require Import State.
From Rocqsheet Require Import Edit.
Import ListNotations.
Import Rocqsheet.

Open Scope itree_scope.
Open Scope int63_scope.
Local Open Scope pstring_scope.

Definition render_one_cell
    (ls : loop_state) (c r : nat) : itree imguiE loop_state :=
  let ref := ref_at c r in
  let '(disp, is_err) :=
    cell_display (ls_sheet ls) (ls_merges ls) (ls_parse_errs ls)
                 (ls_formats ls) ref in
  let selected :=
    match ls_selected ls with
    | None => false
    | Some sr => cellref_eqb sr ref
    end in
  let fmt := lookup_format (ls_formats ls) ref in
  ev <- imgui_selectable_cell_fmt (int_of_nat c) (int_of_nat r)
                                   selected is_err disp
                                   (fmt_bold fmt) (fmt_color_rgb fmt)
                                   (fmt_border fmt)
                                   (align_to_z (fmt_align fmt)) ;;
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

Definition render_tab_bar (ls : loop_state) : itree imguiE loop_state :=
  new_idx <- imgui_tab_bar_select "sheets" (ls_sheet_names ls)
                                  (ls_active ls) ;;
  Ret (switch_to_sheet ls new_idx).

Definition cell_value_z (s : Sheet) (r : CellRef) : option Z :=
  match get_cell s r with
  | CLit n => Some n
  | CForm e =>
    match eval_expr DEFAULT_FUEL (mark_visited empty_visited r) s e with
    | EVal n => Some n
    | _ => None
    end
  | _ => None
  end.

Fixpoint chart_row_values
    (s : Sheet) (row : nat) (col : nat) (count : nat) (acc : list Z) : list Z :=
  match count with
  | O => acc
  | S count' =>
    let r := ref_at col row in
    let acc' :=
      match cell_value_z s r with
      | Some n => acc ++ [n]
      | None => acc
      end in
    chart_row_values s row (S col) count' acc'
  end.

Fixpoint chart_range_values
    (s : Sheet) (row : nat) (count : nat)
    (col_start col_count : nat) (acc : list Z) : list Z :=
  match count with
  | O => acc
  | S count' =>
    let acc' := chart_row_values s row col_start col_count acc in
    chart_range_values s (S row) count' col_start col_count acc'
  end.

Definition chart_values (s : Sheet) (c : Chart) : list Z :=
  let cs := nat_of_int (cell_col_of (chart_tl c)) in
  let ce := nat_of_int (cell_col_of (chart_br c)) in
  let rs := nat_of_int (cell_row_of (chart_tl c)) in
  let re := nat_of_int (cell_row_of (chart_br c)) in
  if andb (Nat.leb cs ce) (Nat.leb rs re)
  then chart_range_values s rs (S (re - rs)) cs (S (ce - cs)) []
  else [].

Definition chart_kind_to_z (k : ChartKind) : Z :=
  match k with
  | ChartLine    => 0%Z
  | ChartBar     => 1%Z
  | ChartPie     => 2%Z
  | ChartScatter => 3%Z
  end.

Definition chart_default_title (k : ChartKind) : PrimString.string :=
  match k with
  | ChartLine    => "Line"
  | ChartBar     => "Bar"
  | ChartPie     => "Pie"
  | ChartScatter => "Scatter"
  end.

Fixpoint render_charts_aux
    (s : Sheet) (cs : list Chart) : itree imguiE unit :=
  match cs with
  | nil => Ret tt
  | c :: rest =>
    let vs := chart_values s c in
    imgui_chart_render (chart_kind_to_z (chart_kind c))
                       vs (chart_default_title (chart_kind c)) ;;
    render_charts_aux s rest
  end.

Definition render_charts (ls : loop_state) : itree imguiE unit :=
  render_charts_aux (ls_sheet ls) (ls_charts ls).

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

(* ----- PDF emission ---------------------------------------- *)

Definition pdf_page_h : Z := 792%Z.
Definition pdf_margin : Z := 36%Z.
Definition pdf_cell_w : Z := 64%Z.
Definition pdf_cell_h : Z := 16%Z.

Definition pdf_text_of_cell (s : Sheet) (r : CellRef) : PrimString.string :=
  match get_cell s r with
  | CEmpty   => ""
  | CLit n   => string_of_z n
  | CFloat f => string_of_float f
  | CStr str => str
  | CBool b  => if b then "TRUE" else "FALSE"
  | CForm e =>
    match eval_expr DEFAULT_FUEL (mark_visited empty_visited r) s e with
    | EVal v   => string_of_z v
    | EFVal f  => string_of_float f
    | EValS sv => sv
    | EValB b  => if b then "TRUE" else "FALSE"
    | _        => ""
    end
  end.

Fixpoint pdf_row_entries
    (s : Sheet) (tl_col tl_row : nat) (col : nat) (cols : nat) (row : nat)
    (acc : list (Z * Z * PrimString.string))
  : list (Z * Z * PrimString.string) :=
  match cols with
  | O => acc
  | S cols' =>
    let r := ref_at col row in
    let txt := pdf_text_of_cell s r in
    let acc' :=
      if PrimInt63.eqb (PrimString.length txt) 0 then acc
      else
        let x := Z.add pdf_margin
                       (Z.mul (Z.of_nat (col - tl_col)) pdf_cell_w) in
        let y := Z.sub
                   (Z.sub pdf_page_h pdf_margin)
                   (Z.mul (Z.add (Z.of_nat (row - tl_row)) 1)
                          pdf_cell_h) in
        acc ++ [(x, y, txt)] in
    pdf_row_entries s tl_col tl_row (S col) cols' row acc'
  end.

Fixpoint pdf_range_entries
    (s : Sheet) (tl_col tl_row : nat) (col_start cols : nat) (row : nat)
    (rows : nat) (acc : list (Z * Z * PrimString.string))
  : list (Z * Z * PrimString.string) :=
  match rows with
  | O => acc
  | S rows' =>
    let acc' := pdf_row_entries s tl_col tl_row col_start cols row acc in
    pdf_range_entries s tl_col tl_row col_start cols (S row) rows' acc'
  end.

Definition default_pdf_pages
    (s : Sheet) : list (list (Z * Z * PrimString.string)) :=
  let entries := pdf_range_entries s 0 0 0 10 0 30 [] in
  [entries].

Definition pdf_path : PrimString.string := "rocqsheet.pdf".

Definition do_pdf_export (ls : loop_state) : itree imguiE loop_state :=
  _ <- imgui_pdf_emit (default_pdf_pages (ls_sheet ls)) pdf_path ;;
  Ret ls.
