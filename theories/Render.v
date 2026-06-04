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
From Rocqsheet Require Import Merges.
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
  let '(disp_raw, is_err) :=
    cell_display (ls_sheet ls) (ls_merges ls) (ls_parse_errs ls)
                 (ls_formats ls) ref in
  (* Item 68: when Show Formulas mode is on, replace each cell's
     evaluated value with its source text (the `=A1+B1` etc.).  We
     keep the parse-error tag so [#PARSE] still surfaces visibly. *)
  let disp :=
    if ls_show_formulas ls then
      let resolved := resolve (ls_merges ls) ref in
      let raw := show_cell (get_cell (ls_sheet ls) resolved) in
      if mem_ref (ls_parse_errs ls) ref then disp_raw else raw
    else disp_raw in
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

(* Item 60: scale column widths by ls_zoom%.  Base width 80 at 100%
   zoom; clamped at runtime to [40, 240] so the grid stays usable
   even at extreme zoom levels. *)
Definition zoomed_col_width (zoom_pct : Z) : Z :=
  let raw := Z.div (Z.mul 80%Z zoom_pct) 100%Z in
  if Z.ltb raw 40%Z then 40%Z
  else if Z.ltb 240%Z raw then 240%Z
  else raw.

Fixpoint setup_columns_z
    (c : nat) (count : nat) (w : int) : itree imguiE unit :=
  match count with
  | O => Ret tt
  | S count' =>
    imgui_table_setup_column (col_label_nat c) w ;;
    setup_columns_z (S c) count' w
  end.

Definition setup_columns (ls : loop_state) (count : nat) : itree imguiE unit :=
  setup_columns_z 0 count (Uint63.of_Z (zoomed_col_width (ls_zoom ls))).

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
    setup_columns ls num_cols_nat ;;
    imgui_table_headers_row ;;
    imgui_clipper_begin (int_of_nat num_rows_nat) ;;
    ls' <- clipper_loop 8 ls num_cols_nat ;;
    imgui_clipper_end ;;
    imgui_end_table ;;
    Ret ls'
  else
    Ret ls.

(* After Enter commits, advance the selection one row down so the
   user can stream a column of values without reaching for the
   arrow keys.  Clamped at the last row.  Item 53 (Enter half).
   Tab-advances are deferred until ImGui's Tab handler is wired to
   bypass focus cycling. *)
Definition advance_after_enter (ls : loop_state) : loop_state :=
  match ls_selected ls with
  | None => ls
  | Some r =>
    let r1 := PrimInt63.add (cell_row_of r) 1 in
    let new_r :=
      if PrimInt63.leb (int_of_nat num_rows_nat) r1
      then PrimInt63.sub (int_of_nat num_rows_nat) 1
      else r1 in
    select_cell ls (mkRef (cell_col_of r) new_r)
  end.

(* Item 53 (Tab half): advance selection one column right, clamped at
   the last column.  Invoked from [handle_shortcuts] when the user
   presses Tab — we read the key before ImGui's focus-cycling handler
   acts on it, so the formula-bar text is committed and the selection
   walks across the row. *)
Definition advance_after_tab (ls : loop_state) : loop_state :=
  match ls_selected ls with
  | None => ls
  | Some r =>
    let c1 := PrimInt63.add (cell_col_of r) 1 in
    let new_c :=
      if PrimInt63.leb (int_of_nat num_cols_nat) c1
      then PrimInt63.sub (int_of_nat num_cols_nat) 1
      else c1 in
    select_cell ls (mkRef new_c (cell_row_of r))
  end.

(* Item 64: count '(' and ')' in the formula-bar text.  The byte-
   exact scan is fine because '(' and ')' are single-byte ASCII even
   under any multi-byte encoding we'd care about. *)
Fixpoint parens_balance_aux (s : PrimString.string) (i : int)
                            (len : int) (fuel : nat) (oc : Z * Z) : Z * Z :=
  let '(o, c) := oc in
  match fuel with
  | O => (o, c)
  | S fuel' =>
    if PrimInt63.leb len i then (o, c)
    else
      let b := PrimString.get s i in
      let oc' :=
        if PrimInt63.eqb b 40%uint63 then (Z.add o 1%Z, c)
        else if PrimInt63.eqb b 41%uint63 then (o, Z.add c 1%Z)
        else (o, c) in
      parens_balance_aux s (PrimInt63.add i 1) len fuel' oc'
  end.

Definition parens_balance (s : PrimString.string) : Z * Z :=
  parens_balance_aux s 0 (PrimString.length s) 4096 (0%Z, 0%Z).

(* Item 64: scan the formula-bar text and compute (open, close)
   parenthesis counts.  Equal counts + nonzero ≡ balanced; anything
   else surfaces a small indicator next to the input. *)
Definition parens_indicator (txt : PrimString.string) : PrimString.string :=
  let p := parens_balance txt in
  let opens := fst p in
  let closes := snd p in
  if Z.eqb opens closes then
    if Z.eqb opens 0%Z then ""%pstring
    else "()"%pstring
  else if Z.ltb closes opens then "(...?"%pstring
  else "?)..."%pstring.

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
  imgui_same_line ;;
  imgui_text (parens_indicator new_text) ;;
  let ls1 := update_fbar ls new_text in
  Ret (if enter then advance_after_enter (do_commit ls1) else ls1).

(* ----- Status bar (item 51) -------------------------------- *)
(* Per-frame aggregate over the active sheet: sum, count, avg, min,
   max, non-empty count.  Surfaced at the bottom of the main window
   so the user does not have to type a [SUM(...)] formula into a
   scratch cell to see the total.  When [ls_selected] resolves to a
   numeric cell, that cell's value and label are appended.  Once the
   selection model is widened to a range (item 50), this driver
   becomes the range-aggregate path. *)

Record sheet_agg : Type := mkAgg {
  ag_count    : nat;
  ag_nonempty : nat;
  ag_sum      : Z;
  ag_min      : Z;
  ag_max      : Z;
  ag_has_any  : bool
}.

Definition empty_agg : sheet_agg :=
  mkAgg 0 0 0%Z 0%Z 0%Z false.

Definition merge_z (a : sheet_agg) (v : Z) : sheet_agg :=
  if ag_has_any a then
    mkAgg (S (ag_count a))
          (S (ag_nonempty a))
          (Z.add (ag_sum a) v)
          (if Z.ltb v (ag_min a) then v else ag_min a)
          (if Z.ltb (ag_max a) v then v else ag_max a)
          true
  else
    mkAgg 1 1 v v v true.

Definition merge_nonempty (a : sheet_agg) : sheet_agg :=
  mkAgg (ag_count a) (S (ag_nonempty a)) (ag_sum a)
        (ag_min a) (ag_max a) (ag_has_any a).

Fixpoint walk_sheet_aux (s : Sheet) (idx : int) (fuel : nat)
                       (acc : sheet_agg) : sheet_agg :=
  match fuel with
  | O => acc
  | S fuel' =>
    if PrimInt63.leb GRID_SIZE idx then acc
    else
      let acc' :=
        match PrimArray.get s idx with
        | CEmpty   => acc
        | CLit n   => merge_z acc n
        | CFloat _ => merge_nonempty acc
        | CStr _   => merge_nonempty acc
        | CBool _  => merge_nonempty acc
        | CForm e =>
          match eval_expr DEFAULT_FUEL empty_visited s e with
          | EVal v => merge_z acc v
          | EFVal _ | EValS _ | EValB _ => merge_nonempty acc
          | _ => acc
          end
        end in
      walk_sheet_aux s (PrimInt63.add idx 1) fuel' acc'
  end.

Definition sheet_aggregate (s : Sheet) : sheet_agg :=
  walk_sheet_aux s 0 60000 empty_agg.

Definition agg_avg (a : sheet_agg) : Z :=
  if Nat.eqb (ag_count a) 0 then 0%Z
  else Z.div (ag_sum a) (Z.of_nat (ag_count a)).

Definition status_bar_text (ls : loop_state) : PrimString.string :=
  let a := sheet_aggregate (ls_sheet ls) in
  let agg :=
    if ag_has_any a then
      PrimString.cat "Sum: "%pstring (
      PrimString.cat (string_of_z (ag_sum a)) (
      PrimString.cat " | Avg: "%pstring (
      PrimString.cat (string_of_z (agg_avg a)) (
      PrimString.cat " | Count: "%pstring (
      PrimString.cat (string_of_z (Z.of_nat (ag_count a))) (
      PrimString.cat " | Non-empty: "%pstring (
      PrimString.cat (string_of_z (Z.of_nat (ag_nonempty a))) (
      PrimString.cat " | Min: "%pstring (
      PrimString.cat (string_of_z (ag_min a)) (
      PrimString.cat " | Max: "%pstring (
      string_of_z (ag_max a))))))))))))
    else
      "Sheet is empty"%pstring in
  match ls_selected ls with
  | None => agg
  | Some r =>
    let '(disp, _) :=
      cell_display (ls_sheet ls) (ls_merges ls) (ls_parse_errs ls)
                   (ls_formats ls) r in
    PrimString.cat "Sel: "%pstring (
    PrimString.cat (cell_label r) (
    PrimString.cat " = "%pstring (
    PrimString.cat disp (
    PrimString.cat "    "%pstring agg))))
  end.

Definition render_status_bar (ls : loop_state) : itree imguiE unit :=
  imgui_text (status_bar_text ls).

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
