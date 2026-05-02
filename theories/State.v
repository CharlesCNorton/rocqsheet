(* Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License. *)
(* Loop-state record, demo content, and the pure helpers (cell_display,
   select_cell, update_fbar, push_undo) that every higher-level module
   in the runtime builds on. *)

From Corelib Require Import PrimString PrimInt63.
From Stdlib Require Import List BinInt.
From Stdlib.Numbers.Cyclic.Int63 Require Import Uint63.
From Crane Require Extraction.
From Crane Require Import Mapping.NatIntStd Mapping.ZInt.
From Crane Require Import Monads.ITree.
From Rocqsheet Require Import Rocqsheet.
From Rocqsheet Require Import ImGuiE.
From Rocqsheet Require Import Formatting.
From Rocqsheet Require Import NumberFormat.
From Rocqsheet Require Import Charts.
From Rocqsheet Require Import Merges.
Import ListNotations.
Import Rocqsheet.

Open Scope itree_scope.
Open Scope int63_scope.
Local Open Scope pstring_scope.

(* Encode the [Align] enum as a Z so the imgui FFI can carry it as a
   single primitive. *)
Definition align_to_z (a : Align) : Z :=
  match a with
  | AlignLeft   => 0%Z
  | AlignCenter => 1%Z
  | AlignRight  => 2%Z
  end.

(* Coercions used by the rendering layer. *)
Axiom int_of_nat : nat -> int.
Crane Extract Inlined Constant int_of_nat =>
  "static_cast<int64_t>(%a0)".

Axiom string_of_z : Z -> PrimString.string.
Crane Extract Inlined Constant string_of_z =>
  "std::to_string(%a0)".

Axiom string_of_float : PrimFloat.float -> PrimString.string.
Crane Extract Inlined Constant string_of_float =>
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

Definition col_label_int (n : int) : PrimString.string :=
  col_label_nat (nat_of_int n).

(* Row and column accessors for [CellRef] computed via [cell_index]. *)
Definition cell_col_of (r : CellRef) : int :=
  PrimInt63.mod (cell_index r) NUM_COLS.

Definition cell_row_of (r : CellRef) : int :=
  PrimInt63.div (cell_index r) NUM_COLS.

Definition cell_label (r : CellRef) : PrimString.string :=
  PrimString.cat (col_label_int (cell_col_of r))
                 (string_of_z (Z.add (Uint63.to_Z (cell_row_of r)) 1)).

(* Demo state: arithmetic, IF, comparison, and error branches. *)
Definition put_lit (s : Sheet) (c r : nat) (v : Z) : Sheet :=
  set_cell s (mkRef (int_of_nat c) (int_of_nat r)) (CLit v).

Definition put_form (s : Sheet) (c r : nat) (e : Expr) : Sheet :=
  set_cell s (mkRef (int_of_nat c) (int_of_nat r)) (CForm e).

Definition put_cell (s : Sheet) (c r : nat) (cell : Cell) : Sheet :=
  set_cell s (mkRef (int_of_nat c) (int_of_nat r)) cell.

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

  let s := put_lit s 0 15 4%Z in
  let s := put_lit s 1 15 7%Z in
  let s := put_lit s 2 15 12%Z in
  let s := put_lit s 3 15 9%Z in
  let s := put_form s 4 15 (ESum (ref_at 0 15) (ref_at 3 15)) in
  let s := put_form s 5 15 (EAvg (ref_at 0 15) (ref_at 3 15)) in
  let s := put_lit s 0 16 2%Z in
  let s := put_lit s 1 16 8%Z in
  let s := put_lit s 2 16 5%Z in
  let s := put_lit s 3 16 11%Z in
  let s := put_form s 4 16 (ESum (ref_at 0 16) (ref_at 3 16)) in
  let s := put_lit s 0 17 3%Z in
  let s := put_lit s 1 17 6%Z in
  let s := put_lit s 2 17 9%Z in
  let s := put_lit s 3 17 14%Z in
  let s := put_form s 4 17 (ESum (ref_at 0 17) (ref_at 3 17)) in
  let s := put_lit s 0 18 10%Z in
  let s := put_lit s 1 18 3%Z in
  let s := put_lit s 2 18 8%Z in
  let s := put_lit s 3 18 7%Z in
  let s := put_form s 4 18 (ESum (ref_at 0 18) (ref_at 3 18)) in
  let s := put_form s 0 19 (ESum (ref_at 0 15) (ref_at 0 18)) in
  let s := put_form s 1 19 (ESum (ref_at 1 15) (ref_at 1 18)) in
  let s := put_form s 2 19 (ESum (ref_at 2 15) (ref_at 2 18)) in
  let s := put_form s 3 19 (ESum (ref_at 3 15) (ref_at 3 18)) in
  let s := put_form s 4 19 (ESum (ref_at 0 15) (ref_at 3 18)) in
  let s := put_form s 6 19 (ECount (ref_at 0 15) (ref_at 3 18)) in

  let s := put_form s 0 21
             (EIfErr (EDiv (ERef (ref_at 0 10)) (EInt 0%Z))
                     (EInt (-1)%Z)) in

  let s := put_cell s 0 23
             (CFloat (PrimFloat.of_uint63 2%uint63)) in
  let s := put_cell s 1 23
             (CFloat (PrimFloat.of_uint63 3%uint63)) in
  let s := put_form s 2 23
             (EFAdd (ERef (ref_at 0 23)) (ERef (ref_at 1 23))) in
  let s := put_form s 3 23
             (EFMul (ERef (ref_at 0 23)) (ERef (ref_at 1 23))) in
  let s := put_form s 4 23
             (EFDiv (ERef (ref_at 1 23)) (ERef (ref_at 0 23))) in

  let s := put_cell s 0 25 (CStr "Rocq"%pstring) in
  let s := put_cell s 1 25 (CStr "sheet"%pstring) in
  let s := put_form s 2 25
             (EConcat (ERef (ref_at 0 25)) (ERef (ref_at 1 25))) in
  let s := put_form s 3 25
             (ELen (ERef (ref_at 2 25))) in
  let s := put_form s 4 25
             (ESubstr (ERef (ref_at 2 25)) (EInt 0%Z) (EInt 4%Z)) in

  let s := put_cell s 0 27 (CBool true) in
  let s := put_cell s 1 27 (CBool false) in
  let s := put_form s 2 27
             (EBAnd (ERef (ref_at 0 27)) (ERef (ref_at 1 27))) in
  let s := put_form s 3 27
             (EBOr (ERef (ref_at 0 27)) (ERef (ref_at 1 27))) in
  let s := put_form s 4 27
             (EBNot (ERef (ref_at 0 27))) in

  let s := put_form s 0 29
             (EMin (ref_at 0 0) (ref_at 1 0)) in
  let s := put_form s 1 29
             (EMax (ref_at 0 0) (ref_at 1 0)) in

  let s := put_form s 0 31
             (EMod (EInt 17%Z) (EInt 5%Z)) in
  let s := put_form s 1 31
             (EPow (EInt 2%Z) (EInt 10%Z)) in
  s.

(* ----- Pretty printer (Cell -> source text) ----------------------- *)

Fixpoint show_expr (e : Expr) : PrimString.string :=
  match e with
  | EInt n => string_of_z n
  | ERef r => cell_label r
  | EAdd a b => PrimString.cat
                 (PrimString.cat
                   (PrimString.cat "(" (show_expr a))
                   ")+(")
                 (PrimString.cat (show_expr b) ")")
  | ESub a b => PrimString.cat
                 (PrimString.cat
                   (PrimString.cat "(" (show_expr a))
                   ")-(")
                 (PrimString.cat (show_expr b) ")")
  | EMul a b => PrimString.cat
                 (PrimString.cat
                   (PrimString.cat "(" (show_expr a))
                   ")*(")
                 (PrimString.cat (show_expr b) ")")
  | EDiv a b => PrimString.cat
                 (PrimString.cat
                   (PrimString.cat "(" (show_expr a))
                   ")/(")
                 (PrimString.cat (show_expr b) ")")
  | EEq a b => PrimString.cat
                 (PrimString.cat
                   (PrimString.cat "(" (show_expr a))
                   ")=(")
                 (PrimString.cat (show_expr b) ")")
  | ELt a b => PrimString.cat
                 (PrimString.cat
                   (PrimString.cat "(" (show_expr a))
                   ")<(")
                 (PrimString.cat (show_expr b) ")")
  | EGt a b => PrimString.cat
                 (PrimString.cat
                   (PrimString.cat "(" (show_expr a))
                   ")>(")
                 (PrimString.cat (show_expr b) ")")
  | EIf c t e =>
    PrimString.cat "IF("
      (PrimString.cat (show_expr c)
        (PrimString.cat ","
          (PrimString.cat (show_expr t)
            (PrimString.cat ","
              (PrimString.cat (show_expr e) ")")))))
  | EMod a b => PrimString.cat
                 (PrimString.cat
                   (PrimString.cat "(" (show_expr a))
                   ")%(")
                 (PrimString.cat (show_expr b) ")")
  | EPow a b => PrimString.cat
                 (PrimString.cat
                   (PrimString.cat "(" (show_expr a))
                   ")^(")
                 (PrimString.cat (show_expr b) ")")
  | ENot a => PrimString.cat "NOT(" (PrimString.cat (show_expr a) ")")
  | EAnd a b => PrimString.cat "AND("
                 (PrimString.cat (show_expr a)
                   (PrimString.cat ","
                     (PrimString.cat (show_expr b) ")")))
  | EOr a b => PrimString.cat "OR("
                (PrimString.cat (show_expr a)
                  (PrimString.cat ","
                    (PrimString.cat (show_expr b) ")")))
  | ESum tl br =>
    PrimString.cat "SUM("
      (PrimString.cat (cell_label tl)
        (PrimString.cat ":"
          (PrimString.cat (cell_label br) ")")))
  | EAvg tl br =>
    PrimString.cat "AVG("
      (PrimString.cat (cell_label tl)
        (PrimString.cat ":"
          (PrimString.cat (cell_label br) ")")))
  | ECount tl br =>
    PrimString.cat "COUNT("
      (PrimString.cat (cell_label tl)
        (PrimString.cat ":"
          (PrimString.cat (cell_label br) ")")))
  | EIfErr a fb =>
    PrimString.cat "IFERROR("
      (PrimString.cat (show_expr a)
        (PrimString.cat ","
          (PrimString.cat (show_expr fb) ")")))
  | EFloat f => string_of_float f
  | EFAdd a b => PrimString.cat
                  (PrimString.cat
                    (PrimString.cat "(" (show_expr a))
                    ").+(")
                  (PrimString.cat (show_expr b) ")")
  | EFSub a b => PrimString.cat
                  (PrimString.cat
                    (PrimString.cat "(" (show_expr a))
                    ").-(")
                  (PrimString.cat (show_expr b) ")")
  | EFMul a b => PrimString.cat
                  (PrimString.cat
                    (PrimString.cat "(" (show_expr a))
                    ").*(")
                  (PrimString.cat (show_expr b) ")")
  | EFDiv a b => PrimString.cat
                  (PrimString.cat
                    (PrimString.cat "(" (show_expr a))
                    ")./(")
                  (PrimString.cat (show_expr b) ")")
  | EStr s => PrimString.cat """" (PrimString.cat s """")
  | EConcat a b =>
    PrimString.cat "CONCAT("
      (PrimString.cat (show_expr a)
        (PrimString.cat ","
          (PrimString.cat (show_expr b) ")")))
  | ELen a =>
    PrimString.cat "LEN(" (PrimString.cat (show_expr a) ")")
  | ESubstr a b c =>
    PrimString.cat "SUBSTR("
      (PrimString.cat (show_expr a)
        (PrimString.cat ","
          (PrimString.cat (show_expr b)
            (PrimString.cat ","
              (PrimString.cat (show_expr c) ")")))))
  | EBool b => if b then "TRUE" else "FALSE"
  | EBNot a => PrimString.cat "BNOT(" (PrimString.cat (show_expr a) ")")
  | EBAnd a b => PrimString.cat "BAND("
                  (PrimString.cat (show_expr a)
                    (PrimString.cat ","
                      (PrimString.cat (show_expr b) ")")))
  | EBOr a b => PrimString.cat "BOR("
                 (PrimString.cat (show_expr a)
                   (PrimString.cat ","
                     (PrimString.cat (show_expr b) ")")))
  | EMin tl br =>
    PrimString.cat "MIN("
      (PrimString.cat (cell_label tl)
        (PrimString.cat ":"
          (PrimString.cat (cell_label br) ")")))
  | EMax tl br =>
    PrimString.cat "MAX("
      (PrimString.cat (cell_label tl)
        (PrimString.cat ":"
          (PrimString.cat (cell_label br) ")")))
  end.

Definition show_cell (c : Cell) : PrimString.string :=
  match c with
  | CEmpty   => ""
  | CLit n   => string_of_z n
  | CFloat f => string_of_float f
  | CStr s   => s
  | CBool b  => if b then "TRUE" else "FALSE"
  | CForm e  => PrimString.cat "=" (show_expr e)
  end.

(* ----- Loop state --------------------------------------------- *)

(* Assoc-list workbook keyed by int63. *)
Fixpoint assoc_int_lookup (xs : list (int * Sheet)) (k : int) : option Sheet :=
  match xs with
  | nil => None
  | (k', v) :: rest =>
    if PrimInt63.eqb k k' then Some v else assoc_int_lookup rest k
  end.

Fixpoint assoc_int_remove (xs : list (int * Sheet)) (k : int)
    : list (int * Sheet) :=
  match xs with
  | nil => nil
  | (k', v) :: rest =>
    if PrimInt63.eqb k k' then assoc_int_remove rest k
    else (k', v) :: assoc_int_remove rest k
  end.

Record loop_state : Type := mkLoop {
  ls_sheet        : Sheet;
  ls_selected     : option CellRef;
  ls_fbar_text    : PrimString.string;
  ls_edit_buf     : list (CellRef * PrimString.string);
  ls_parse_errs   : list CellRef;
  ls_undo         : list (Sheet * PrimString.string);
  ls_redo         : list (Sheet * PrimString.string);
  ls_formats      : FormatMap;
  ls_other_sheets : list (int * Sheet);
  ls_active       : int;
  ls_charts       : list Chart;
  ls_merges       : MergeList;
  ls_sheet_names  : list PrimString.string
}.

(* Helpers for the [ls_sheet_names] list. *)
Fixpoint list_set_nth_string (xs : list PrimString.string) (n : nat)
                             (v : PrimString.string)
  : list PrimString.string :=
  match xs, n with
  | nil, _      => nil
  | _ :: ys, O  => v :: ys
  | y :: ys, S n' => y :: list_set_nth_string ys n' v
  end.

Fixpoint list_nth_string (xs : list PrimString.string) (n : nat)
                         (default : PrimString.string)
  : PrimString.string :=
  match xs, n with
  | nil, _ => default
  | y :: _, O => y
  | _ :: ys, S n' => list_nth_string ys n' default
  end.

Definition default_sheet_names : list PrimString.string :=
  ["Sheet 1"; "Sheet 2"; "Sheet 3"; "Sheet 4";
   "Sheet 5"; "Sheet 6"; "Sheet 7"; "Sheet 8";
   "Sheet 9"; "Sheet 10"; "Sheet 11"; "Sheet 12";
   "Sheet 13"; "Sheet 14"; "Sheet 15"; "Sheet 16"].

Definition demo_formats : FormatMap :=
  [ (ref_at 2 0, mkFormat true 16711680%Z (* 0xFF0000 red *)
                          false AlignRight NFCurrency)
  ; (ref_at 3 0, mkFormat true 16711680%Z false AlignRight (NFDecimal 2%Z))
  ; (ref_at 2 2, mkFormat false 32768%Z   (* 0x008000 green *)
                          true  AlignRight NFInteger)
  ; (ref_at 3 2, mkFormat true 255%Z      (* 0x0000FF blue *)
                          true  AlignCenter NFPercent)
  ; (ref_at 2 4, mkFormat false 8388736%Z (* 0x800080 purple *)
                          false AlignRight NFInteger) ].

Definition sales_sheet : Sheet :=
  let s := new_sheet in
  let s := put_lit s 0 0 100%Z in
  let s := put_lit s 1 0 7%Z in
  let s := put_form s 2 0
             (EMul (ERef (ref_at 0 0)) (ERef (ref_at 1 0))) in
  let s := put_lit s 0 1 250%Z in
  let s := put_lit s 1 1 12%Z in
  let s := put_form s 2 1
             (EMul (ERef (ref_at 0 1)) (ERef (ref_at 1 1))) in s.

Definition initial_other_sheets : list (int * Sheet) :=
  [(1%uint63, sales_sheet)].

Definition initial_charts : list Chart :=
  [ mkChart ChartLine    (ref_at 0 0) (ref_at 3 0) []
  ; mkChart ChartBar     (ref_at 0 2) (ref_at 3 2) []
  ; mkChart ChartScatter (ref_at 0 4) (ref_at 2 4) [] ].

Definition initial_loop_state : loop_state :=
  mkLoop demo_sheet None "" nil nil nil nil demo_formats
         initial_other_sheets 0%uint63 initial_charts nil
         default_sheet_names.

(* ----- Edit-buffer / parse-error helpers -------------------- *)

Fixpoint lookup_edit (eb : list (CellRef * PrimString.string)) (r : CellRef)
  : option PrimString.string :=
  match eb with
  | nil => None
  | (r', s) :: rest =>
    if cellref_eqb r r' then Some s else lookup_edit rest r
  end.

Fixpoint remove_edit (eb : list (CellRef * PrimString.string)) (r : CellRef)
  : list (CellRef * PrimString.string) :=
  match eb with
  | nil => nil
  | (r', s) :: rest =>
    if cellref_eqb r r' then rest else (r', s) :: remove_edit rest r
  end.

Definition put_edit (eb : list (CellRef * PrimString.string))
    (r : CellRef) (s : PrimString.string)
  : list (CellRef * PrimString.string) :=
  (r, s) :: remove_edit eb r.

Fixpoint mem_ref (xs : list CellRef) (r : CellRef) : bool :=
  match xs with
  | nil => false
  | r' :: rest => if cellref_eqb r r' then true else mem_ref rest r
  end.

Fixpoint remove_ref (xs : list CellRef) (r : CellRef) : list CellRef :=
  match xs with
  | nil => nil
  | r' :: rest =>
    if cellref_eqb r r' then rest else r' :: remove_ref rest r
  end.

Definition add_ref (xs : list CellRef) (r : CellRef) : list CellRef :=
  if mem_ref xs r then xs else r :: xs.

(* ----- Cell display ----------------------------------------- *)

Definition err_marker : PrimString.string := "#ERR".
Definition parse_marker : PrimString.string := "#PARSE".

Definition cell_display (s : Sheet) (ms : MergeList) (errs : list CellRef)
                        (fm : FormatMap) (r : CellRef)
  : PrimString.string * bool :=
  if mem_ref errs r then (parse_marker, true)
  else
    let resolved := resolve ms r in
    let nf := fmt_number (lookup_format fm resolved) in
    match get_cell s resolved with
    | CEmpty   => ("", false)
    | CLit n   => (format_z n nf, false)
    | CFloat f => (format_float f nf, false)
    | CStr str => (str, false)
    | CBool b  => ((if b then "TRUE" else "FALSE"), false)
    | CForm e =>
      match eval_expr DEFAULT_FUEL (mark_visited empty_visited resolved) s e with
      | EVal v   => (format_z v nf, false)
      | EFVal f  => (format_float f nf, false)
      | EValS sv => (sv, false)
      | EValB b  => ((if b then "TRUE" else "FALSE"), false)
      | EErr     => (err_marker, true)
      | EFuel    => (err_marker, true)
      end
    end.

Definition fbar_for_cell
    (eb : list (CellRef * PrimString.string)) (s : Sheet) (r : CellRef)
  : PrimString.string :=
  match lookup_edit eb r with
  | Some t => t
  | None => show_cell (get_cell s r)
  end.

(* ----- Pure event handlers --------------------------------- *)

(* Maximum undo-stack depth.  Every push trims the head to keep
   long-running sessions from accumulating unbounded sheet snapshots
   on the heap.  Wired through by [trim_undo] below; future config
   work can move this onto [loop_state] for per-session overrides. *)
Definition undo_max_depth : nat := 100.

Definition trim_undo (xs : list (Sheet * PrimString.string))
  : list (Sheet * PrimString.string) :=
  firstn undo_max_depth xs.

Definition push_undo (ls : loop_state) (before : Sheet)
                     (desc : PrimString.string) : loop_state :=
  mkLoop (ls_sheet ls) (ls_selected ls) (ls_fbar_text ls)
         (ls_edit_buf ls) (ls_parse_errs ls)
         (trim_undo ((before, desc) :: ls_undo ls)) nil (ls_formats ls)
         (ls_other_sheets ls) (ls_active ls) (ls_charts ls)
         (ls_merges ls) (ls_sheet_names ls).

(* What text to show in the menu bar's "Undo" / "Redo" item: the
   description of the head entry, or the empty string when the stack
   is empty (the menu item also greys out in that case). *)
Definition next_undo_desc (ls : loop_state) : PrimString.string :=
  match ls_undo ls with
  | nil => ""
  | (_, d) :: _ => d
  end.

Definition next_redo_desc (ls : loop_state) : PrimString.string :=
  match ls_redo ls with
  | nil => ""
  | (_, d) :: _ => d
  end.

Definition select_cell (ls : loop_state) (r : CellRef) : loop_state :=
  mkLoop (ls_sheet ls) (Some r)
         (fbar_for_cell (ls_edit_buf ls) (ls_sheet ls) r)
         (ls_edit_buf ls) (ls_parse_errs ls)
         (ls_undo ls) (ls_redo ls) (ls_formats ls)
         (ls_other_sheets ls) (ls_active ls) (ls_charts ls)
         (ls_merges ls) (ls_sheet_names ls).

Definition update_fbar (ls : loop_state) (s : PrimString.string) : loop_state :=
  mkLoop (ls_sheet ls) (ls_selected ls) s
         (ls_edit_buf ls) (ls_parse_errs ls)
         (ls_undo ls) (ls_redo ls) (ls_formats ls)
         (ls_other_sheets ls) (ls_active ls) (ls_charts ls)
         (ls_merges ls) (ls_sheet_names ls).
