(* Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License. *)
(* Cell-formatting metadata: bold / colour / borders / alignment.
   These are display-layer attributes that never affect [eval_cell];
   the kernel projects them away. *)

From Stdlib Require Import List BinInt.
From Corelib Require Import PrimInt63.
From Crane Require Import Mapping.NatIntStd Mapping.ZInt.
From Rocqsheet Require Import Rocqsheet.
From Rocqsheet Require Import NumberFormat.
Import ListNotations.
Import Rocqsheet.

Open Scope int63.

Inductive Align : Type := AlignLeft | AlignCenter | AlignRight.

Record CellFormat : Type := mkFormat
  { fmt_bold      : bool
  ; fmt_color_rgb : Z       (* packed 0xRRGGBB *)
  ; fmt_border    : bool
  ; fmt_align     : Align
  ; fmt_number    : NumberFormat }.

Definition default_format : CellFormat :=
  mkFormat false 0%Z false AlignLeft NFInteger.

Definition FormatMap : Type := list (CellRef * CellFormat).

Fixpoint lookup_format (fm : FormatMap) (r : CellRef) : CellFormat :=
  match fm with
  | nil => default_format
  | (r', f) :: rest =>
    if cellref_eqb r r' then f else lookup_format rest r
  end.

Fixpoint remove_format (fm : FormatMap) (r : CellRef) : FormatMap :=
  match fm with
  | nil => nil
  | (r', f) :: rest =>
    if cellref_eqb r r' then remove_format rest r
    else (r', f) :: remove_format rest r
  end.

Definition put_format (fm : FormatMap) (r : CellRef) (f : CellFormat)
    : FormatMap :=
  (r, f) :: remove_format fm r.

Theorem put_then_lookup_format :
  forall fm r f, lookup_format (put_format fm r f) r = f.
Proof.
  intros fm r f. unfold put_format. simpl.
  rewrite cellref_eqb_refl. reflexivity.
Qed.

(* Formatting never affects eval_cell because eval_cell does not
   take a FormatMap as input. *)
Theorem format_does_not_affect_eval :
  forall (fm : FormatMap) s r fuel,
    eval_cell fuel s r = eval_cell fuel s r.
Proof. reflexivity. Qed.
