(* Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License. *)
(* PDF export sketch: the kernel side of a future C++ printing
   layer.  Here we pin down the in-memory document structure and
   prove a few invariants; the actual PDF byte stream is produced
   by the C++ runtime. *)

From Stdlib Require Import List BinInt.
From Corelib Require Import PrimString PrimInt63.
From Crane Require Import Mapping.NatIntStd Mapping.ZInt.
From Rocqsheet Require Import Rocqsheet.
Import ListNotations.
Import Rocqsheet.

Open Scope Z_scope.

Inductive PageOrientation : Type := Portrait | Landscape.

Record PdfPage : Type := mkPdfPage
  { page_orientation : PageOrientation
  ; page_top_left   : CellRef
  ; page_bot_right  : CellRef }.

Definition PdfDoc : Type := list PdfPage.

Definition empty_pdf : PdfDoc := [].

Definition append_page (d : PdfDoc) (p : PdfPage) : PdfDoc := d ++ [p].

Theorem append_page_count : forall d p,
  List.length (append_page d p) = S (List.length d).
Proof.
  intros. unfold append_page. rewrite List.app_length. simpl.
  induction (List.length d); simpl; [reflexivity|f_equal; assumption].
Qed.

Theorem empty_pdf_no_pages : List.length empty_pdf = 0%nat.
Proof. reflexivity. Qed.
