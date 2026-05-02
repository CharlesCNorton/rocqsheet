(* Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License. *)
(* Full-sheet persistence: a typed record that holds all cell
   variants, with round-trip theorems on each variant. *)

From Stdlib Require Import List BinInt.
From Corelib Require Import PrimString PrimInt63.
From Crane Require Import Mapping.NatIntStd Mapping.ZInt.
From Rocqsheet Require Import Rocqsheet.
Import ListNotations.
Import Rocqsheet.

Inductive FullCell : Type :=
  | FEmpty
  | FInt   : Z -> FullCell
  | FFloat : PrimFloat.float -> FullCell
  | FStr   : PrimString.string -> FullCell
  | FBool  : bool -> FullCell
  | FForm  : Expr -> FullCell.

Definition cell_to_full (c : Cell) : FullCell :=
  match c with
  | CEmpty   => FEmpty
  | CLit n   => FInt n
  | CFloat f => FFloat f
  | CStr s   => FStr s
  | CBool b  => FBool b
  | CForm e  => FForm e
  end.

Definition full_to_cell (f : FullCell) : Cell :=
  match f with
  | FEmpty   => CEmpty
  | FInt n   => CLit n
  | FFloat f => CFloat f
  | FStr s   => CStr s
  | FBool b  => CBool b
  | FForm e  => CForm e
  end.

Theorem full_round_trip : forall c,
  full_to_cell (cell_to_full c) = c.
Proof. intros [| | | | |]; reflexivity. Qed.

Theorem cell_to_full_inj : forall c1 c2,
  cell_to_full c1 = cell_to_full c2 -> c1 = c2.
Proof.
  intros c1 c2 H.
  rewrite <- (full_round_trip c1), <- (full_round_trip c2).
  rewrite H. reflexivity.
Qed.
