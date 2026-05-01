(* Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License. *)
From Corelib Require Import PrimString PrimInt63.
From Stdlib Require Import List.
From Crane Require Import Mapping.Std.
From Rocqsheet Require Import Rocqsheet.
Import ListNotations.
Import Rocqsheet.

Definition NameMap : Type := list (PrimString.string * CellRef).

Definition pstring_eqb (a b : PrimString.string) : bool :=
  match PrimString.compare a b with
  | Eq => true
  | _ => false
  end.

Fixpoint lookup_name (nm : NameMap) (n : PrimString.string)
    : option CellRef :=
  match nm with
  | nil => None
  | (n', r) :: rest =>
    if pstring_eqb n n' then Some r else lookup_name rest n
  end.

Fixpoint remove_name (nm : NameMap) (n : PrimString.string) : NameMap :=
  match nm with
  | nil => nil
  | (n', r) :: rest =>
    if pstring_eqb n n' then remove_name rest n
    else (n', r) :: remove_name rest n
  end.

Definition define_name (nm : NameMap) (n : PrimString.string) (r : CellRef)
    : NameMap :=
  (n, r) :: remove_name nm n.

Theorem lookup_after_define_smoke :
  let nm : NameMap := nil in
  let nm' := define_name nm "myCell" (mkRef 3 5) in
  lookup_name nm' "myCell" = Some (mkRef 3 5).
Proof. vm_compute. reflexivity. Qed.

Theorem lookup_undefined_smoke :
  let nm : NameMap := nil in
  lookup_name nm "missing" = None.
Proof. reflexivity. Qed.

Theorem define_then_undefine_smoke :
  let nm : NameMap := nil in
  let nm' := define_name nm "x" (mkRef 0 0) in
  let nm'' := remove_name nm' "x" in
  lookup_name nm'' "x" = None.
Proof. vm_compute. reflexivity. Qed.
