(* Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License. *)
From Corelib Require Import PrimString PrimInt63.
From Stdlib Require Import List BinInt.
From Crane Require Import Mapping.Std Mapping.ZInt.
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

(* Named-cell evaluator: resolve a name, then evaluate the cell.
   When the name is unbound, evaluation is an error. *)
Definition eval_named (nm : NameMap) (fuel : nat) (s : Sheet)
                      (n : PrimString.string) : EvalResult :=
  match lookup_name nm n with
  | Some r => eval_at_ref fuel nil s r
  | None => EErr
  end.

Theorem eval_named_eq :
  forall nm n r fuel s,
    lookup_name nm n = Some r ->
    eval_named nm fuel s n = eval_at_ref fuel nil s r.
Proof.
  intros nm n r fuel s Hlk.
  unfold eval_named. rewrite Hlk. reflexivity.
Qed.

Theorem eval_named_unbound :
  forall nm n fuel s,
    lookup_name nm n = None ->
    eval_named nm fuel s n = EErr.
Proof.
  intros. unfold eval_named. rewrite H. reflexivity.
Qed.

(* Smoke: defining a name and then evaluating through it returns
   the same result as evaluating the named cell directly. *)
Theorem eval_named_after_define_smoke :
  let nm := define_name nil "x" (mkRef 0 0) in
  let s := set_cell new_sheet (mkRef 0 0) (CLit 99%Z) in
  eval_named nm DEFAULT_FUEL s "x" = EVal 99%Z.
Proof. vm_compute. reflexivity. Qed.
