From Rocqsheet Require Import Rocqsheet.
From Rocqsheet Require Import RocqsheetCofix.
From Stdlib Require Import List BinInt.
From Stdlib.Numbers.Cyclic.Int63 Require Import Uint63.
Import ListNotations.
Import Rocqsheet.
Open Scope int63.

(* ((((0 + 1) + 2) + ...) + n) as a Coq Fixpoint over Expr. *)
Fixpoint deep_add (n : nat) : Expr :=
  match n with
  | O => EInt 0%Z
  | S n' => EAdd (deep_add n') (EInt (Z.of_nat (S n')))
  end.

(* 1+2+...+50 = 1275; checked by both evaluators. *)
Theorem deep_50_fuel :
  let r := mkRef 0 0 in
  let s := set_cell new_sheet r (CForm (deep_add 50)) in
  eval_cell DEFAULT_FUEL s r = EVal 1275%Z.
Proof. vm_compute. reflexivity. Qed.

Theorem deep_50_cofix :
  let r := mkRef 0 0 in
  let s := set_cell new_sheet r (CForm (deep_add 50)) in
  run_n 2000 (eval_cell_co s r) = Some (Some 1275%Z).
Proof. vm_compute. reflexivity. Qed.

(* 1+2+...+500 = 125250. *)
Theorem deep_500_fuel :
  let r := mkRef 0 0 in
  let s := set_cell new_sheet r (CForm (deep_add 500)) in
  eval_cell DEFAULT_FUEL s r = EVal 125250%Z.
Proof. vm_compute. reflexivity. Qed.

Theorem deep_500_cofix :
  let r := mkRef 0 0 in
  let s := set_cell new_sheet r (CForm (deep_add 500)) in
  run_n 50000 (eval_cell_co s r) = Some (Some 125250%Z).
Proof. vm_compute. reflexivity. Qed.

(* Reference chain: A1 = 0, A2 = A1 + 1, ..., An+1 = An + 1.
   Top of an n-deep chain should evaluate to n. *)
Fixpoint chain_sheet (n : nat) (s : Sheet) : Sheet :=
  match n with
  | O => set_cell s (mkRef 0 0) (CLit 0%Z)
  | S k =>
    let s := chain_sheet k s in
    set_cell s (mkRef 0 (Uint63.of_Z (Z.of_nat (S k))))
             (CForm (EAdd (ERef (mkRef 0 (Uint63.of_Z (Z.of_nat k))))
                          (EInt 1%Z)))
  end.

Theorem chain_30_fuel :
  let s := chain_sheet 30 new_sheet in
  let top := mkRef 0 (Uint63.of_Z 30%Z) in
  eval_cell DEFAULT_FUEL s top = EVal 30%Z.
Proof. vm_compute. reflexivity. Qed.

Theorem chain_30_cofix :
  let s := chain_sheet 30 new_sheet in
  let top := mkRef 0 (Uint63.of_Z 30%Z) in
  run_n 5000 (eval_cell_co s top) = Some (Some 30%Z).
Proof. vm_compute. reflexivity. Qed.
