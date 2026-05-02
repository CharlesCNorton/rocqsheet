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

(* --- Ad-hoc experiments added during ingestion ----------------- *)

(* Gauss: 1..n = n*(n+1)/2.  Holds for the closed form at n=500. *)
Theorem deep_500_is_gauss :
  let n := 500%Z in
  let r := mkRef 0 0 in
  let s := set_cell new_sheet r (CForm (deep_add 500)) in
  eval_cell DEFAULT_FUEL s r = EVal (Z.div (Z.mul n (Z.add n 1)) 2).
Proof. vm_compute. reflexivity. Qed.

(* SUM over a 5x5 block of 1..25 yields 325 (sum 1..25 = 25*26/2). *)
Definition fill_5x5 (s : Sheet) : Sheet :=
  let s := set_cell s (mkRef 0 0) (CLit 1%Z) in
  let s := set_cell s (mkRef 1 0) (CLit 2%Z) in
  let s := set_cell s (mkRef 2 0) (CLit 3%Z) in
  let s := set_cell s (mkRef 3 0) (CLit 4%Z) in
  let s := set_cell s (mkRef 4 0) (CLit 5%Z) in
  let s := set_cell s (mkRef 0 1) (CLit 6%Z) in
  let s := set_cell s (mkRef 1 1) (CLit 7%Z) in
  let s := set_cell s (mkRef 2 1) (CLit 8%Z) in
  let s := set_cell s (mkRef 3 1) (CLit 9%Z) in
  let s := set_cell s (mkRef 4 1) (CLit 10%Z) in
  let s := set_cell s (mkRef 0 2) (CLit 11%Z) in
  let s := set_cell s (mkRef 1 2) (CLit 12%Z) in
  let s := set_cell s (mkRef 2 2) (CLit 13%Z) in
  let s := set_cell s (mkRef 3 2) (CLit 14%Z) in
  let s := set_cell s (mkRef 4 2) (CLit 15%Z) in
  let s := set_cell s (mkRef 0 3) (CLit 16%Z) in
  let s := set_cell s (mkRef 1 3) (CLit 17%Z) in
  let s := set_cell s (mkRef 2 3) (CLit 18%Z) in
  let s := set_cell s (mkRef 3 3) (CLit 19%Z) in
  let s := set_cell s (mkRef 4 3) (CLit 20%Z) in
  let s := set_cell s (mkRef 0 4) (CLit 21%Z) in
  let s := set_cell s (mkRef 1 4) (CLit 22%Z) in
  let s := set_cell s (mkRef 2 4) (CLit 23%Z) in
  let s := set_cell s (mkRef 3 4) (CLit 24%Z) in
  let s := set_cell s (mkRef 4 4) (CLit 25%Z) in
  s.

Theorem sum_5x5_smoke :
  let dst := mkRef 5 0 in
  let s := fill_5x5 new_sheet in
  let s := set_cell s dst (CForm (ESum (mkRef 0 0) (mkRef 4 4))) in
  eval_cell DEFAULT_FUEL s dst = EVal 325%Z.
Proof. vm_compute. reflexivity. Qed.

(* SUM treats CEmpty as 0: punching a hole in the middle drops the
   sum by exactly the cleared cell's value. *)
Theorem sum_5x5_with_hole :
  let dst := mkRef 5 0 in
  let s := fill_5x5 new_sheet in
  let s := set_cell s (mkRef 2 2) CEmpty in   (* clears the middle 13 *)
  let s := set_cell s dst (CForm (ESum (mkRef 0 0) (mkRef 4 4))) in
  eval_cell DEFAULT_FUEL s dst = EVal (325 - 13)%Z.
Proof. vm_compute. reflexivity. Qed.

(* MIN + MAX = 1 + 25 = 26 over the 5x5 block, exercised against the
   IFERROR trap so that any divergence becomes a visible -1. *)
Theorem min_plus_max_5x5_smoke :
  let dst := mkRef 5 1 in
  let s := fill_5x5 new_sheet in
  let s := set_cell s dst
    (CForm (EIfErr
              (EAdd (EMin (mkRef 0 0) (mkRef 4 4))
                    (EMax (mkRef 0 0) (mkRef 4 4)))
              (EInt (-1)%Z))) in
  eval_cell DEFAULT_FUEL s dst = EVal 26%Z.
Proof. vm_compute. reflexivity. Qed.

(* IFERROR catches a nested division-by-zero. *)
Theorem iferror_traps_nested_divzero :
  let dst := mkRef 0 0 in
  let s := set_cell new_sheet dst
    (CForm (EIfErr
              (EAdd (EInt 1%Z) (EDiv (EInt 10%Z) (EInt 0%Z)))
              (EInt 999%Z))) in
  eval_cell DEFAULT_FUEL s dst = EVal 999%Z.
Proof. vm_compute. reflexivity. Qed.

(* Cofix and fuel evaluators agree on a Gauss sum at n=100. *)
Theorem deep_100_corr :
  let r := mkRef 0 0 in
  let s := set_cell new_sheet r (CForm (deep_add 100)) in
  eval_cell DEFAULT_FUEL s r = EVal 5050%Z
  /\ run_n 5000 (eval_cell_co s r) = Some (Some 5050%Z).
Proof. vm_compute. split; reflexivity. Qed.
