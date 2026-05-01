(* Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License. *)
(* Coinductive evaluator for the Rocqsheet kernel.  Cycles are
   caught by the visited-set check inside [trans], not by fuel.
   Theorems use a bounded [run_n] driver so [vm_compute] can
   discharge closed cases.  Not extracted. *)

From Stdlib Require Import List BinInt.
From Corelib Require Import PrimInt63.
From Crane Require Import Mapping.NatIntStd Mapping.ZInt.
From Crane Require Import Monads.ITreeReified.
From Rocqsheet Require Import Rocqsheet.
Import ListNotations.
Import Rocqsheet.

Open Scope int63.

Definition NoE : Type -> Type := fun _ => Empty_set.

Inductive Cont : Type :=
  | KAddR  : list CellRef -> Expr -> Cont
  | KAddL  : Z -> Cont
  | KSubR  : list CellRef -> Expr -> Cont
  | KSubL  : Z -> Cont
  | KMulR  : list CellRef -> Expr -> Cont
  | KMulL  : Z -> Cont
  | KDivR  : list CellRef -> Expr -> Cont
  | KDivL  : Z -> Cont
  | KEqR   : list CellRef -> Expr -> Cont
  | KEqL   : Z -> Cont
  | KLtR   : list CellRef -> Expr -> Cont
  | KLtL   : Z -> Cont
  | KGtR   : list CellRef -> Expr -> Cont
  | KGtL   : Z -> Cont
  | KIf    : list CellRef -> Expr -> Expr -> Cont.

Inductive PC : Type :=
  | PCEval  : list CellRef -> Expr -> PC
  | PCApply : option Z -> PC.

Record State : Type := mkSt
  { st_sheet : Sheet
  ; st_pc    : PC
  ; st_stack : list Cont }.

(* One transition: either a successor state or a terminal value. *)
Definition trans (st : State) : State + option Z :=
  match st_pc st with
  | PCEval visited (EInt n) =>
      inl (mkSt (st_sheet st) (PCApply (Some n)) (st_stack st))
  | PCEval visited (ERef r) =>
      if mem_cellref r visited then
        inl (mkSt (st_sheet st) (PCApply None) (st_stack st))
      else
        match get_cell (st_sheet st) r with
        | CEmpty   => inl (mkSt (st_sheet st) (PCApply (Some 0%Z)) (st_stack st))
        | CLit n   => inl (mkSt (st_sheet st) (PCApply (Some n)) (st_stack st))
        | CForm e' => inl (mkSt (st_sheet st)
                                (PCEval (r :: visited) e') (st_stack st))
        end
  | PCEval visited (EAdd a b) =>
      inl (mkSt (st_sheet st) (PCEval visited a)
               (KAddR visited b :: st_stack st))
  | PCEval visited (ESub a b) =>
      inl (mkSt (st_sheet st) (PCEval visited a)
               (KSubR visited b :: st_stack st))
  | PCEval visited (EMul a b) =>
      inl (mkSt (st_sheet st) (PCEval visited a)
               (KMulR visited b :: st_stack st))
  | PCEval visited (EDiv a b) =>
      inl (mkSt (st_sheet st) (PCEval visited a)
               (KDivR visited b :: st_stack st))
  | PCEval visited (EEq a b) =>
      inl (mkSt (st_sheet st) (PCEval visited a)
               (KEqR visited b :: st_stack st))
  | PCEval visited (ELt a b) =>
      inl (mkSt (st_sheet st) (PCEval visited a)
               (KLtR visited b :: st_stack st))
  | PCEval visited (EGt a b) =>
      inl (mkSt (st_sheet st) (PCEval visited a)
               (KGtR visited b :: st_stack st))
  | PCEval visited (EIf c t e) =>
      inl (mkSt (st_sheet st) (PCEval visited c)
               (KIf visited t e :: st_stack st))
  (* The cofix machine pre-dates EMod/EPow/ENot/EAnd/EOr/ESum.
     Cofix support for those constructors would mean new
     continuations and (for ESum) a separate sum-walking sub-state.
     They terminate the trampoline with [None] for now; the five
     closed-term theorems below are all in the original
     sub-language and remain provable. *)
  | PCEval _ (EMod _ _) | PCEval _ (EPow _ _)
  | PCEval _ (ENot _)   | PCEval _ (EAnd _ _)
  | PCEval _ (EOr  _ _) | PCEval _ (ESum _ _) =>
      inr None
  | PCApply None =>
      inr None
  | PCApply (Some v) =>
      match st_stack st with
      | [] => inr (Some v)
      | KAddR vp b :: k' =>
          inl (mkSt (st_sheet st) (PCEval vp b) (KAddL v :: k'))
      | KAddL vL :: k' =>
          inl (mkSt (st_sheet st) (PCApply (Some (Z.add vL v))) k')
      | KSubR vp b :: k' =>
          inl (mkSt (st_sheet st) (PCEval vp b) (KSubL v :: k'))
      | KSubL vL :: k' =>
          inl (mkSt (st_sheet st) (PCApply (Some (Z.sub vL v))) k')
      | KMulR vp b :: k' =>
          inl (mkSt (st_sheet st) (PCEval vp b) (KMulL v :: k'))
      | KMulL vL :: k' =>
          inl (mkSt (st_sheet st) (PCApply (Some (Z.mul vL v))) k')
      | KDivR vp b :: k' =>
          inl (mkSt (st_sheet st) (PCEval vp b) (KDivL v :: k'))
      | KDivL vL :: k' =>
          if Z.eqb v 0%Z then inr None
          else inl (mkSt (st_sheet st) (PCApply (Some (Z.div vL v))) k')
      | KEqR vp b :: k' =>
          inl (mkSt (st_sheet st) (PCEval vp b) (KEqL v :: k'))
      | KEqL vL :: k' =>
          inl (mkSt (st_sheet st)
                    (PCApply (Some (if Z.eqb vL v then 1%Z else 0%Z))) k')
      | KLtR vp b :: k' =>
          inl (mkSt (st_sheet st) (PCEval vp b) (KLtL v :: k'))
      | KLtL vL :: k' =>
          inl (mkSt (st_sheet st)
                    (PCApply (Some (if Z.ltb vL v then 1%Z else 0%Z))) k')
      | KGtR vp b :: k' =>
          inl (mkSt (st_sheet st) (PCEval vp b) (KGtL v :: k'))
      | KGtL vL :: k' =>
          inl (mkSt (st_sheet st)
                    (PCApply (Some (if Z.gtb vL v then 1%Z else 0%Z))) k')
      | KIf vp t e :: k' =>
          if Z.eqb v 0%Z then
            inl (mkSt (st_sheet st) (PCEval vp e) k')
          else
            inl (mkSt (st_sheet st) (PCEval vp t) k')
      end
  end.

(* The recursive call sits directly under [Tau] for guardedness. *)
CoFixpoint step (st : State) : itree NoE (option Z) :=
  match trans st with
  | inl st' => Tau (step st')
  | inr v   => Ret v
  end.

Definition eval_co (visited : list CellRef) (s : Sheet) (e : Expr)
  : itree NoE (option Z) :=
  step (mkSt s (PCEval visited e) []).

Definition eval_cell_co (s : Sheet) (r : CellRef) : itree NoE (option Z) :=
  match get_cell s r with
  | CEmpty => Ret (Some 0%Z)
  | CLit n => Ret (Some n)
  | CForm e => eval_co (r :: nil) s e
  end.

(* Bounded driver: takes up to [n] Tau steps.  [Vis] is unreachable
   because [NoE] is empty. *)
Fixpoint run_n (n : nat) (t : itree NoE (option Z)) : option (option Z) :=
  match n with
  | O => None
  | S n' =>
    match observe t with
    | RetF v => Some v
    | TauF t' => run_n n' t'
    | _ => None
    end
  end.

(* --- Closed-term theorems --- *)

Theorem co_smoke :
  let a1 := mkRef 0 0 in
  let b1 := mkRef 1 0 in
  let c1 := mkRef 2 0 in
  let s0 := new_sheet in
  let s1 := set_cell s0 a1 (CLit 2%Z) in
  let s2 := set_cell s1 b1 (CLit 3%Z) in
  let s3 := set_cell s2 c1
    (CForm (EMul (EAdd (ERef a1) (ERef b1)) (EInt 7%Z))) in
  run_n 200 (eval_cell_co s3 c1) = Some (Some 35%Z).
Proof. vm_compute. reflexivity. Qed.

Theorem co_self_cycle :
  let r := mkRef 0 0 in
  let s := set_cell new_sheet r (CForm (ERef r)) in
  run_n 50 (eval_cell_co s r) = Some None.
Proof. vm_compute. reflexivity. Qed.

Theorem co_divzero :
  let r := mkRef 0 0 in
  let s := set_cell new_sheet r
    (CForm (EDiv (EInt 1%Z) (EInt 0%Z))) in
  run_n 50 (eval_cell_co s r) = Some None.
Proof. vm_compute. reflexivity. Qed.

Theorem co_if_then :
  let r := mkRef 0 0 in
  let s := set_cell new_sheet r
    (CForm (EIf (EInt 1%Z) (EInt 7%Z) (EInt 99%Z))) in
  run_n 50 (eval_cell_co s r) = Some (Some 7%Z).
Proof. vm_compute. reflexivity. Qed.

Theorem co_if_else :
  let r := mkRef 0 0 in
  let s := set_cell new_sheet r
    (CForm (EIf (EInt 0%Z) (EInt 7%Z) (EInt 99%Z))) in
  run_n 50 (eval_cell_co s r) = Some (Some 99%Z).
Proof. vm_compute. reflexivity. Qed.
