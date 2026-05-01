(* Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License. *)
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
  | KAddR    : list CellRef -> Expr -> Cont
  | KAddL    : Z -> Cont
  | KSubR    : list CellRef -> Expr -> Cont
  | KSubL    : Z -> Cont
  | KMulR    : list CellRef -> Expr -> Cont
  | KMulL    : Z -> Cont
  | KDivR    : list CellRef -> Expr -> Cont
  | KDivL    : Z -> Cont
  | KEqR     : list CellRef -> Expr -> Cont
  | KEqL     : Z -> Cont
  | KLtR     : list CellRef -> Expr -> Cont
  | KLtL     : Z -> Cont
  | KGtR     : list CellRef -> Expr -> Cont
  | KGtL     : Z -> Cont
  | KIf      : list CellRef -> Expr -> Expr -> Cont
  | KModR    : list CellRef -> Expr -> Cont
  | KModL    : Z -> Cont
  | KPowR    : list CellRef -> Expr -> Cont
  | KPowL    : Z -> Cont
  | KNot     : Cont
  | KAndR    : list CellRef -> Expr -> Cont
  | KAndL    : Z -> Cont
  | KOrR     : list CellRef -> Expr -> Cont
  | KOrL     : Z -> Cont
  | KSumNext : list CellRef -> int -> int -> int -> int -> int -> Z -> Cont
  | KIfErr   : list CellRef -> Expr -> Cont.

Inductive PC : Type :=
  | PCEval    : list CellRef -> Expr -> PC
  | PCApply   : option Z -> PC
  | PCSumStep : list CellRef -> int -> int -> int -> int -> int -> Z -> PC.

Record State : Type := mkSt
  { st_sheet : Sheet
  ; st_pc    : PC
  ; st_stack : list Cont }.

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
        | CFloat _ => inr None  (* cofix evaluator covers Z only *)
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
  | PCEval visited (EMod a b) =>
      inl (mkSt (st_sheet st) (PCEval visited a)
               (KModR visited b :: st_stack st))
  | PCEval visited (EPow a b) =>
      inl (mkSt (st_sheet st) (PCEval visited a)
               (KPowR visited b :: st_stack st))
  | PCEval visited (ENot a) =>
      inl (mkSt (st_sheet st) (PCEval visited a)
               (KNot :: st_stack st))
  | PCEval visited (EAnd a b) =>
      inl (mkSt (st_sheet st) (PCEval visited a)
               (KAndR visited b :: st_stack st))
  | PCEval visited (EOr a b) =>
      inl (mkSt (st_sheet st) (PCEval visited a)
               (KOrR visited b :: st_stack st))
  | PCEval visited (ESum tl br) =>
      let lc := cell_col_of tl in
      let hc := cell_col_of br in
      let lr := cell_row_of tl in
      let hr := cell_row_of br in
      inl (mkSt (st_sheet st)
                (PCSumStep visited lc hc lc lr hr 0%Z)
                (st_stack st))
  | PCEval visited (EAvg _ _) =>
      inr None
  | PCEval visited (ECount tl br) =>
      let lc := cell_col_of tl in
      let hc := cell_col_of br in
      let lr := cell_row_of tl in
      let hr := cell_row_of br in
      if orb (PrimInt63.ltb hc lc) (PrimInt63.ltb hr lr) then
        inl (mkSt (st_sheet st) (PCApply (Some 0%Z)) (st_stack st))
      else
        let cs := PrimInt63.add (PrimInt63.sub hc lc) 1 in
        let rs := PrimInt63.add (PrimInt63.sub hr lr) 1 in
        inl (mkSt (st_sheet st)
                  (PCApply (Some (Uint63.to_Z (PrimInt63.mul cs rs))))
                  (st_stack st))
  | PCEval visited (EIfErr a fb) =>
      inl (mkSt (st_sheet st) (PCEval visited a)
               (KIfErr visited fb :: st_stack st))
  | PCEval _ (EFloat _) => inr None
  | PCEval _ (EFAdd _ _) => inr None
  | PCEval _ (EFSub _ _) => inr None
  | PCEval _ (EFMul _ _) => inr None
  | PCEval _ (EFDiv _ _) => inr None
  | PCSumStep visited lc hc col row hr acc =>
      if PrimInt63.ltb hr row then
        inl (mkSt (st_sheet st) (PCApply (Some acc)) (st_stack st))
      else if PrimInt63.ltb hc col then
        inl (mkSt (st_sheet st)
                  (PCSumStep visited lc hc lc
                             (PrimInt63.add row 1) hr acc)
                  (st_stack st))
      else
        inl (mkSt (st_sheet st)
                  (PCEval visited (ERef (mkRef col row)))
                  (KSumNext visited lc hc col row hr acc :: st_stack st))
  | PCApply None =>
      match st_stack st with
      | KIfErr vp fb :: k' =>
          inl (mkSt (st_sheet st) (PCEval vp fb) k')
      | _ => inr None
      end
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
          if Z.eqb v 0%Z then
            inl (mkSt (st_sheet st) (PCApply None) k')
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
      | KModR vp b :: k' =>
          inl (mkSt (st_sheet st) (PCEval vp b) (KModL v :: k'))
      | KModL vL :: k' =>
          if Z.eqb v 0%Z then
            inl (mkSt (st_sheet st) (PCApply None) k')
          else inl (mkSt (st_sheet st) (PCApply (Some (Z.modulo vL v))) k')
      | KPowR vp b :: k' =>
          inl (mkSt (st_sheet st) (PCEval vp b) (KPowL v :: k'))
      | KPowL vL :: k' =>
          if Z.ltb v 0%Z then
            inl (mkSt (st_sheet st) (PCApply None) k')
          else inl (mkSt (st_sheet st) (PCApply (Some (Z.pow vL v))) k')
      | KNot :: k' =>
          inl (mkSt (st_sheet st)
                    (PCApply (Some (if Z.eqb v 0%Z then 1%Z else 0%Z))) k')
      | KAndR vp b :: k' =>
          inl (mkSt (st_sheet st) (PCEval vp b) (KAndL v :: k'))
      | KAndL vL :: k' =>
          inl (mkSt (st_sheet st)
                    (PCApply (Some (if andb (negb (Z.eqb vL 0%Z))
                                            (negb (Z.eqb v 0%Z))
                                    then 1%Z else 0%Z))) k')
      | KOrR vp b :: k' =>
          inl (mkSt (st_sheet st) (PCEval vp b) (KOrL v :: k'))
      | KOrL vL :: k' =>
          inl (mkSt (st_sheet st)
                    (PCApply (Some (if orb (negb (Z.eqb vL 0%Z))
                                           (negb (Z.eqb v 0%Z))
                                    then 1%Z else 0%Z))) k')
      | KSumNext visited lc hc col row hr acc :: k' =>
          inl (mkSt (st_sheet st)
                    (PCSumStep visited lc hc
                               (PrimInt63.add col 1) row hr
                               (Z.add acc v))
                    k')
      | KIfErr _ _ :: k' =>
          inl (mkSt (st_sheet st) (PCApply (Some v)) k')
      end
  end.

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
  | CEmpty   => Ret (Some 0%Z)
  | CLit n   => Ret (Some n)
  | CFloat _ => Ret None  (* cofix evaluator covers Z only *)
  | CForm e  => eval_co (r :: nil) s e
  end.

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

Theorem co_mod_smoke :
  let r := mkRef 0 0 in
  let s := set_cell new_sheet r
    (CForm (EMod (EInt 10%Z) (EInt 3%Z))) in
  run_n 50 (eval_cell_co s r) = Some (Some 1%Z).
Proof. vm_compute. reflexivity. Qed.

Theorem co_mod_zero :
  let r := mkRef 0 0 in
  let s := set_cell new_sheet r
    (CForm (EMod (EInt 5%Z) (EInt 0%Z))) in
  run_n 50 (eval_cell_co s r) = Some None.
Proof. vm_compute. reflexivity. Qed.

Theorem co_pow_smoke :
  let r := mkRef 0 0 in
  let s := set_cell new_sheet r
    (CForm (EPow (EInt 2%Z) (EInt 10%Z))) in
  run_n 50 (eval_cell_co s r) = Some (Some 1024%Z).
Proof. vm_compute. reflexivity. Qed.

Theorem co_pow_neg :
  let r := mkRef 0 0 in
  let s := set_cell new_sheet r
    (CForm (EPow (EInt 2%Z) (EInt (-1)%Z))) in
  run_n 50 (eval_cell_co s r) = Some None.
Proof. vm_compute. reflexivity. Qed.

Theorem co_not_zero :
  let r := mkRef 0 0 in
  let s := set_cell new_sheet r
    (CForm (ENot (EInt 0%Z))) in
  run_n 50 (eval_cell_co s r) = Some (Some 1%Z).
Proof. vm_compute. reflexivity. Qed.

Theorem co_not_nonzero :
  let r := mkRef 0 0 in
  let s := set_cell new_sheet r
    (CForm (ENot (EInt 5%Z))) in
  run_n 50 (eval_cell_co s r) = Some (Some 0%Z).
Proof. vm_compute. reflexivity. Qed.

Theorem co_and_true :
  let r := mkRef 0 0 in
  let s := set_cell new_sheet r
    (CForm (EAnd (EInt 1%Z) (EInt 2%Z))) in
  run_n 50 (eval_cell_co s r) = Some (Some 1%Z).
Proof. vm_compute. reflexivity. Qed.

Theorem co_and_false :
  let r := mkRef 0 0 in
  let s := set_cell new_sheet r
    (CForm (EAnd (EInt 0%Z) (EInt 1%Z))) in
  run_n 50 (eval_cell_co s r) = Some (Some 0%Z).
Proof. vm_compute. reflexivity. Qed.

Theorem co_or_true :
  let r := mkRef 0 0 in
  let s := set_cell new_sheet r
    (CForm (EOr (EInt 0%Z) (EInt 1%Z))) in
  run_n 50 (eval_cell_co s r) = Some (Some 1%Z).
Proof. vm_compute. reflexivity. Qed.

Theorem co_or_false :
  let r := mkRef 0 0 in
  let s := set_cell new_sheet r
    (CForm (EOr (EInt 0%Z) (EInt 0%Z))) in
  run_n 50 (eval_cell_co s r) = Some (Some 0%Z).
Proof. vm_compute. reflexivity. Qed.

Theorem co_sum_row :
  let s := set_cell new_sheet (mkRef 0 0) (CLit 1%Z) in
  let s := set_cell s (mkRef 1 0) (CLit 2%Z) in
  let s := set_cell s (mkRef 2 0) (CLit 3%Z) in
  let dst := mkRef 0 5 in
  let s := set_cell s dst (CForm (ESum (mkRef 0 0) (mkRef 2 0))) in
  run_n 200 (eval_cell_co s dst) = Some (Some 6%Z).
Proof. vm_compute. reflexivity. Qed.

Theorem co_sum_rect :
  let s := set_cell new_sheet (mkRef 0 0) (CLit 1%Z) in
  let s := set_cell s (mkRef 1 0) (CLit 2%Z) in
  let s := set_cell s (mkRef 0 1) (CLit 3%Z) in
  let s := set_cell s (mkRef 1 1) (CLit 4%Z) in
  let dst := mkRef 0 5 in
  let s := set_cell s dst (CForm (ESum (mkRef 0 0) (mkRef 1 1))) in
  run_n 300 (eval_cell_co s dst) = Some (Some 10%Z).
Proof. vm_compute. reflexivity. Qed.

Theorem co_sum_singleton :
  let r := mkRef 4 4 in
  let dst := mkRef 0 5 in
  let s := set_cell new_sheet r (CLit 42%Z) in
  let s := set_cell s dst (CForm (ESum r r)) in
  run_n 100 (eval_cell_co s dst) = Some (Some 42%Z).
Proof. vm_compute. reflexivity. Qed.

Theorem co_iferror_some_eq_first :
  let r := mkRef 0 0 in
  let s := set_cell new_sheet r
    (CForm (EIfErr (EInt 42%Z) (EInt 99%Z))) in
  run_n 50 (eval_cell_co s r) = Some (Some 42%Z).
Proof. vm_compute. reflexivity. Qed.

Theorem co_iferror_traps_divzero :
  let r := mkRef 0 0 in
  let s := set_cell new_sheet r
    (CForm (EIfErr (EDiv (EInt 1%Z) (EInt 0%Z)) (EInt 99%Z))) in
  run_n 50 (eval_cell_co s r) = Some (Some 99%Z).
Proof. vm_compute. reflexivity. Qed.

Theorem co_iferror_traps_cycle :
  let r0 := mkRef 0 0 in
  let r1 := mkRef 1 0 in
  let s := set_cell new_sheet r0 (CForm (ERef r0)) in
  let s := set_cell s r1
    (CForm (EIfErr (ERef r0) (EInt 7%Z))) in
  run_n 50 (eval_cell_co s r1) = Some (Some 7%Z).
Proof. vm_compute. reflexivity. Qed.
