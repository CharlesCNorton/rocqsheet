(* Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License. *)
(* Standalone proof file for derivable lemmas about [eval_expr] and
   the surrounding kernel.  Definitions live in Rocqsheet.v;
   theorems here build on top of it without re-extracting. *)

From Stdlib Require Import List BinInt Lia.
From Stdlib.Numbers.Cyclic.Int63 Require Import Uint63.
From Corelib Require Import PrimInt63 Uint63Axioms.
From Crane Require Import Mapping.NatIntStd Mapping.ZInt.
From Rocqsheet Require Import Rocqsheet.
Import ListNotations.
Import Rocqsheet.

Open Scope int63.

(* Adding zero on the right preserves the value. *)
Theorem eval_add_zero_r : forall a fuel visited s,
  eval_expr (S (S fuel)) visited s (EAdd (EInt a) (EInt 0%Z)) = EVal a.
Proof.
  intros. simpl. rewrite Z.add_0_r. reflexivity.
Qed.

(* Multiplication by one on the right preserves the value. *)
Theorem eval_mul_one_r : forall a fuel visited s,
  eval_expr (S (S fuel)) visited s (EMul (EInt a) (EInt 1%Z)) = EVal a.
Proof.
  intros. simpl. rewrite Z.mul_1_r. reflexivity.
Qed.

(* Subtracting itself yields zero. *)
Theorem eval_sub_self : forall a fuel visited s,
  eval_expr (S (S fuel)) visited s (ESub (EInt a) (EInt a)) = EVal 0%Z.
Proof.
  intros. simpl. rewrite Z.sub_diag. reflexivity.
Qed.

(* Empty cell evaluates to zero regardless of the formula context. *)
Theorem eval_cell_empty_is_zero : forall fuel s r,
  get_cell s r = CEmpty -> eval_cell fuel s r = EVal 0%Z.
Proof.
  intros fuel s r H. apply eval_empty. exact H.
Qed.

(* Adding identical operands doubles the result. *)
Theorem eval_add_self : forall a fuel visited s,
  eval_expr (S (S fuel)) visited s (EAdd (EInt a) (EInt a))
  = EVal (Z.add a a).
Proof. reflexivity. Qed.

(* Multiplying by zero yields zero. *)
Theorem eval_mul_zero_l_proof : forall a fuel visited s,
  eval_expr (S (S fuel)) visited s (EMul (EInt 0%Z) (EInt a)) = EVal 0%Z.
Proof. reflexivity. Qed.

Theorem eval_mul_zero_r_proof : forall a fuel visited s,
  eval_expr (S (S fuel)) visited s (EMul (EInt a) (EInt 0%Z)) = EVal 0%Z.
Proof.
  intros. simpl. rewrite Z.mul_0_r. reflexivity.
Qed.

(* Sub then add the same value recovers the original. *)
Theorem eval_sub_add_cancel : forall a b fuel visited s,
  eval_expr (S (S (S fuel))) visited s
    (EAdd (ESub (EInt a) (EInt b)) (EInt b))
  = EVal a.
Proof.
  intros. simpl. f_equal. lia.
Qed.

(* IF on a positive literal takes the then-branch. *)
Theorem eval_if_pos_lit_smoke :
  let s := new_sheet in
  eval_expr 5 nil s (EIf (EInt 7%Z) (EInt 1%Z) (EInt 2%Z)) = EVal 1%Z.
Proof. vm_compute. reflexivity. Qed.

(* IF on a negative literal takes the then-branch. *)
Theorem eval_if_neg_lit_smoke :
  let s := new_sheet in
  eval_expr 5 nil s (EIf (EInt (-3)%Z) (EInt 1%Z) (EInt 2%Z)) = EVal 1%Z.
Proof. vm_compute. reflexivity. Qed.

(* IF on zero takes the else-branch. *)
Theorem eval_if_zero_lit_smoke :
  let s := new_sheet in
  eval_expr 5 nil s (EIf (EInt 0%Z) (EInt 1%Z) (EInt 2%Z)) = EVal 2%Z.
Proof. vm_compute. reflexivity. Qed.

(* Universal algebraic identities over arbitrary subexpressions whose
   evaluation succeeds, lifted from the closed-form variants in
   Rocqsheet.v via the compositional helpers. *)

Theorem eval_add_comm_universal :
  forall fuel visited s a b va vb,
    eval_expr fuel visited s a = EVal va ->
    eval_expr fuel visited s b = EVal vb ->
    eval_expr (S fuel) visited s (EAdd a b)
    = eval_expr (S fuel) visited s (EAdd b a).
Proof.
  intros fuel visited s a b va vb Ha Hb.
  rewrite (eval_expr_compositional_add fuel visited s a b va vb Ha Hb).
  rewrite (eval_expr_compositional_add fuel visited s b a vb va Hb Ha).
  f_equal. apply Z.add_comm.
Qed.

Theorem eval_mul_comm_universal :
  forall fuel visited s a b va vb,
    eval_expr fuel visited s a = EVal va ->
    eval_expr fuel visited s b = EVal vb ->
    eval_expr (S fuel) visited s (EMul a b)
    = eval_expr (S fuel) visited s (EMul b a).
Proof.
  intros fuel visited s a b va vb Ha Hb.
  rewrite (eval_expr_compositional_mul fuel visited s a b va vb Ha Hb).
  rewrite (eval_expr_compositional_mul fuel visited s b a vb va Hb Ha).
  f_equal. apply Z.mul_comm.
Qed.

Theorem eval_add_assoc_universal :
  forall fuel visited s a b c va vb vc,
    eval_expr fuel visited s a = EVal va ->
    eval_expr fuel visited s b = EVal vb ->
    eval_expr fuel visited s c = EVal vc ->
    eval_expr (S (S fuel)) visited s (EAdd (EAdd a b) c)
    = eval_expr (S (S fuel)) visited s (EAdd a (EAdd b c)).
Proof.
  intros. eapply eval_add_assoc_tree; eauto.
Qed.

Theorem eval_mul_assoc_universal :
  forall fuel visited s a b c va vb vc,
    eval_expr fuel visited s a = EVal va ->
    eval_expr fuel visited s b = EVal vb ->
    eval_expr fuel visited s c = EVal vc ->
    eval_expr (S (S fuel)) visited s (EMul (EMul a b) c)
    = eval_expr (S (S fuel)) visited s (EMul a (EMul b c)).
Proof.
  intros. eapply eval_mul_assoc_tree; eauto.
Qed.

Theorem eval_sub_self_universal :
  forall fuel visited s a va,
    eval_expr fuel visited s a = EVal va ->
    eval_expr (S fuel) visited s (ESub a a) = EVal 0%Z.
Proof.
  intros fuel visited s a va Ha.
  rewrite (eval_expr_compositional_sub fuel visited s a a va va Ha Ha).
  f_equal. apply Z.sub_diag.
Qed.

Lemma eval_bool_lit_inv : forall fuel visited s b,
  eval_expr (S fuel) visited s (EBool b) = EValB b.
Proof. reflexivity. Qed.

Theorem eval_band_comm_universal :
  forall fuel visited s a b ba bb,
    eval_expr fuel visited s a = EValB ba ->
    eval_expr fuel visited s b = EValB bb ->
    eval_expr (S fuel) visited s (EBAnd a b)
    = eval_expr (S fuel) visited s (EBAnd b a).
Proof.
  intros fuel visited s a b ba bb Ha Hb.
  simpl. rewrite Ha, Hb. f_equal. apply Bool.andb_comm.
Qed.

Theorem eval_bor_comm_universal :
  forall fuel visited s a b ba bb,
    eval_expr fuel visited s a = EValB ba ->
    eval_expr fuel visited s b = EValB bb ->
    eval_expr (S fuel) visited s (EBOr a b)
    = eval_expr (S fuel) visited s (EBOr b a).
Proof.
  intros fuel visited s a b ba bb Ha Hb.
  simpl. rewrite Ha, Hb. f_equal. apply Bool.orb_comm.
Qed.

Theorem eval_bnot_involutive_universal :
  forall fuel visited s a b,
    eval_expr fuel visited s a = EValB b ->
    eval_expr (S (S fuel)) visited s (EBNot (EBNot a)) = EValB b.
Proof.
  intros fuel visited s a b Ha.
  simpl. rewrite Ha. simpl. rewrite Bool.negb_involutive. reflexivity.
Qed.

Theorem eval_de_morgan_universal :
  forall fuel visited s a b ba bb,
    eval_expr fuel visited s a = EValB ba ->
    eval_expr fuel visited s b = EValB bb ->
    eval_expr (S (S fuel)) visited s (EBNot (EBAnd a b))
    = eval_expr (S (S fuel)) visited s (EBOr (EBNot a) (EBNot b)).
Proof.
  intros fuel visited s a b ba bb Ha Hb. simpl.
  rewrite Ha, Hb. simpl. rewrite Bool.negb_andb. reflexivity.
Qed.

From Stdlib.Strings Require Import PrimStringAxioms.

Lemma to_list_inj : forall a b,
  PrimStringAxioms.to_list a = PrimStringAxioms.to_list b -> a = b.
Proof.
  intros a b H.
  rewrite <- (of_to_list a), <- (of_to_list b).
  rewrite H. reflexivity.
Qed.

Lemma cat_empty_l : forall a, PrimString.cat ""%pstring a = a.
Proof.
  intros a. apply to_list_inj.
  rewrite cat_spec.
  assert (Hlen : Datatypes.length (PrimStringAxioms.to_list a) <=
                 Uint63.to_nat PrimString.max_length) by apply to_list_length.
  cbn [PrimStringAxioms.to_list app].
  apply List.firstn_all2. exact Hlen.
Qed.

Lemma cat_empty_r : forall a, PrimString.cat a ""%pstring = a.
Proof.
  intros a. apply to_list_inj.
  rewrite cat_spec.
  rewrite List.app_nil_r.
  apply List.firstn_all2. apply to_list_length.
Qed.

(* Associativity holds whenever the combined length stays within
   PrimString.max_length; truncation breaks it otherwise. *)
Lemma cat_assoc_bounded : forall a b c,
  Datatypes.length (PrimStringAxioms.to_list a)
    + Datatypes.length (PrimStringAxioms.to_list b)
    + Datatypes.length (PrimStringAxioms.to_list c)
    <= Uint63.to_nat PrimString.max_length ->
  PrimString.cat (PrimString.cat a b) c
  = PrimString.cat a (PrimString.cat b c).
Proof.
  intros a b c Hbound. apply to_list_inj.
  rewrite !cat_spec.
  assert (Hab : Datatypes.length
                  (PrimStringAxioms.to_list a ++ PrimStringAxioms.to_list b)
                <= Uint63.to_nat PrimString.max_length).
  { rewrite List.length_app. lia. }
  assert (Hbc : Datatypes.length
                  (PrimStringAxioms.to_list b ++ PrimStringAxioms.to_list c)
                <= Uint63.to_nat PrimString.max_length).
  { rewrite List.length_app. lia. }
  rewrite (@List.firstn_all2 _ _ _ Hab).
  rewrite (@List.firstn_all2 _ _ _ Hbc).
  rewrite List.app_assoc.
  reflexivity.
Qed.

Lemma eval_fuel_monotone_evals :
  forall fuel e fuel' visited s sv,
    fuel <= fuel' ->
    eval_expr fuel visited s e = EValS sv ->
    eval_expr fuel' visited s e = EValS sv.
Proof.
  intros fuel e fuel' visited s sv Hle Hev.
  rewrite (proj1 (fuel_monotone_all fuel) e fuel' visited s Hle)
    by (rewrite Hev; congruence).
  exact Hev.
Qed.

Lemma eval_compositional_concat :
  forall fuel visited s a b sa sb,
    eval_expr fuel visited s a = EValS sa ->
    eval_expr fuel visited s b = EValS sb ->
    eval_expr (S fuel) visited s (EConcat a b) = EValS (PrimString.cat sa sb).
Proof.
  intros fuel visited s a b sa sb Ha Hb.
  simpl. rewrite Ha, Hb. reflexivity.
Qed.

Theorem eval_concat_empty_l_universal :
  forall fuel visited s a sa,
    eval_expr fuel visited s a = EValS sa ->
    eval_expr (S (S fuel)) visited s (EConcat (EStr ""%pstring) a) = EValS sa.
Proof.
  intros fuel visited s a sa Ha.
  rewrite (eval_compositional_concat (S fuel) visited s
             (EStr ""%pstring) a ""%pstring sa).
  - rewrite cat_empty_l. reflexivity.
  - reflexivity.
  - apply (eval_fuel_monotone_evals fuel a (S fuel) visited s sa); [lia|exact Ha].
Qed.

Theorem eval_concat_empty_r_universal :
  forall fuel visited s a sa,
    eval_expr fuel visited s a = EValS sa ->
    eval_expr (S (S fuel)) visited s (EConcat a (EStr ""%pstring)) = EValS sa.
Proof.
  intros fuel visited s a sa Ha.
  rewrite (eval_compositional_concat (S fuel) visited s
             a (EStr ""%pstring) sa ""%pstring).
  - rewrite cat_empty_r. reflexivity.
  - apply (eval_fuel_monotone_evals fuel a (S fuel) visited s sa); [lia|exact Ha].
  - reflexivity.
Qed.

Theorem eval_concat_assoc_universal_bounded :
  forall fuel visited s a b c sa sb sc,
    eval_expr fuel visited s a = EValS sa ->
    eval_expr fuel visited s b = EValS sb ->
    eval_expr fuel visited s c = EValS sc ->
    Datatypes.length (PrimStringAxioms.to_list sa)
      + Datatypes.length (PrimStringAxioms.to_list sb)
      + Datatypes.length (PrimStringAxioms.to_list sc)
      <= Uint63.to_nat PrimString.max_length ->
    eval_expr (S (S fuel)) visited s (EConcat (EConcat a b) c)
    = eval_expr (S (S fuel)) visited s (EConcat a (EConcat b c)).
Proof.
  intros fuel visited s a b c sa sb sc Ha Hb Hc Hbound.
  pose proof (eval_fuel_monotone_evals fuel a (S fuel) visited s sa
                ltac:(lia) Ha) as Ha'.
  pose proof (eval_fuel_monotone_evals fuel b (S fuel) visited s sb
                ltac:(lia) Hb) as Hb'.
  pose proof (eval_fuel_monotone_evals fuel c (S fuel) visited s sc
                ltac:(lia) Hc) as Hc'.
  pose proof (eval_compositional_concat fuel visited s a b sa sb Ha Hb) as Hab.
  pose proof (eval_compositional_concat fuel visited s b c sb sc Hb Hc) as Hbc.
  pose proof (eval_compositional_concat (S fuel) visited s
                (EConcat a b) c (PrimString.cat sa sb) sc Hab Hc') as Hlhs.
  pose proof (eval_compositional_concat (S fuel) visited s
                a (EConcat b c) sa (PrimString.cat sb sc) Ha' Hbc) as Hrhs.
  rewrite Hlhs, Hrhs. f_equal. apply cat_assoc_bounded. exact Hbound.
Qed.

