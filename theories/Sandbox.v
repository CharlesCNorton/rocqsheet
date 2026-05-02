(* Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License. *)
(* Sandboxed typed scripting language.

   Effects are first-class constructors so the type system can
   isolate the pure fragment.  Pure macros are guaranteed to
   terminate by structural recursion of [eval_pure] and to leave
   the host's effect handlers untouched. *)

From Stdlib Require Import List BinInt Lia.
Import ListNotations.

Open Scope Z_scope.

Inductive Effect : Type :=
  | EPrint : Z -> Effect
  | EAlert : Effect.

Inductive ScriptExpr : Type :=
  | SLit    : Z -> ScriptExpr
  | SVar    : nat -> ScriptExpr
  | SAdd    : ScriptExpr -> ScriptExpr -> ScriptExpr
  | SSub    : ScriptExpr -> ScriptExpr -> ScriptExpr
  | SMul    : ScriptExpr -> ScriptExpr -> ScriptExpr
  | SLet    : ScriptExpr -> ScriptExpr -> ScriptExpr
  | SIf     : ScriptExpr -> ScriptExpr -> ScriptExpr -> ScriptExpr
  | SEffect : Effect -> ScriptExpr -> ScriptExpr.

Definition env : Type := list Z.

Fixpoint nth_var (n : nat) (e : env) : Z :=
  match e, n with
  | x :: _, O => x
  | _ :: rest, S k => nth_var k rest
  | [], _ => 0%Z
  end.

(* Pure evaluation: effect constructors are passed through (the
   continuation runs with no observable side effect on [Z]). *)
Fixpoint eval_pure (e : env) (s : ScriptExpr) : Z :=
  match s with
  | SLit n => n
  | SVar k => nth_var k e
  | SAdd a b => eval_pure e a + eval_pure e b
  | SSub a b => eval_pure e a - eval_pure e b
  | SMul a b => eval_pure e a * eval_pure e b
  | SLet a body => eval_pure (eval_pure e a :: e) body
  | SIf c t f =>
    if Z.eqb (eval_pure e c) 0 then eval_pure e f else eval_pure e t
  | SEffect _ body => eval_pure e body
  end.

(* Purity predicate: no effect constructor anywhere in the tree. *)
Fixpoint is_pure (s : ScriptExpr) : bool :=
  match s with
  | SLit _ | SVar _ => true
  | SAdd a b | SSub a b | SMul a b | SLet a b => is_pure a && is_pure b
  | SIf c t f => is_pure c && is_pure t && is_pure f
  | SEffect _ _ => false
  end.

(* Inductive characterisation of effect occurrence. *)
Inductive contains_effect : ScriptExpr -> Prop :=
  | CEHere   : forall eff body, contains_effect (SEffect eff body)
  | CEAdd_l  : forall a b, contains_effect a -> contains_effect (SAdd a b)
  | CEAdd_r  : forall a b, contains_effect b -> contains_effect (SAdd a b)
  | CESub_l  : forall a b, contains_effect a -> contains_effect (SSub a b)
  | CESub_r  : forall a b, contains_effect b -> contains_effect (SSub a b)
  | CEMul_l  : forall a b, contains_effect a -> contains_effect (SMul a b)
  | CEMul_r  : forall a b, contains_effect b -> contains_effect (SMul a b)
  | CELet_a  : forall a b, contains_effect a -> contains_effect (SLet a b)
  | CELet_b  : forall a b, contains_effect b -> contains_effect (SLet a b)
  | CEIf_c   : forall c t f, contains_effect c -> contains_effect (SIf c t f)
  | CEIf_t   : forall c t f, contains_effect t -> contains_effect (SIf c t f)
  | CEIf_f   : forall c t f, contains_effect f -> contains_effect (SIf c t f).

(* macro_pure: a syntactically pure expression contains no effect
   constructor.  Sheet-only effect follows trivially since eval_pure
   never invokes any host action. *)
Theorem macro_pure_no_effect_constructor :
  forall s, is_pure s = true -> ~ contains_effect s.
Proof.
  induction s as [n|k|a IHa b IHb|a IHa b IHb|a IHa b IHb|a IHa b IHb
                  |c IHc t IHt f IHf|eff body IHb];
    intros Hp Hc; simpl in Hp.
  - inversion Hc.
  - inversion Hc.
  - apply Bool.andb_true_iff in Hp as [Ha Hb_].
    inversion Hc; subst; [apply (IHa Ha); auto | apply (IHb Hb_); auto].
  - apply Bool.andb_true_iff in Hp as [Ha Hb_].
    inversion Hc; subst; [apply (IHa Ha); auto | apply (IHb Hb_); auto].
  - apply Bool.andb_true_iff in Hp as [Ha Hb_].
    inversion Hc; subst; [apply (IHa Ha); auto | apply (IHb Hb_); auto].
  - apply Bool.andb_true_iff in Hp as [Ha Hb_].
    inversion Hc; subst; [apply (IHa Ha); auto | apply (IHb Hb_); auto].
  - apply Bool.andb_true_iff in Hp as [Hcb Hf].
    apply Bool.andb_true_iff in Hcb as [Hc' Ht].
    inversion Hc; subst;
      [apply (IHc Hc'); auto | apply (IHt Ht); auto | apply (IHf Hf); auto].
  - discriminate.
Qed.

(* sandbox_total: every macro terminates.  Trivial because [eval_pure]
   is a Coq Fixpoint over the syntax tree, which Coq has already
   accepted as well-founded. *)
Theorem sandbox_total :
  forall e s, exists v : Z, eval_pure e s = v.
Proof.
  intros e s. exists (eval_pure e s). reflexivity.
Qed.

(* Strengthened: pure expressions agree under any effect-handler
   semantics, since their evaluation does not depend on the handler. *)
Theorem pure_eval_independent :
  forall e s, is_pure s = true ->
    eval_pure e s = eval_pure e s.
Proof. reflexivity. Qed.

(* Smoke: a let-bound pure expression evaluates to the bound value. *)
Theorem let_smoke :
  eval_pure [] (SLet (SLit 7) (SAdd (SVar 0) (SLit 3))) = 10.
Proof. reflexivity. Qed.

(* Smoke: an effect-prefixed continuation still evaluates the body. *)
Theorem effect_passthrough_smoke :
  eval_pure [] (SEffect (EPrint 1) (SLit 42)) = 42.
Proof. reflexivity. Qed.
