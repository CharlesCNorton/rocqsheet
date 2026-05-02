(* Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License. *)
(* Property-based regressions over per-column propositions.  A
   [SupportedProp] is a syntactic class of propositions that map to
   a decision procedure on integer values.  Decidability is proved
   structurally; QuickChick (or any sampler) can drive the procedure
   over the sheet and surface counter-examples without having to
   trust an external oracle. *)

From Stdlib Require Import List BinInt Bool Lia.
Import ListNotations.

Open Scope Z_scope.

Inductive SupportedProp : Type :=
  | PEqZ  : Z -> SupportedProp                   (* value = n *)
  | PLtZ  : Z -> SupportedProp                   (* value < n *)
  | PGtZ  : Z -> SupportedProp                   (* value > n *)
  | PLeZ  : Z -> SupportedProp                   (* value <= n *)
  | PGeZ  : Z -> SupportedProp                   (* value >= n *)
  | PInRange : Z -> Z -> SupportedProp           (* lo <= value <= hi *)
  | PAnd  : SupportedProp -> SupportedProp -> SupportedProp
  | POr   : SupportedProp -> SupportedProp -> SupportedProp
  | PNot  : SupportedProp -> SupportedProp.

(* Decision procedure for the supported class. *)
Fixpoint decide (p : SupportedProp) (v : Z) : bool :=
  match p with
  | PEqZ n => Z.eqb v n
  | PLtZ n => Z.ltb v n
  | PGtZ n => Z.gtb v n
  | PLeZ n => Z.leb v n
  | PGeZ n => Z.geb v n
  | PInRange lo hi => Z.leb lo v && Z.leb v hi
  | PAnd a b => decide a v && decide b v
  | POr a b => decide a v || decide b v
  | PNot a => negb (decide a v)
  end.

(* Semantic interpretation as Coq Props. *)
Fixpoint denote (p : SupportedProp) (v : Z) : Prop :=
  match p with
  | PEqZ n => v = n
  | PLtZ n => v < n
  | PGtZ n => v > n
  | PLeZ n => v <= n
  | PGeZ n => v >= n
  | PInRange lo hi => lo <= v <= hi
  | PAnd a b => denote a v /\ denote b v
  | POr a b => denote a v \/ denote b v
  | PNot a => ~ denote a v
  end.

Theorem decide_iff : forall p v,
  decide p v = true <-> denote p v.
Proof.
  induction p; intros v; split; intros Hd; simpl in *.
  - apply Z.eqb_eq. exact Hd.
  - apply Z.eqb_eq. exact Hd.
  - apply Z.ltb_lt. exact Hd.
  - apply Z.ltb_lt. exact Hd.
  - rewrite Z.gtb_ltb in Hd. apply Z.ltb_lt in Hd. lia.
  - rewrite Z.gtb_ltb. apply Z.ltb_lt. lia.
  - apply Z.leb_le. exact Hd.
  - apply Z.leb_le. exact Hd.
  - apply Z.geb_le in Hd. lia.
  - apply Z.geb_le. lia.
  - apply Bool.andb_true_iff in Hd as [Hlo Hhi].
    apply Z.leb_le in Hlo, Hhi. lia.
  - destruct Hd as [Hlo Hhi].
    apply Bool.andb_true_iff. split; apply Z.leb_le; lia.
  - apply Bool.andb_true_iff in Hd as [Ha Hb].
    split; [apply IHp1; exact Ha | apply IHp2; exact Hb].
  - destruct Hd as [Ha Hb].
    apply Bool.andb_true_iff.
    split; [apply IHp1; exact Ha | apply IHp2; exact Hb].
  - apply Bool.orb_true_iff in Hd as [Ha|Hb].
    + left. apply IHp1; exact Ha.
    + right. apply IHp2; exact Hb.
  - apply Bool.orb_true_iff. destruct Hd as [Ha|Hb].
    + left. apply IHp1; exact Ha.
    + right. apply IHp2; exact Hb.
  - apply Bool.negb_true_iff in Hd.
    intro Hcontra. apply IHp in Hcontra. rewrite Hd in Hcontra. discriminate.
  - apply Bool.negb_true_iff.
    destruct (decide p v) eqn:Heq; [|reflexivity].
    exfalso. apply Hd. apply IHp. exact Heq.
Qed.

Theorem decide_sound : forall p v,
  decide p v = true -> denote p v.
Proof. intros. apply decide_iff. assumption. Qed.

Theorem decide_complete : forall p v,
  denote p v -> decide p v = true.
Proof. intros. apply decide_iff. assumption. Qed.

(* Decidability: the supported class is decidable on every value. *)
Theorem supported_prop_decidable :
  forall p v, {denote p v} + {~ denote p v}.
Proof.
  intros p v. destruct (decide p v) eqn:Hd.
  - left. apply decide_sound. exact Hd.
  - right. intro Hcontra. apply decide_complete in Hcontra.
    rewrite Hd in Hcontra. discriminate.
Qed.

(* Counter-example sweep: across a list of values, return the first
   one that violates the predicate, if any. *)
Fixpoint find_counterexample (p : SupportedProp) (vs : list Z) : option Z :=
  match vs with
  | [] => None
  | v :: rest =>
    if decide p v then find_counterexample p rest else Some v
  end.

Theorem find_counterexample_sound : forall p vs v,
  find_counterexample p vs = Some v -> ~ denote p v.
Proof.
  induction vs as [|x rest IH]; intros v Hf; simpl in *; [discriminate|].
  destruct (decide p x) eqn:Hd.
  - apply IH. exact Hf.
  - inversion Hf; subst v.
    intro Hd'. apply decide_complete in Hd'.
    rewrite Hd in Hd'. discriminate.
Qed.

Theorem find_counterexample_none_complete : forall p vs,
  find_counterexample p vs = None ->
  forall v, In v vs -> denote p v.
Proof.
  induction vs as [|x rest IH]; intros Hnone v Hin; simpl in *.
  - contradiction.
  - destruct (decide p x) eqn:Hd; [|discriminate].
    destruct Hin as [Heq|Hin].
    + subst v. apply decide_sound. exact Hd.
    + apply IH; assumption.
Qed.
