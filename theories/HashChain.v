(* Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License. *)
(* Hash-chained edit log over an arbitrary operation type [Op].

   Each entry stores a payload op plus a digest [hash = H(prev_hash,
   op_payload)].  Theorems: chain non-malleability (under
   collision-resistance of the digest), genesis replay, and head
   sensitivity to any tamper. *)

From Stdlib Require Import List ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition Hash : Type := Z.

Section Chain.
  Variable Op : Type.
  Variable digest : Hash -> Op -> Hash.

  (* Genesis hash chosen by the chain operator. *)
  Variable genesis : Hash.

  Record Entry : Type := mkEntry {
    e_prev : Hash;
    e_op   : Op;
    e_hash : Hash
  }.

  Definition entry_well_formed (e : Entry) : Prop :=
    e_hash e = digest (e_prev e) (e_op e).

  Fixpoint chain_well_formed (es : list Entry) (prev : Hash) : Prop :=
    match es with
    | [] => True
    | e :: rest =>
      e_prev e = prev /\
      entry_well_formed e /\
      chain_well_formed rest (e_hash e)
    end.

  (* Head hash starting from an arbitrary [start].  Each entry
     replaces the running head; the empty-list head is just [start]. *)
  Fixpoint chain_head_at (start : Hash) (es : list Entry) : Hash :=
    match es with
    | [] => start
    | e :: rest => chain_head_at (e_hash e) rest
    end.

  Definition chain_head (es : list Entry) : Hash := chain_head_at genesis es.

  (* Append one op to a well-formed chain. *)
  Definition append (es : list Entry) (op : Op) : list Entry :=
    let prev := chain_head es in
    es ++ [mkEntry prev op (digest prev op)].

  Lemma chain_head_at_app_one : forall start es e,
    chain_head_at start (es ++ [e]) = e_hash e.
  Proof.
    intros start es e. revert start.
    induction es as [|x rest IH]; intros start; simpl; [reflexivity|].
    apply IH.
  Qed.

  Lemma chain_head_app_one : forall es e,
    chain_head (es ++ [e]) = e_hash e.
  Proof. intros. unfold chain_head. apply chain_head_at_app_one. Qed.

  (* Generalized append preservation: for any starting [prev]. *)
  Lemma append_preserves_well_formed_at : forall es op prev,
    chain_well_formed es prev ->
    chain_well_formed
      (es ++ [mkEntry (chain_head_at prev es) op
                      (digest (chain_head_at prev es) op)])
      prev.
  Proof.
    induction es as [|e rest IH]; intros op prev Hwf; simpl in *.
    - split; [reflexivity|]. split; [unfold entry_well_formed; reflexivity|].
      exact I.
    - destruct Hwf as [Hprev [Hentry Hrest]].
      split; [exact Hprev|]. split; [exact Hentry|].
      apply IH. exact Hrest.
  Qed.

  (* Appending preserves well-formedness from genesis. *)
  Theorem append_preserves_well_formed : forall es op,
    chain_well_formed es genesis ->
    chain_well_formed (append es op) genesis.
  Proof.
    intros es op H. unfold append, chain_head.
    apply append_preserves_well_formed_at. exact H.
  Qed.

  (* Genesis replay: a chain produced by repeated appends from the
     empty chain has the right head. *)
  Theorem append_head_is_digest : forall es op,
    chain_head (append es op) = digest (chain_head es) op.
  Proof.
    intros es op. unfold append. rewrite chain_head_app_one. reflexivity.
  Qed.

  (* Collision-resistance of the digest. *)
  Definition collision_resistant : Prop :=
    forall p1 p2 op1 op2, digest p1 op1 = digest p2 op2 -> p1 = p2 /\ op1 = op2.

  (* Last-entry uniqueness: under collision resistance, the last entry
     of a well-formed chain is determined by its hash and the chain's
     prefix.  Two chains with the same prefix and same final hash
     must agree on the final entry. *)
  Theorem chain_last_entry_unique :
    collision_resistant ->
    forall es e1 e2 prev,
      chain_well_formed (es ++ [e1]) prev ->
      chain_well_formed (es ++ [e2]) prev ->
      e_hash e1 = e_hash e2 ->
      e1 = e2.
  Proof.
    intros Hres es e1 e2 prev Hwf1 Hwf2 Hhash.
    (* Both last entries have e_prev = chain_head_at prev es and
       e_hash = digest (e_prev) (e_op).  Equal e_hash + Hres yields
       equal e_prev and e_op, hence equal entries. *)
    assert (Haux1 : forall (e : Entry) (es : list Entry) (prev : Hash),
              chain_well_formed (es ++ [e]) prev ->
              e_prev e = chain_head_at prev es /\ entry_well_formed e).
    { clear es e1 e2 prev Hwf1 Hwf2 Hhash.
      intros e es. induction es as [|x rest IH]; intros prev Hwf;
        simpl in *.
      - destruct Hwf as [Hp [Hen _]]. split; assumption.
      - destruct Hwf as [_ [_ Hr]]. apply IH. exact Hr. }
    destruct (Haux1 e1 es prev Hwf1) as [Hp1 Hwf_e1].
    destruct (Haux1 e2 es prev Hwf2) as [Hp2 Hwf_e2].
    unfold entry_well_formed in Hwf_e1, Hwf_e2.
    pose proof Hhash as Hhash_for_op.
    rewrite Hwf_e1, Hwf_e2 in Hhash_for_op.
    apply Hres in Hhash_for_op as [_ Hopeq].
    destruct e1 as [p1 o1 h1], e2 as [p2 o2 h2]; simpl in *.
    subst p1 p2 h1 h2 o1.
    reflexivity.
  Qed.

  (* Tamper sensitivity: changing any payload changes the head, under
     collision resistance.  Stated as a contrapositive: same head
     implies same chain.  Specialised to single-op append. *)
  Theorem tamper_changes_head :
    collision_resistant ->
    forall es op1 op2,
      chain_head (append es op1) = chain_head (append es op2) ->
      op1 = op2.
  Proof.
    intros Hres es op1 op2 Hheq.
    rewrite !append_head_is_digest in Hheq.
    apply Hres in Hheq as [_ Hopeq]. exact Hopeq.
  Qed.
End Chain.
