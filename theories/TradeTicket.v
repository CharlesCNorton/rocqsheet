(* Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License. *)
(* Trade-ticket schema with field-level invariants and round-trip
   between record and association-list encoding.  Self-contained:
   does not depend on Sheet / PrimArray, so [vm_compute] checks stay
   trivial. *)

From Stdlib Require Import List Bool BinInt Lia.
Import ListNotations.

Open Scope Z_scope.

(* Finite currency tag set. *)
Inductive Currency : Type :=
  | USD | EUR | GBP | JPY | CHF.

Definition currency_eqb (c1 c2 : Currency) : bool :=
  match c1, c2 with
  | USD, USD | EUR, EUR | GBP, GBP | JPY, JPY | CHF, CHF => true
  | _, _ => false
  end.

Lemma currency_eqb_sound : forall c1 c2,
  currency_eqb c1 c2 = true <-> c1 = c2.
Proof.
  intros c1 c2. split.
  - destruct c1, c2; simpl; intro H; auto; discriminate.
  - intro Heq. subst. destruct c2; reflexivity.
Qed.

Lemma currency_eqb_refl : forall c, currency_eqb c c = true.
Proof. intro c. apply currency_eqb_sound. reflexivity. Qed.

(* Trade ticket fields are stored as Z; validity is captured separately. *)
Record TradeTicket : Type := mkTicket {
  tt_notional   : Z;
  tt_value_date : Z;
  tt_maturity   : Z;
  tt_currency   : Currency
}.

Definition valid_ticket (t : TradeTicket) : Prop :=
  0 < tt_notional t /\ tt_value_date t < tt_maturity t.

Definition valid_ticket_b (t : TradeTicket) : bool :=
  Z.ltb 0 (tt_notional t) && Z.ltb (tt_value_date t) (tt_maturity t).

Lemma valid_ticket_b_sound : forall t,
  valid_ticket_b t = true <-> valid_ticket t.
Proof.
  intro t. unfold valid_ticket_b, valid_ticket.
  rewrite Bool.andb_true_iff, !Z.ltb_lt. tauto.
Qed.

(* Field tags used as schema keys for the association-list encoding. *)
Inductive Field : Type :=
  | FNotional | FValueDate | FMaturity | FCurrency.

Definition field_eqb (f1 f2 : Field) : bool :=
  match f1, f2 with
  | FNotional, FNotional | FValueDate, FValueDate
  | FMaturity, FMaturity | FCurrency, FCurrency => true
  | _, _ => false
  end.

Lemma field_eqb_refl : forall f, field_eqb f f = true.
Proof. intro f. destruct f; reflexivity. Qed.

(* Encoded entry: a field tag plus a Z payload (currencies are
   encoded as 0..4 indices). *)
Definition Entry : Type := Field * Z.

Definition currency_to_z (c : Currency) : Z :=
  match c with
  | USD => 0 | EUR => 1 | GBP => 2 | JPY => 3 | CHF => 4
  end.

Definition currency_of_z (z : Z) : option Currency :=
  if Z.eqb z 0 then Some USD
  else if Z.eqb z 1 then Some EUR
  else if Z.eqb z 2 then Some GBP
  else if Z.eqb z 3 then Some JPY
  else if Z.eqb z 4 then Some CHF
  else None.

Lemma currency_round_trip : forall c,
  currency_of_z (currency_to_z c) = Some c.
Proof. intro c. destruct c; reflexivity. Qed.

Definition encode (t : TradeTicket) : list Entry :=
  [ (FNotional,   tt_notional t);
    (FValueDate,  tt_value_date t);
    (FMaturity,   tt_maturity t);
    (FCurrency,   currency_to_z (tt_currency t)) ].

Fixpoint lookup (es : list Entry) (f : Field) : option Z :=
  match es with
  | [] => None
  | (f', z) :: rest => if field_eqb f f' then Some z else lookup rest f
  end.

Definition decode (es : list Entry) : option TradeTicket :=
  match lookup es FNotional, lookup es FValueDate,
        lookup es FMaturity, lookup es FCurrency with
  | Some n, Some vd, Some mat, Some cz =>
    match currency_of_z cz with
    | Some c => Some (mkTicket n vd mat c)
    | None => None
    end
  | _, _, _, _ => None
  end.

Theorem encode_decode_round_trip : forall t,
  decode (encode t) = Some t.
Proof.
  intro t. destruct t as [n vd m c].
  unfold encode, decode. simpl.
  rewrite currency_round_trip. reflexivity.
Qed.

(* Schema invariants survive any pure modification that itself
   produces a valid ticket. *)
Theorem encode_decode_preserves_validity : forall t,
  valid_ticket t ->
  match decode (encode t) with
  | Some t' => valid_ticket t'
  | None => False
  end.
Proof.
  intros t Hvalid.
  rewrite encode_decode_round_trip. exact Hvalid.
Qed.

(* A pure update keeps the ticket valid when the new field values
   satisfy the per-field bounds. *)
Definition with_notional (t : TradeTicket) (n : Z) : TradeTicket :=
  mkTicket n (tt_value_date t) (tt_maturity t) (tt_currency t).

Definition with_maturity (t : TradeTicket) (m : Z) : TradeTicket :=
  mkTicket (tt_notional t) (tt_value_date t) m (tt_currency t).

Theorem with_notional_preserves_validity : forall t n,
  valid_ticket t -> 0 < n -> valid_ticket (with_notional t n).
Proof.
  intros t n [_ Hdates] Hpos. unfold with_notional, valid_ticket. simpl.
  split; assumption.
Qed.

Theorem with_maturity_preserves_validity : forall t m,
  valid_ticket t -> tt_value_date t < m ->
  valid_ticket (with_maturity t m).
Proof.
  intros t m [Hpos _] Hdate. unfold with_maturity, valid_ticket. simpl.
  split; assumption.
Qed.

(* Round-trip + validity: book_to_sheet_to_book = id under the
   schema invariant. *)
Theorem book_to_sheet_to_book :
  forall t, valid_ticket t ->
  match decode (encode t) with
  | Some t' => t' = t /\ valid_ticket t'
  | None => False
  end.
Proof.
  intros t Hvalid. rewrite encode_decode_round_trip.
  split; [reflexivity|exact Hvalid].
Qed.
