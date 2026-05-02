(* Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License. *)
(* Per-cell contracts: each cell ref carries an optional decidable
   predicate over [Z] values.  A guarded commit step refuses writes
   that violate the predicate and leaves the sheet unchanged.  The
   pattern integrates with [RocqsheetMain.commit_to] by wrapping
   integer-literal commits; non-integer cell types fall through to
   the unguarded path. *)

From Stdlib Require Import List Bool BinInt Lia.
From Corelib Require Import PrimInt63.
From Crane Require Import Mapping.NatIntStd Mapping.ZInt.
From Rocqsheet Require Import Rocqsheet.
Import ListNotations.
Import Rocqsheet.

Open Scope int63.

Definition CellContract : Type := CellRef -> option (Z -> bool).

Definition empty_contract : CellContract := fun _ => None.

Definition put_contract
    (c : CellContract) (r : CellRef) (p : Z -> bool) : CellContract :=
  fun r' => if cellref_eqb r r' then Some p else c r'.

(* Guarded commit: write [CLit val] at [r] only when the contract for
   [r] is absent or holds at [val].  Returns [None] on rejection. *)
Definition commit_with_contract
    (c : CellContract) (s : Sheet) (r : CellRef) (val : Z) : option Sheet :=
  match c r with
  | None => Some (set_cell s r (CLit val))
  | Some pred => if pred val then Some (set_cell s r (CLit val)) else None
  end.

(* Lookup of a contract just installed returns it. *)
Theorem put_contract_lookup_same :
  forall c r p, put_contract c r p r = Some p.
Proof.
  intros. unfold put_contract. rewrite cellref_eqb_refl. reflexivity.
Qed.

Lemma cellref_eqb_sym_local : forall r1 r2,
  cellref_eqb r1 r2 = cellref_eqb r2 r1.
Proof.
  intros r1 r2.
  destruct (cellref_eqb r1 r2) eqn:H1, (cellref_eqb r2 r1) eqn:H2.
  - reflexivity.
  - apply cellref_eqb_sound in H1. subst.
    rewrite cellref_eqb_refl in H2. discriminate.
  - apply cellref_eqb_sound in H2. subst.
    rewrite cellref_eqb_refl in H1. discriminate.
  - reflexivity.
Qed.

(* Lookup of an unrelated reference is unchanged. *)
Theorem put_contract_lookup_other :
  forall c r p r',
    cellref_eqb r r' = false ->
    put_contract c r p r' = c r'.
Proof.
  intros c r p r' Hne. unfold put_contract. rewrite Hne. reflexivity.
Qed.

(* When the contract is absent, the commit always succeeds and writes. *)
Theorem commit_no_contract :
  forall c s r val,
    c r = None ->
    commit_with_contract c s r val = Some (set_cell s r (CLit val)).
Proof.
  intros c s r val H. unfold commit_with_contract. rewrite H. reflexivity.
Qed.

(* When the predicate accepts, the commit succeeds and writes. *)
Theorem commit_predicate_accepts :
  forall c s r val pred,
    c r = Some pred ->
    pred val = true ->
    commit_with_contract c s r val = Some (set_cell s r (CLit val)).
Proof.
  intros c s r val pred Hc Hp. unfold commit_with_contract.
  rewrite Hc, Hp. reflexivity.
Qed.

(* When the predicate rejects, the commit fails and yields [None]. *)
Theorem commit_predicate_rejects :
  forall c s r val pred,
    c r = Some pred ->
    pred val = false ->
    commit_with_contract c s r val = None.
Proof.
  intros c s r val pred Hc Hp. unfold commit_with_contract.
  rewrite Hc, Hp. reflexivity.
Qed.

(* Invariant preservation, restricted to in-bounds (valid) references.
   Out-of-bounds references are not exposed to callers, so this is
   the only case [commit_with_contract] is asked about. *)
Definition cell_satisfies_contract (c : CellContract) (s : Sheet) (r : CellRef)
    : Prop :=
  match c r, get_cell s r with
  | None, _ => True
  | Some _, CEmpty | Some _, CFloat _ | Some _, CStr _
  | Some _, CBool _ | Some _, CForm _ => True
  | Some pred, CLit v => pred v = true
  end.

Definition contract_invariant_on (c : CellContract) (s : Sheet) : Prop :=
  forall r, valid_ref r = true -> cell_satisfies_contract c s r.

Theorem commit_preserves_invariant_on :
  forall c s r val s',
    valid_ref r = true ->
    well_formed_sheet s ->
    contract_invariant_on c s ->
    commit_with_contract c s r val = Some s' ->
    contract_invariant_on c s'.
Proof.
  intros c s r val s' Hvalid Hwf Hinv Hcommit r' Hvr'.
  unfold cell_satisfies_contract.
  destruct (cellref_eqb r' r) eqn:Hreq.
  - apply cellref_eqb_sound in Hreq. subst r'.
    destruct (c r) as [pred|] eqn:Hcr.
    + unfold commit_with_contract in Hcommit. rewrite Hcr in Hcommit.
      destruct (pred val) eqn:Hpv; [|discriminate].
      inversion Hcommit; subst s'.
      rewrite get_set_eq_wf; [|exact Hwf|exact Hvr'].
      exact Hpv.
    + destruct (get_cell s' r); trivial.
  - assert (Hri : cell_index r' <> cell_index r).
    { intro Hi.
      apply cell_index_inj in Hi; [|exact Hvr'|exact Hvalid].
      subst r'. rewrite cellref_eqb_refl in Hreq. discriminate. }
    unfold commit_with_contract in Hcommit.
    destruct (c r) as [pred|] eqn:Hcr.
    + destruct (pred val); [|discriminate].
      inversion Hcommit; subst s'.
      pose proof (Hinv r' Hvr') as Hr'.
      unfold cell_satisfies_contract in Hr'.
      destruct (c r') as [pred'|] eqn:Hcr'; [|trivial].
      rewrite get_set_neq; [exact Hr'|exact Hri].
    + inversion Hcommit; subst s'.
      pose proof (Hinv r' Hvr') as Hr'.
      unfold cell_satisfies_contract in Hr'.
      destruct (c r') as [pred'|] eqn:Hcr'; [|trivial].
      rewrite get_set_neq; [exact Hr'|exact Hri].
Qed.
