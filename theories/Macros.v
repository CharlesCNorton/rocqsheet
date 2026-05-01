(* Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License. *)
From Stdlib Require Import List BinInt.
From Corelib Require Import PrimInt63.
From Crane Require Import Mapping.NatIntStd Mapping.ZInt.
From Rocqsheet Require Import Rocqsheet.
Import ListNotations.
Import Rocqsheet.

Open Scope int63.

(* A macro is a finite sequence of cell-set actions.  This is the
   smallest closed sublanguage: each step is exactly an operation
   the user could perform manually (set_cell), so soundness is
   structural and the sandbox boundary is trivial (no other
   actions are expressible). *)

Definition MacroAction : Type := CellRef * Cell.
Definition Macro : Type := list MacroAction.

Fixpoint apply_macro (m : Macro) (s : Sheet) : Sheet :=
  match m with
  | nil => s
  | (r, c) :: rest => apply_macro rest (set_cell s r c)
  end.

(* --- Theorems ---------------------------------------------------- *)

(* Determinism: running the same macro on the same state yields the
   same result.  Trivial since [apply_macro] is a total function. *)
Theorem macro_deterministic :
  forall m s, apply_macro m s = apply_macro m s.
Proof. reflexivity. Qed.

(* Soundness: an empty macro is a no-op. *)
Theorem macro_empty_noop :
  forall s, apply_macro [] s = s.
Proof. reflexivity. Qed.

(* Soundness: a singleton macro is exactly one set_cell. *)
Theorem macro_single_is_set :
  forall r c s,
    apply_macro [(r, c)] s = set_cell s r c.
Proof. reflexivity. Qed.

(* Sandbox: every reachable state via apply_macro can be reached by
   a finite chain of set_cell calls; no other operations.  Captured
   here as: the result equals a fold of set_cell over the list. *)
Theorem macro_factors_through_set_cell :
  forall m s,
    apply_macro m s
    = fold_left (fun acc x => set_cell acc (fst x) (snd x)) m s.
Proof.
  induction m as [|[r c] rest IH]; intros s.
  - reflexivity.
  - simpl. apply IH.
Qed.

(* Smoke: a 2-step macro produces the expected sheet. *)
Theorem macro_smoke :
  let m : Macro := [(mkRef 0 0, CLit 1%Z); (mkRef 1 0, CLit 2%Z)] in
  let s := apply_macro m new_sheet in
  get_cell s (mkRef 0 0) = CLit 1%Z
  /\ get_cell s (mkRef 1 0) = CLit 2%Z.
Proof. vm_compute. split; reflexivity. Qed.
