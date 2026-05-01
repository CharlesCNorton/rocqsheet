(* Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License. *)
From Stdlib Require Import List BinInt.
From Corelib Require Import PrimInt63.
From Crane Require Import Mapping.NatIntStd Mapping.ZInt.
From Rocqsheet Require Import Rocqsheet.
Import ListNotations.
Import Rocqsheet.

Open Scope int63.

(* A simple persistent representation: a list of (col, row, value)
   triples for cells holding integer literals.  Empty cells are not
   serialised; this is the minimum subset needed for the round-trip
   theorems below.  Float, string, bool and formula cells require
   their own per-type serialisers and are beyond this scope. *)

Definition CellEntry : Type := int * int * Z.

Definition Persisted : Type := list CellEntry.

(* Serialise: walk all cells, emit an entry for each [CLit n]. *)

Fixpoint persist_aux (s : Sheet) (idx fuel : nat) (acc : Persisted) : Persisted :=
  match fuel with
  | O => acc
  | S fuel' =>
    let r := mkRef (PrimInt63.mod (Uint63.of_Z (Z.of_nat idx)) NUM_COLS)
                   (PrimInt63.div (Uint63.of_Z (Z.of_nat idx)) NUM_COLS) in
    let acc' :=
      match get_cell s r with
      | CLit n => (ref_col r, ref_row r, n) :: acc
      | _ => acc
      end in
    persist_aux s (S idx) fuel' acc'
  end.

Definition persist (s : Sheet) : Persisted := persist_aux s 0 60000 [].

(* Deserialise: fold each entry back into a fresh sheet. *)

Fixpoint restore (entries : Persisted) (s : Sheet) : Sheet :=
  match entries with
  | nil => s
  | (col, row, n) :: rest =>
    restore rest (set_cell s (mkRef col row) (CLit n))
  end.

(* Round-trip smoke: a sheet with two CLit entries serialises and
   deserialises to a sheet that returns the same values at those
   cells. *)

Theorem persist_restore_smoke :
  let s := set_cell new_sheet (mkRef 0 0) (CLit 7%Z) in
  let s' := set_cell s (mkRef 1 0) (CLit 13%Z) in
  let s'' := restore (persist s') new_sheet in
  get_cell s'' (mkRef 0 0) = CLit 7%Z
  /\ get_cell s'' (mkRef 1 0) = CLit 13%Z.
Proof. vm_compute. split; reflexivity. Qed.

(* Idempotence on no-change: persisting then restoring an empty
   sheet yields an empty sheet at the cell. *)
Theorem persist_restore_empty_smoke :
  let s'' := restore (persist new_sheet) new_sheet in
  get_cell s'' (mkRef 5%uint63 7%uint63) = CEmpty.
Proof. vm_compute. reflexivity. Qed.

(* save_then_load_then_eval: evaluating a CLit cell after a
   save+load round-trip yields the same value as evaluating the
   original. *)
Theorem persist_restore_then_eval_smoke :
  let s := set_cell new_sheet (mkRef 0 0) (CLit 42%Z) in
  let s' := restore (persist s) new_sheet in
  eval_cell DEFAULT_FUEL s (mkRef 0 0)
  = eval_cell DEFAULT_FUEL s' (mkRef 0 0).
Proof. vm_compute. reflexivity. Qed.

(* --- Extended persistence covering bool and float cells ------- *)

Inductive PCell : Type :=
  | PEmpty
  | PInt   : Z -> PCell
  | PFloat : PrimFloat.float -> PCell
  | PBool  : bool -> PCell.

Definition cell_to_pcell (c : Cell) : option PCell :=
  match c with
  | CEmpty   => Some PEmpty
  | CLit n   => Some (PInt n)
  | CFloat f => Some (PFloat f)
  | CBool b  => Some (PBool b)
  | CStr _   => None
  | CForm _  => None
  end.

Definition pcell_to_cell (p : PCell) : Cell :=
  match p with
  | PEmpty   => CEmpty
  | PInt n   => CLit n
  | PFloat f => CFloat f
  | PBool b  => CBool b
  end.

Theorem pcell_round_trip_lit : forall n,
  match cell_to_pcell (CLit n) with
  | Some p => pcell_to_cell p = CLit n
  | None => False
  end.
Proof. reflexivity. Qed.

Theorem pcell_round_trip_float : forall f,
  match cell_to_pcell (CFloat f) with
  | Some p => pcell_to_cell p = CFloat f
  | None => False
  end.
Proof. reflexivity. Qed.

Theorem pcell_round_trip_bool : forall b,
  match cell_to_pcell (CBool b) with
  | Some p => pcell_to_cell p = CBool b
  | None => False
  end.
Proof. reflexivity. Qed.

Theorem pcell_round_trip_empty :
  match cell_to_pcell CEmpty with
  | Some p => pcell_to_cell p = CEmpty
  | None => False
  end.
Proof. reflexivity. Qed.
