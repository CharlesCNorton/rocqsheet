(* Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License. *)
From Stdlib Require Import List Bool BinInt Lia.
From Corelib Require Import PrimInt63.
From Crane Require Import Mapping.NatIntStd Mapping.ZInt.
From Rocqsheet Require Import Rocqsheet.
Import ListNotations.
Import Rocqsheet.

Open Scope int63.

(* Local accessors computed via [cell_index] so the extracted C++
   does not emit a base-class-qualified projection (which Crane
   produces for direct [ref_col r] / [ref_row r] outside the
   [Rocqsheet] module). *)
Definition col_of (r : CellRef) : int :=
  PrimInt63.mod (cell_index r) NUM_COLS.

Definition row_of (r : CellRef) : int :=
  PrimInt63.div (cell_index r) NUM_COLS.

(* A merged region is a (top-left, bottom-right) pair. *)
Definition MergeRegion : Type := CellRef * CellRef.

Definition MergeList : Type := list MergeRegion.

(* True if [r] is inside the rectangle [tl, br]. *)
Definition in_region (r : CellRef) (m : MergeRegion) : bool :=
  let '(tl, br) := m in
  andb (PrimInt63.leb (col_of tl) (col_of r))
       (andb (PrimInt63.leb (col_of r) (col_of br))
             (andb (PrimInt63.leb (row_of tl) (row_of r))
                   (PrimInt63.leb (row_of r) (row_of br)))).

(* Find the first region containing [r]; return its top-left.  When
   no region contains [r], return [r] unchanged. *)
Fixpoint resolve (ms : MergeList) (r : CellRef) : CellRef :=
  match ms with
  | nil => r
  | m :: rest =>
    if in_region r m then fst m else resolve rest r
  end.

(* Read through merges: a cell in a merged region resolves to the
   top-left's underlying value. *)
Definition merged_get (s : Sheet) (ms : MergeList) (r : CellRef) : Cell :=
  get_cell s (resolve ms r).

(* Write through merges: writes always land at the top-left of the
   first region containing the target, leaving other cells in the
   region untouched. *)
Definition merged_set (s : Sheet) (ms : MergeList) (r : CellRef) (c : Cell)
    : Sheet :=
  set_cell s (resolve ms r) c.

(* Add a merge region.  No deduplication. *)
Definition add_merge (ms : MergeList) (tl br : CellRef) : MergeList :=
  (tl, br) :: ms.

(* Remove the first region whose top-left equals [tl]. *)
Fixpoint remove_merge (ms : MergeList) (tl : CellRef) : MergeList :=
  match ms with
  | nil => nil
  | m :: rest =>
    if cellref_eqb (fst m) tl then rest
    else m :: remove_merge rest tl
  end.

(* --- Theorems ---------------------------------------------------- *)

(* eval_merged_region_at_top_left: for any cell in a merged region,
   merged_get returns the cell value at the region's top-left. *)
Theorem merged_get_in_region :
  forall s tl br r ms,
    in_region r (tl, br) = true ->
    merged_get s ((tl, br) :: ms) r = get_cell s tl.
Proof.
  intros s tl br r ms Hin.
  unfold merged_get. cbn [resolve fst].
  rewrite Hin. reflexivity.
Qed.

(* At the top-left itself, merged_get coincides with plain get_cell. *)
Theorem merged_get_at_top_left :
  forall s tl br ms,
    in_region tl (tl, br) = true ->
    merged_get s ((tl, br) :: ms) tl = get_cell s tl.
Proof.
  intros s tl br ms Hin.
  apply (merged_get_in_region s tl br tl ms Hin).
Qed.

(* unmerge ∘ merge = id when the new merge's top-left is not already
   present.  remove_merge picks the first matching entry and the
   add_merge above puts the fresh one at the head, so the operation
   pair cancels. *)
Theorem unmerge_after_merge_is_id :
  forall ms tl br,
    remove_merge (add_merge ms tl br) tl = ms.
Proof.
  intros ms tl br. unfold add_merge, remove_merge.
  simpl. rewrite cellref_eqb_refl. reflexivity.
Qed.

(* Setting a cell that lies in a merged region only writes to the
   region's top-left; any other cell is unchanged. *)
Theorem merged_set_only_writes_top_left :
  forall s tl br r r' ms c,
    in_region r (tl, br) = true ->
    cell_index r' <> cell_index tl ->
    get_cell (merged_set s ((tl, br) :: ms) r c) r' = get_cell s r'.
Proof.
  intros s tl br r r' ms c Hin Hneq.
  unfold merged_set. cbn [resolve fst].
  rewrite Hin.
  apply get_set_neq. exact Hneq.
Qed.

(* Smoke: a 2x2 merged region; reading any of the 4 cells through
   merged_get returns the value stored at the top-left. *)
Theorem merged_get_smoke :
  let tl := mkRef 1 1 in
  let br := mkRef 2 2 in
  let s := set_cell new_sheet tl (CLit 7%Z) in
  let ms : MergeList := [(tl, br)] in
  merged_get s ms (mkRef 2 2) = CLit 7%Z.
Proof. vm_compute. reflexivity. Qed.
