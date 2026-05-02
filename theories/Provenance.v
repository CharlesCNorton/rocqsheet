(* Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License. *)
(* Per-cell provenance hashes.

   [value_hash f ih] combines a formula's own hash [f] with the
   ordered hashes of its inputs [ih] into a single digest.  Identical
   workbooks under identical inputs produce identical digests
   (functional determinism).  Collision resistance reduces to the
   underlying digest on the (formula, inputs) tuple. *)

From Stdlib Require Import List ZArith Lia.
Import ListNotations.

Open Scope Z_scope.

(* A digest is a Z; the actual hash function is an abstract parameter
   that callers can instantiate with SHA-256, BLAKE3, etc. *)
Definition Digest : Type := Z.

Section Hash.
  Variable digest : list Z -> Digest.

  (* value_hash combines the formula digest [f] with the input
     digests [ih] by feeding the concatenated list to [digest]. *)
  Definition value_hash (f : Digest) (ih : list Digest) : Digest :=
    digest (f :: ih).

  Theorem value_hash_deterministic :
    forall f1 f2 ih1 ih2,
      f1 = f2 -> ih1 = ih2 -> value_hash f1 ih1 = value_hash f2 ih2.
  Proof. intros; subst; reflexivity. Qed.

  (* Identical workbooks under identical inputs produce identical
     hashes.  Stated over per-cell input lists [w]. *)
  Theorem identical_inputs_identical_hash :
    forall w1 w2 : list (Digest * list Digest),
      w1 = w2 ->
      map (fun fw => value_hash (fst fw) (snd fw)) w1
      = map (fun fw => value_hash (fst fw) (snd fw)) w2.
  Proof. intros; subst; reflexivity. Qed.

  (* Collision-resistance reduction: any collision on [value_hash]
     with the same formula digest [f] reduces to a collision on the
     underlying [digest] over its (f :: inputs) tuple. *)
  Theorem value_hash_collision_reduces :
    forall f ih1 ih2,
      value_hash f ih1 = value_hash f ih2 ->
      digest (f :: ih1) = digest (f :: ih2).
  Proof. intros; assumption. Qed.

  (* Stronger reduction: any collision on [value_hash] reduces to a
     collision on [digest] over the (f :: ih) packing.  The
     contrapositive is what callers will use: if [digest] is
     collision-resistant on (f :: ih) packings, so is [value_hash]
     on the projected (f, ih) pair. *)
  Theorem value_hash_collision_packed_reduces :
    forall f1 f2 ih1 ih2,
      value_hash f1 ih1 = value_hash f2 ih2 ->
      digest (f1 :: ih1) = digest (f2 :: ih2).
  Proof. intros; assumption. Qed.

  (* Collision resistance for [digest] (parametric assumption). *)
  Definition collision_resistant : Prop :=
    forall xs ys, digest xs = digest ys -> xs = ys.

  (* Under collision resistance of [digest], a [value_hash] collision
     forces (f1, ih1) = (f2, ih2). *)
  Theorem value_hash_injective_under_resistance :
    collision_resistant ->
    forall f1 f2 ih1 ih2,
      value_hash f1 ih1 = value_hash f2 ih2 ->
      f1 = f2 /\ ih1 = ih2.
  Proof.
    intros Hres f1 f2 ih1 ih2 Heq.
    apply Hres in Heq. inversion Heq. split; reflexivity.
  Qed.
End Hash.

(* A concrete (non-cryptographic) digest used to keep the module
   self-contained for testing.  Production callers should instantiate
   the [Hash] section with a real hash. *)
Definition fnv_offset : Z := 14695981039346656037%Z.
Definition fnv_prime  : Z := 1099511628211%Z.

Definition fnv_step (acc x : Z) : Z :=
  Z.modulo ((acc + x) * fnv_prime) (Z.pow 2 64).

Definition fnv (xs : list Z) : Digest :=
  fold_left fnv_step xs fnv_offset.

(* Smoke: identical input lists hash identically with the FNV
   instantiation.  vm_compute on small inputs is fine. *)
Theorem fnv_deterministic_smoke :
  fnv [1; 2; 3] = fnv [1; 2; 3].
Proof. reflexivity. Qed.

Theorem value_hash_fnv_deterministic_smoke :
  value_hash fnv 7 [11; 13; 17] = value_hash fnv 7 [11; 13; 17].
Proof. reflexivity. Qed.
