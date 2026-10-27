(** * Prelude: bitvector helpers and a tiny radix-tree map.

    The map is hand-rolled (rather than stdpp's [gmap]) so that OCaml
    extraction stays small and dictionary-free. *)

From stdpp.bitvector Require Export bitvector.
From Stdlib Require Export ZArith.

Open Scope bv_scope.

Notation word := (bv 64) (only parsing).
Notation reg := (bv 5) (only parsing).

(** Extract bits [hi..lo] (inclusive) of [w] as a bitvector of the
    appropriate width.  Callers pass the result width explicitly so the
    types stay syntactic. *)
Definition bits {n} (lo len : N) (w : bv n) : bv len := bv_extract lo len w.

Definition sext {n} (m : N) (b : bv n) : bv m := bv_sign_extend m b.
Definition zext {n} (m : N) (b : bv n) : bv m := bv_zero_extend m b.

(** Untyped bit test, for decoding. *)
Definition bit {n} (i : N) (w : bv n) : bool :=
  Z.testbit (bv_unsigned w) (Z.of_N i).

(** * Signedness-explicit wrappers

    Most [bv] operations (add, sub, mul, and, ...) mean the same thing
    under a signed or unsigned reading, but comparisons and the high
    half of a full-width product do not.  Those are isolated here so
    that every use site names the interpretation it wants, rather than
    picking [bv_signed]/[bv_unsigned] inline.  Naming follows the
    stdpp-bitvector [bv_] convention, with coqutil's suffixes for the
    signedness variants (lts/ltu, mulhss/mulhsu/mulhuu). *)

Definition bv_lts {n} (a b : bv n) : bool := Z.ltb (bv_signed a) (bv_signed b).
Definition bv_ltu {n} (a b : bv n) : bool := Z.ltb (bv_unsigned a) (bv_unsigned b).

(** Equality is signedness-independent; included for uniformity. *)
Definition bv_eqb {n} (a b : bv n) : bool := Z.eqb (bv_unsigned a) (bv_unsigned b).

(** High [n] bits of the exact 2n-bit product: the operands are read as
    signed/signed, signed/unsigned, unsigned/unsigned respectively, and
    the exact integer product is arithmetically shifted right by [n]. *)
Definition bv_mulhss {n} (a b : bv n) : bv n :=
  Z_to_bv n (Z.shiftr (bv_signed a * bv_signed b) (Z.of_N n)).
Definition bv_mulhsu {n} (a b : bv n) : bv n :=
  Z_to_bv n (Z.shiftr (bv_signed a * bv_unsigned b) (Z.of_N n)).
Definition bv_mulhuu {n} (a b : bv n) : bv n :=
  Z_to_bv n (Z.shiftr (bv_unsigned a * bv_unsigned b) (Z.of_N n)).

(** * Radix-tree map keyed by [positive] *)

Inductive tree (A : Type) : Type :=
| TEmpty
| TNode (l : tree A) (v : option A) (r : tree A).
Arguments TEmpty {A}.
Arguments TNode {A} l v r.

Fixpoint tget {A} (p : positive) (t : tree A) : option A :=
  match t with
  | TEmpty => None
  | TNode l v r =>
      match p with
      | xH => v
      | xO p => tget p l
      | xI p => tget p r
      end
  end.

Fixpoint tset {A} (p : positive) (x : A) (t : tree A) : tree A :=
  match t with
  | TEmpty =>
      match p with
      | xH => TNode TEmpty (Some x) TEmpty
      | xO p => TNode (tset p x TEmpty) None TEmpty
      | xI p => TNode TEmpty None (tset p x TEmpty)
      end
  | TNode l v r =>
      match p with
      | xH => TNode l (Some x) r
      | xO p => TNode (tset p x l) v r
      | xI p => TNode l v (tset p x r)
      end
  end.

Lemma tget_tset_same {A} (p : positive) (x : A) t :
  tget p (tset p x t) = Some x.
Proof.
  revert t; induction p; intros [|l v r]; simpl; auto.
Qed.

Lemma tget_tset_other {A} (p q : positive) (x : A) t :
  p ≠ q → tget q (tset p x t) = tget q t.
Proof.
  revert q t; induction p; intros [q'|q'|] [|l v r] Hne; simpl; auto;
    try congruence;
    try (rewrite IHp; [destruct q'; auto|congruence]);
    try (apply IHp; congruence);
    destruct q'; auto.
Qed.

(** Map bitvector keys (register indices, addresses) into [positive]. *)
Definition bv_key {n} (b : bv n) : positive := Z.to_pos (bv_unsigned b + 1).

Lemma bv_key_inj {n} (b1 b2 : bv n) : bv_key b1 = bv_key b2 → b1 = b2.
Proof.
  unfold bv_key. intros H. apply bv_eq.
  pose proof (bv_unsigned_in_range _ b1) as [? _].
  pose proof (bv_unsigned_in_range _ b2) as [? _].
  lia.
Qed.

Definition bvmap (n : N) (A : Type) := tree A.
Definition bvmap_get {n A} (k : bv n) (m : bvmap n A) : option A :=
  tget (bv_key k) m.
Definition bvmap_set {n A} (k : bv n) (x : A) (m : bvmap n A) : bvmap n A :=
  tset (bv_key k) x m.
Definition bvmap_empty {n A} : bvmap n A := TEmpty.

Lemma bvmap_get_set_same {n A} (k : bv n) (x : A) m :
  bvmap_get k (bvmap_set k x m) = Some x.
Proof. apply tget_tset_same. Qed.

Lemma bvmap_get_set_other {n A} (k k' : bv n) (x : A) m :
  k ≠ k' → bvmap_get k' (bvmap_set k x m) = bvmap_get k' m.
Proof.
  intros Hne. apply tget_tset_other. intros Hk. apply Hne, bv_key_inj, Hk.
Qed.
