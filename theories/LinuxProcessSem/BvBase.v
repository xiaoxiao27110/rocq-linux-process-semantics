(** * LinuxProcessSem.BvBase — shared bitvector helpers for the spec layer

    TRUST BOUNDARY: this file is part of the trusted specification.

    Bitvector representation follows two rules:

    - machine QUANTITIES (register values, addresses, syscall args and
      returns, fds, channel ids, sizes, offsets, exit codes) are
      [word = bv 64]; memory/file/event BYTES are [byte = bv 8];
    - RANGE and DISJOINTNESS arithmetic is done in [Z] over
      [bv_unsigned] (no wrap-around), so bound checks keep a precise
      meaning.  Only data that lands back in registers or memory is
      re-wrapped with [Z_to_bv].

    [word], [reg], [bv_eqb], [bv_ltu], [bv_lts] come from the ISA
    prelude (LinuxProcessSemantics.Riscv.Prelude). *)

From LinuxProcessSemantics.Riscv Require Export Prelude.
From Stdlib Require Import List Lia.
Import ListNotations.
Open Scope bv_scope.

Notation byte := (bv 8) (only parsing).

(** Unsigned [<=] as a boolean (unsigned [<] is [bv_ltu]). *)
Definition bv_leu {n} (a b : bv n) : bool :=
  Z.leb (bv_unsigned a) (bv_unsigned b).

(** List length as a 64-bit word (all modeled lengths are far below
    2^64, so this never wraps). *)
Definition len_word {A} (l : list A) : word :=
  Z_to_bv 64 (Z.of_nat (length l)).

(** Word/nat bridges for list indexing and fuel. *)
Definition word_to_nat (w : word) : nat := Z.to_nat (bv_unsigned w).
Definition nat_to_word (n : nat) : word := Z_to_bv 64 (Z.of_nat n).

(** Convert a word to a [nat], but never construct a unary numeral larger
    than [bound].  The comparison stays in [Z], and OCaml evaluates only
    the selected branch, so a huge word takes the constant-size [bound]
    branch without first materializing [word_to_nat w].  Extensionally
    this is just [Nat.min]; the spelling is load-bearing for extraction. *)
Definition word_to_nat_bounded (w : word) (bound : nat) : nat :=
  if (bv_unsigned w <=? Z.of_nat bound)%Z
  then word_to_nat w
  else bound.

Lemma word_to_nat_bounded_eq_min : forall w bound,
  word_to_nat_bounded w bound = Nat.min (word_to_nat w) bound.
Proof.
  intros w bound. pose proof (bv_unsigned_in_range 64 w) as Hw.
  unfold word_to_nat_bounded.
  destruct (bv_unsigned w <=? Z.of_nat bound)%Z eqn:Hle.
  - apply Z.leb_le in Hle. rewrite Nat.min_l; [reflexivity|].
    unfold word_to_nat. rewrite <- (Nat2Z.id bound).
    apply Z2Nat.inj_le; lia.
  - apply Z.leb_gt in Hle. rewrite Nat.min_r; [reflexivity|].
    unfold word_to_nat. rewrite <- (Nat2Z.id bound).
    apply Z2Nat.inj_le; lia.
Qed.

(** ** Little-endian byte (de)composition *)

(** The 8 little-endian bytes of a 64-bit word (index 0 = least
    significant). *)
Definition word_le8 (v : word) : list byte :=
  [ bv_extract 0 8 v; bv_extract 8 8 v; bv_extract 16 8 v;
    bv_extract 24 8 v; bv_extract 32 8 v; bv_extract 40 8 v;
    bv_extract 48 8 v; bv_extract 56 8 v ].

(** Little-endian assembly ([bv_concat] puts its FIRST argument in the
    high bits). *)
Definition le2 (b1 b0 : byte) : bv 16 := bv_concat 16 b1 b0.
Definition le4 (b3 b2 b1 b0 : byte) : bv 32 :=
  bv_concat 32 (le2 b3 b2) (le2 b1 b0).
Definition le8 (b7 b6 b5 b4 b3 b2 b1 b0 : byte) : word :=
  bv_concat 64 (le4 b7 b6 b5 b4) (le4 b3 b2 b1 b0).

(** The value of a little-endian byte list (index 0 = least
    significant), as an EXACT non-negative [Z]: it walks the whole list
    and truncates nothing, so a list longer than 8 bytes yields a number
    above 2^64.  The 64-bit truncation belongs to [le_bytes_to_word]
    below, not here — a distinction [Uapi.timespec_ns] relies on, since
    it bounds a decoded [tv_sec] by arithmetic on this exact value. *)
Fixpoint bytes_le_to_Z (bs : list byte) : Z :=
  match bs with
  | [] => 0%Z
  | b :: rest => Z.lor (bv_unsigned b) (Z.shiftl (bytes_le_to_Z rest) 8)
  end.

(** The same value truncated to 64 bits; callers never pass more than
    8 bytes, where the truncation does nothing. *)
Definition le_bytes_to_word (bs : list byte) : word :=
  Z_to_bv 64 (bytes_le_to_Z bs).

(** The [n] little-endian bytes of [z] (index 0 = least significant) —
    [bytes_le_to_Z]'s inverse, truncating [z] to [8n] bits.  Both the
    machine semantics (for stores) and the syscall specs (for encoding a
    C struct into user memory) need it, so it sits with its inverse
    rather than in either of them. *)
Fixpoint Z_to_le_bytes (n : nat) (z : Z) : list byte :=
  match n with
  | O => []
  | S n' => Z_to_bv 8 z :: Z_to_le_bytes n' (Z.shiftr z 8)
  end.

Lemma length_Z_to_le_bytes : forall n z, length (Z_to_le_bytes n z) = n.
Proof.
  induction n as [|n IH]; intro z; [reflexivity|].
  cbn [Z_to_le_bytes length]. now rewrite IH.
Qed.

Lemma bv_wrap8_mod : forall z : Z, bv_wrap 8 z = (z mod 2 ^ 8)%Z.
Proof. reflexivity. Qed.

(** [Z_to_le_bytes] keeps exactly the low [8k] bits. *)
Lemma bytes_le_to_Z_of_le_bytes : forall k z, (0 <= z)%Z ->
  bytes_le_to_Z (Z_to_le_bytes k z) = (z mod 2 ^ (8 * Z.of_nat k))%Z.
Proof.
  induction k as [|k IH]; intros z Hz.
  - cbn. change (2 ^ (8 * Z.of_nat 0))%Z with 1%Z. rewrite Z.mod_1_r. reflexivity.
  - cbn [Z_to_le_bytes bytes_le_to_Z].
    rewrite IH by (apply Z.shiftr_nonneg; lia).
    rewrite Z_to_bv_unsigned, bv_wrap8_mod.
    replace (8 * Z.of_nat (S k))%Z with (8 * Z.of_nat k + 8)%Z by lia.
    pose proof (Nat2Z.is_nonneg k).
    apply Z.bits_inj'. intros i Hi.
    rewrite Z.lor_spec, Z.shiftl_spec by lia.
    destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
    + rewrite (Z.mod_pow2_bits_low z 8 i) by lia.
      rewrite (Z.mod_pow2_bits_low z (8 * Z.of_nat k + 8) i) by lia.
      rewrite (Z.testbit_neg_r _ (i - 8)) by lia.
      apply orb_false_r.
    + rewrite (Z.mod_pow2_bits_high z 8 i) by lia.
      rewrite orb_false_l.
      destruct (Z.lt_ge_cases i (8 * Z.of_nat k + 8)) as [Hik|Hik].
      * rewrite (Z.mod_pow2_bits_low _ (8 * Z.of_nat k) (i - 8)) by lia.
        rewrite Z.shiftr_spec by lia.
        rewrite (Z.mod_pow2_bits_low z (8 * Z.of_nat k + 8) i) by lia.
        f_equal. lia.
      * rewrite (Z.mod_pow2_bits_high _ (8 * Z.of_nat k) (i - 8)) by lia.
        rewrite (Z.mod_pow2_bits_high z (8 * Z.of_nat k + 8) i) by lia.
        reflexivity.
Qed.

(** The 4 little-endian bytes of a word's low half — an [int] as the
    kernel's [put_user] stores it. *)
Definition word_le4 (v : word) : list byte :=
  [ bv_extract 0 8 v; bv_extract 8 8 v; bv_extract 16 8 v;
    bv_extract 24 8 v ].

(** The 2 little-endian bytes of a word's low quarter — a [short] as
    the kernel's [put_user] stores it.  [ppoll]'s [revents] is the one
    field any modeled syscall writes at this width. *)
Definition word_le2 (v : word) : list byte :=
  [ bv_extract 0 8 v; bv_extract 8 8 v ].
