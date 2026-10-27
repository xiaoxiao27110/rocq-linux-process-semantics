From Coq.Unicode Require Export Utf8.
From Coq.ZArith Require Export ZArith.
From Coq.NArith Require Export NArith.
From Coq.Bool Require Export Bool.
From Coq.Lists Require Import List.
From Coq.Logic Require Import Eqdep_dec.
From Coq.micromega Require Export Lia.

Global Open Scope Z_scope.

Definition bv_modulus (n : N) : Z := 2 ^ Z.of_N n.
Definition bv_half_modulus (n : N) : Z := 2 ^ (Z.of_N n - 1).

Lemma bv_modulus_pos (n : N) : 0 < bv_modulus n.
Proof.
  unfold bv_modulus. apply Z.pow_pos_nonneg; [lia | apply N2Z.is_nonneg].
Qed.

Definition bv_wrap (n : N) (z : Z) : Z := z mod bv_modulus n.

Definition bv_swrap (n : N) (z : Z) : Z :=
  bv_wrap n (z + bv_half_modulus n) - bv_half_modulus n.

Lemma bv_wrap_in_range (n : N) (z : Z) : 0 <= bv_wrap n z < bv_modulus n.
Proof.
  unfold bv_wrap. apply Z.mod_pos_bound. apply bv_modulus_pos.
Qed.

Lemma bv_wrap_small (n : N) (z : Z) :
  0 <= z < bv_modulus n -> bv_wrap n z = z.
Proof.
  intros H. unfold bv_wrap. apply Z.mod_small. exact H.
Qed.

Lemma bv_wrap_0 (n : N) : bv_wrap n 0 = 0.
Proof.
  unfold bv_wrap. apply Z.mod_0_l.
  pose proof (bv_modulus_pos n). lia.
Qed.

Lemma bv_wrap_idemp (n : N) (z : Z) : bv_wrap n (bv_wrap n z) = bv_wrap n z.
Proof.
  apply bv_wrap_small. apply bv_wrap_in_range.
Qed.

Lemma bv_wrap_add_idemp_l (n : N) (x y : Z) :
  bv_wrap n (bv_wrap n x + y) = bv_wrap n (x + y).
Proof.
  unfold bv_wrap. apply Zplus_mod_idemp_l.
Qed.

Lemma bv_wrap_add_idemp_r (n : N) (x y : Z) :
  bv_wrap n (x + bv_wrap n y) = bv_wrap n (x + y).
Proof.
  unfold bv_wrap. apply Zplus_mod_idemp_r.
Qed.

Lemma bv_wrap_sub_idemp_l (n : N) (x y : Z) :
  bv_wrap n (bv_wrap n x - y) = bv_wrap n (x - y).
Proof.
  unfold bv_wrap. apply Zminus_mod_idemp_l.
Qed.

Lemma bv_wrap_sub_idemp_r (n : N) (x y : Z) :
  bv_wrap n (x - bv_wrap n y) = bv_wrap n (x - y).
Proof.
  unfold bv_wrap. apply Zminus_mod_idemp_r.
Qed.

Lemma bv_wrap_mul_idemp_l (n : N) (x y : Z) :
  bv_wrap n (bv_wrap n x * y) = bv_wrap n (x * y).
Proof.
  unfold bv_wrap. apply Zmult_mod_idemp_l.
Qed.

Lemma bv_wrap_mul_idemp_r (n : N) (x y : Z) :
  bv_wrap n (x * bv_wrap n y) = bv_wrap n (x * y).
Proof.
  unfold bv_wrap. apply Zmult_mod_idemp_r.
Qed.

Lemma bv_swrap_wrap (n : N) (z : Z) :
  bv_swrap n (bv_wrap n z) = bv_swrap n z.
Proof.
  unfold bv_swrap. rewrite bv_wrap_add_idemp_l. reflexivity.
Qed.

Lemma bv_wrap_factor (n m : N) (z : Z) :
  (n <= m)%N -> bv_wrap n (bv_wrap m z) = bv_wrap n z.
Proof.
  intros Hle. unfold bv_wrap, bv_modulus.
  apply Z.bits_inj'. intros k Hk.
  destruct (Z.lt_ge_cases k (Z.of_N n)) as [Hlt | Hge].
  - rewrite !Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Definition bv_wf_bool (n : N) (z : Z) : bool :=
  (0 <=? z) && (z <? bv_modulus n).

Lemma bv_wrap_wf (n : N) (z : Z) : bv_wf_bool n (bv_wrap n z) = true.
Proof.
  unfold bv_wf_bool.
  destruct (bv_wrap_in_range n z) as [Hlo Hhi].
  apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; assumption.
Qed.

Record bv (n : N) : Type := BV {
  bv_unsigned : Z;
  bv_wf : bv_wf_bool n bv_unsigned = true
}.
Arguments BV {_} _ _.
Arguments bv_unsigned {_} _.
Arguments bv_wf {_} _.

Definition Z_to_bv (n : N) (z : Z) : bv n :=
  BV (bv_wrap n z) (bv_wrap_wf n z).
Global Arguments Z_to_bv : simpl never.

Lemma bv_eq {n : N} (b1 b2 : bv n) :
  b1 = b2 <-> bv_unsigned b1 = bv_unsigned b2.
Proof.
  split.
  - intros ->. reflexivity.
  - destruct b1 as [u1 w1], b2 as [u2 w2]; cbn.
    intros Heq; subst u2.
    f_equal. apply (UIP_dec Bool.bool_dec).
Qed.

Lemma bv_unsigned_in_range (n : N) (b : bv n) :
  0 <= bv_unsigned b < bv_modulus n.
Proof.
  destruct b as [u w]; cbn.
  unfold bv_wf_bool in w.
  apply andb_true_iff in w as [Hlo Hhi].
  split; [apply Z.leb_le | apply Z.ltb_lt]; assumption.
Qed.

Lemma Z_to_bv_unsigned (n : N) (z : Z) :
  bv_unsigned (Z_to_bv n z) = bv_wrap n z.
Proof. reflexivity. Qed.

Lemma Z_to_bv_small (n : N) (z : Z) :
  0 <= z < bv_modulus n -> bv_unsigned (Z_to_bv n z) = z.
Proof.
  intros H. rewrite Z_to_bv_unsigned. apply bv_wrap_small. exact H.
Qed.

Lemma Z_to_bv_bv_unsigned (n : N) (b : bv n) :
  Z_to_bv n (bv_unsigned b) = b.
Proof.
  apply bv_eq. rewrite Z_to_bv_unsigned.
  apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Definition bv_signed {n : N} (b : bv n) : Z :=
  bv_swrap n (bv_unsigned b).

Lemma Z_to_bv_signed (n : N) (z : Z) :
  bv_signed (Z_to_bv n z) = bv_swrap n z.
Proof.
  unfold bv_signed. rewrite Z_to_bv_unsigned. apply bv_swrap_wrap.
Qed.

Definition bv_add {n : N} (a b : bv n) : bv n :=
  Z_to_bv n (bv_unsigned a + bv_unsigned b).
Definition bv_sub {n : N} (a b : bv n) : bv n :=
  Z_to_bv n (bv_unsigned a - bv_unsigned b).
Definition bv_opp {n : N} (a : bv n) : bv n :=
  Z_to_bv n (- bv_unsigned a).
Definition bv_mul {n : N} (a b : bv n) : bv n :=
  Z_to_bv n (bv_unsigned a * bv_unsigned b).
Definition bv_divu {n : N} (a b : bv n) : bv n :=
  Z_to_bv n (bv_unsigned a / bv_unsigned b).
Definition bv_modu {n : N} (a b : bv n) : bv n :=
  Z_to_bv n (bv_unsigned a mod bv_unsigned b).
Definition bv_quots {n : N} (a b : bv n) : bv n :=
  Z_to_bv n (Z.quot (bv_signed a) (bv_signed b)).
Definition bv_rems {n : N} (a b : bv n) : bv n :=
  Z_to_bv n (Z.rem (bv_signed a) (bv_signed b)).
Definition bv_and {n : N} (a b : bv n) : bv n :=
  Z_to_bv n (Z.land (bv_unsigned a) (bv_unsigned b)).
Definition bv_or {n : N} (a b : bv n) : bv n :=
  Z_to_bv n (Z.lor (bv_unsigned a) (bv_unsigned b)).
Definition bv_xor {n : N} (a b : bv n) : bv n :=
  Z_to_bv n (Z.lxor (bv_unsigned a) (bv_unsigned b)).
Definition bv_not {n : N} (a : bv n) : bv n :=
  Z_to_bv n (Z.lnot (bv_unsigned a)).
Definition bv_shiftl {n : N} (a s : bv n) : bv n :=
  Z_to_bv n (Z.shiftl (bv_unsigned a) (bv_unsigned s)).
Definition bv_shiftr {n : N} (a s : bv n) : bv n :=
  Z_to_bv n (Z.shiftr (bv_unsigned a) (bv_unsigned s)).
Definition bv_ashiftr {n : N} (a s : bv n) : bv n :=
  Z_to_bv n (Z.shiftr (bv_signed a) (bv_unsigned s)).

Definition bv_extract {n : N} (lo len : N) (a : bv n) : bv len :=
  Z_to_bv len (Z.shiftr (bv_unsigned a) (Z.of_N lo)).
Definition bv_zero_extend {n : N} (m : N) (a : bv n) : bv m :=
  Z_to_bv m (bv_unsigned a).
Definition bv_sign_extend {n : N} (m : N) (a : bv n) : bv m :=
  Z_to_bv m (bv_signed a).
Definition bv_concat {n1 n2 : N} (m : N) (a : bv n1) (b : bv n2) : bv m :=
  Z_to_bv m (Z.lor (Z.shiftl (bv_unsigned a) (Z.of_N n2)) (bv_unsigned b)).

Lemma bv_add_unsigned {n : N} (a b : bv n) :
  bv_unsigned (bv_add a b) = bv_wrap n (bv_unsigned a + bv_unsigned b).
Proof. reflexivity. Qed.

Lemma bv_sub_unsigned {n : N} (a b : bv n) :
  bv_unsigned (bv_sub a b) = bv_wrap n (bv_unsigned a - bv_unsigned b).
Proof. reflexivity. Qed.

Lemma bv_mul_unsigned {n : N} (a b : bv n) :
  bv_unsigned (bv_mul a b) = bv_wrap n (bv_unsigned a * bv_unsigned b).
Proof. reflexivity. Qed.

Lemma bv_testbit_high {n : N} (a : bv n) (k : Z) :
  Z.of_N n <= k -> Z.testbit (bv_unsigned a) k = false.
Proof.
  intros Hk.
  destruct (bv_unsigned_in_range n a) as [Hlo Hhi].
  unfold bv_modulus in Hhi.
  rewrite <- (Z.mod_small (bv_unsigned a) (2 ^ Z.of_N n)) by lia.
  apply Z.mod_pow2_bits_high. lia.
Qed.

Lemma bv_and_unsigned {n : N} (a b : bv n) :
  bv_unsigned (bv_and a b) = Z.land (bv_unsigned a) (bv_unsigned b).
Proof.
  unfold bv_and, bv_wrap, bv_modulus; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus.
  apply Z.bits_inj'. intros k Hk.
  destruct (Z.lt_ge_cases k (Z.of_N n)) as [Hlt | Hge].
  - rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite Z.mod_pow2_bits_high by lia.
    rewrite Z.land_spec, (bv_testbit_high a k Hge). reflexivity.
Qed.

Lemma bv_or_unsigned {n : N} (a b : bv n) :
  bv_unsigned (bv_or a b) = Z.lor (bv_unsigned a) (bv_unsigned b).
Proof.
  unfold bv_or; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus.
  apply Z.bits_inj'. intros k Hk.
  destruct (Z.lt_ge_cases k (Z.of_N n)) as [Hlt | Hge].
  - rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite Z.mod_pow2_bits_high by lia.
    rewrite Z.lor_spec, (bv_testbit_high a k Hge), (bv_testbit_high b k Hge). reflexivity.
Qed.

Lemma bv_xor_unsigned {n : N} (a b : bv n) :
  bv_unsigned (bv_xor a b) = Z.lxor (bv_unsigned a) (bv_unsigned b).
Proof.
  unfold bv_xor; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus.
  apply Z.bits_inj'. intros k Hk.
  destruct (Z.lt_ge_cases k (Z.of_N n)) as [Hlt | Hge].
  - rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite Z.mod_pow2_bits_high by lia.
    rewrite Z.lxor_spec, (bv_testbit_high a k Hge), (bv_testbit_high b k Hge). reflexivity.
Qed.

Lemma bv_extract_unsigned {n : N} (lo len : N) (a : bv n) :
  bv_unsigned (bv_extract lo len a) = bv_wrap len (Z.shiftr (bv_unsigned a) (Z.of_N lo)).
Proof. reflexivity. Qed.

Lemma bv_zero_extend_unsigned {n : N} (m : N) (a : bv n) :
  (n <= m)%N -> bv_unsigned (bv_zero_extend m a) = bv_unsigned a.
Proof.
  intros Hle. unfold bv_zero_extend. rewrite Z_to_bv_unsigned.
  apply bv_wrap_small.
  destruct (bv_unsigned_in_range n a) as [Hlo Hhi].
  split; [exact Hlo |].
  eapply Z.lt_le_trans; [exact Hhi |].
  unfold bv_modulus. apply Z.pow_le_mono_r; lia.
Qed.

Lemma bv_sign_extend_unsigned {n : N} (m : N) (a : bv n) :
  bv_unsigned (bv_sign_extend m a) = bv_wrap m (bv_signed a).
Proof. reflexivity. Qed.

Lemma bv_concat_unsigned {n1 n2 : N} (m : N) (a : bv n1) (b : bv n2) :
  m = (n1 + n2)%N ->
  bv_unsigned (bv_concat m a b) = Z.lor (Z.shiftl (bv_unsigned a) (Z.of_N n2)) (bv_unsigned b).
Proof.
  intros Hm. subst m. unfold bv_concat; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus.
  apply Z.bits_inj'. intros k Hk.
  destruct (Z.lt_ge_cases k (Z.of_N (n1 + n2))) as [Hlt | Hge].
  - rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite Z.mod_pow2_bits_high by lia.
    rewrite Z.lor_spec, Z.shiftl_spec by lia.
    rewrite (bv_testbit_high a (k - Z.of_N n2)) by lia.
    rewrite (bv_testbit_high b k) by lia.
    reflexivity.
Qed.

Declare Scope bv_scope.
Delimit Scope bv_scope with bv.
Bind Scope bv_scope with bv.

Infix "+" := bv_add : bv_scope.
Infix "-" := bv_sub : bv_scope.
Infix "*" := bv_mul : bv_scope.
Notation "- x" := (bv_opp x) : bv_scope.
Infix "≪" := bv_shiftl (at level 35) : bv_scope.
Infix "≫" := bv_shiftr (at level 35) : bv_scope.

Definition Z_to_bv_coercion {n : N} (z : Z) : bv n := Z_to_bv n z.
#[warning="-uniform-inheritance"] Coercion Z_to_bv_coercion : Z >-> bv.

Definition Decision (P : Prop) : Type := {P} + {~P}.
Existing Class Decision.
Definition decide (P : Prop) `{H : Decision P} : {P} + {~P} := H.
Notation EqDecision A := (forall x y : A, Decision (x = y)).

Global Instance bv_eq_dec {n : N} : EqDecision (bv n).
Proof.
  intros [u1 w1] [u2 w2].
  destruct (Z.eq_dec u1 u2) as [Heq | Hne].
  - left. subst u2. f_equal. apply (UIP_dec Bool.bool_dec).
  - right. intros H. injection H. exact Hne.
Defined.

Global Instance prod_eq_dec {A B : Type} (HA : EqDecision A) (HB : EqDecision B) : EqDecision (A * B).
Proof. intros [x1 y1] [x2 y2]. unfold Decision. decide equality; [apply HB | apply HA]. Defined.

Global Instance list_eq_dec {A : Type} (HA : EqDecision A) : EqDecision (list A).
Proof. intros x y. apply List.list_eq_dec. exact HA. Defined.

Ltac solve_decision :=
  intros x y; unfold Decision; decide equality; apply (decide (_ = _)).
