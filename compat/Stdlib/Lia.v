From Coq.ZArith Require Import ZArith.
From Coq.micromega Require Export Lia.
From Coq.micromega Require Import Zify.

Ltac is_ground_Z x :=
  lazymatch x with
  | Z0 => idtac
  | Z.pos _ => idtac
  | Z.neg _ => idtac
  | (?a + ?b)%Z => is_ground_Z a; is_ground_Z b
  | (?a - ?b)%Z => is_ground_Z a; is_ground_Z b
  | (?a * ?b)%Z => is_ground_Z a; is_ground_Z b
  | (?a / ?b)%Z => is_ground_Z a; is_ground_Z b
  | (?a mod ?b)%Z => is_ground_Z a; is_ground_Z b
  | (?a ^ ?b)%Z => is_ground_Z a; is_ground_Z b
  | (- ?a)%Z => is_ground_Z a
  end.

Ltac zify_eval_const :=
  repeat match goal with
  | H : (?w < _)%Z |- context [ match ?q with 0%Z => 0%Z | Z.pos _ => _ | Z.neg _ => _ end ] =>
      change (match q with 0%Z => 0%Z | Z.pos y' => Z.pos (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO y')))))))))))) | Z.neg y' => Z.neg (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO y')))))))))))) end)
        with w
  | H : context [ (Z.pos ?a ^ Z.pos ?b)%Z ] |- _ =>
      let v := eval vm_compute in (Z.pos a ^ Z.pos b)%Z in
      change (Z.pos a ^ Z.pos b)%Z with v in H
  | |- context [ (Z.pos ?a ^ Z.pos ?b)%Z ] =>
      let v := eval vm_compute in (Z.pos a ^ Z.pos b)%Z in
      change (Z.pos a ^ Z.pos b)%Z with v
  | H : context [ (?a mod Z.pos ?b)%Z ] |- _ =>
      is_ground_Z a;
      let v := eval vm_compute in (a mod Z.pos b)%Z in
      change (a mod Z.pos b)%Z with v in H
  | |- context [ (?a mod Z.pos ?b)%Z ] =>
      is_ground_Z a;
      let v := eval vm_compute in (a mod Z.pos b)%Z in
      change (a mod Z.pos b)%Z with v
  | H : context [ (?a / Z.pos ?b)%Z ] |- _ =>
      is_ground_Z a;
      let v := eval vm_compute in (a / Z.pos b)%Z in
      change (a / Z.pos b)%Z with v in H
  | |- context [ (?a / Z.pos ?b)%Z ] =>
      is_ground_Z a;
      let v := eval vm_compute in (a / Z.pos b)%Z in
      change (a / Z.pos b)%Z with v
  end.

Global Ltac Zify.zify_pre_hook ::= zify_eval_const.
