From Coq.Lists Require Export List.

Notation length_app := app_length (only parsing).
Notation length_map := map_length (only parsing).
Notation length_rev := rev_length (only parsing).
Notation length_seq := seq_length (only parsing).
Notation length_repeat := repeat_length (only parsing).
Notation length_firstn := firstn_length (only parsing).
Notation length_skipn := skipn_length (only parsing).
Notation skipn_0 := skipn_O (only parsing).
Notation firstn_0 := firstn_O (only parsing).

Lemma NoDup_app : forall {A : Type} {l1 l2 : list A},
  NoDup l1 -> NoDup l2 -> (forall x, In x l1 -> ~ In x l2) -> NoDup (l1 ++ l2).
Proof.
  intros A l1 l2 H1 H2 Hdisj.
  induction H1 as [| x l1 Hnin H1 IH]; cbn; [exact H2 |].
  constructor.
  - intros Hin. apply in_app_iff in Hin as [Hin | Hin];
      [exact (Hnin Hin) | exact (Hdisj x (or_introl eq_refl) Hin)].
  - apply IH. intros y Hy. apply Hdisj. right. exact Hy.
Qed.
