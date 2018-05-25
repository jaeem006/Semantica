(*Javier Enríquez Mendoza*)

Require Import Arith.

Fixpoint compara (n m : nat) : comparison :=
match n, m with
| 0, 0 => Eq
| S n', 0 => Gt
| 0 , S m' => Lt
| S n', S m' => compara n' m'
end.

Theorem eq : forall (n m : nat),compara n m = Eq <-> n = m.
Proof.
induction n.
destruct m; split;trivial.
discriminate.
discriminate.
destruct m.
split; discriminate.
simpl.
destruct IHn with m.
split.
intros.
apply H in H1.
rewrite H1.
trivial.
intros.
inversion H1.
rewrite H3 in H0.
apply H0.
trivial.
Qed.

Theorem Lt : forall (n m : nat), compara n m = Lt <-> n < m.
Proof.
induction n; destruct m; split; intro.
discriminate H.
unfold lt in H.
inversion H.
unfold lt.
apply le_n_S.
apply le_0_n.
reflexivity.
simpl in H.
discriminate H.
inversion H.
simpl in H.
unfold lt.
unfold lt in IHn.
apply le_n_S.
apply IHn.
trivial.
unfold lt in IHn.
destruct IHn with m.
unfold lt in H.
apply le_S_n in H.
apply H1 in H.
simpl.
trivial.
Qed.

Theorem Gt : forall (n m : nat), compara n m = Gt <-> n > m.
Proof.
induction n; destruct m; split; intro.
discriminate H.
unfold gt in H.
unfold lt in H.
inversion H.
discriminate H.
unfold gt in H.
unfold lt in H.
inversion H.
unfold gt.
unfold lt.
apply le_n_S.
apply le_0_n.
reflexivity.
destruct IHn with m.
simpl in H.
apply H0 in H.
unfold gt in H.
unfold gt.
unfold lt in H.
unfold lt.
apply le_n_S.
trivial.
simpl.
unfold gt in H.
unfold gt in IHn.
unfold lt in H.
unfold lt in IHn.
apply le_S_n in H.
apply IHn in H.
trivial.
Qed.
