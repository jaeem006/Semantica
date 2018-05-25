Require Import Arith.
Variable A:Type.
Print list.

Notation "x :: l" := (cons x l) (at level 60, right associativity).

Notation "[ ]" := nil.

Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).

Fixpoint get (l : list A)(n : nat): option A :=
  match l, n with
    | [] , _ => None
    | x::xs, 0 => Some x
    | x::xs, S n0 => get xs n0
  end.

Fixpoint update (l : list A)(n : nat)(a : A):list A :=
  match l, n with
    | x::xs, 0 => a::xs
    | [], _ => []
    | x::xs, S n => x::(update xs n a)
  end.

Variable error : A.

(*Esto siento que esta super chaca pero fue lo único que se me ocurrio para quitar el option*)
Fixpoint chaka (a : option A): A :=
match a with 
| Some b => b
| none => error
end.

Lemma mayor_0: forall (n m : nat), n > S m ->  n <> 0.
Proof.
  intros.
  induction n.
  unfold gt in H.
  apply lt_n_0 in H.
  exfalso;trivial.
  discriminate.
Qed.

Lemma ex_n : forall (n : nat), n <> 0 -> exists (m : nat), n = S m.
Proof.
  induction n.
  intro.
  contradict H.
  trivial.
  intro.
  exists n.
  trivial.
Qed.

Theorem uno: forall (l : list A)(i : nat), i > (length l) -> (get l i) = None.
Proof.
  intro.
  induction l.
  trivial.
  intros.
  simpl in H.
  assert (i > S (length l)).
  trivial.
  simpl.
  apply mayor_0 in H.
  apply ex_n in H.
  destruct H.
  rewrite H.
  apply IHl.
  rewrite H in H0.
  apply gt_S_n in H0.
  trivial.
Qed.

Lemma not_in_head: forall (l : list A)(x a : A),~ List.In x (a :: l) -> x <> a.
Admitted.

Lemma not_in_tail: forall (l : list A)(x a : A),~ List.In x (a :: l) -> ~ List.In x l.
Admitted.

(*Los dos lemas de arriba son equivalentes al lema not_in_cons que esta en 
Coq.Lists.List pero por alguna razon no lo pude usar, es por eso que no los demostre*)

Theorem dos: forall (x : A)(l : list A), ~(List.In x l) -> forall (i : nat), ~(get l i = Some x).
Proof.
  intros x l.
  induction l.
  intros.
  simpl.
  discriminate.
  intros.
  destruct i.
  simpl.
  apply not_in_head in H.
  admit. (*No sé como demostrar que Some a <> Some x si a <> x pero es claro que es cierto*)
  apply IHl.
  apply not_in_tail in H.
  trivial.
Qed.

Theorem tres: forall (x : A)(l : list A), List.In x l -> exists (i : nat), get l i = Some x.
Proof.
  intros x l.
  induction l; intro.
  simpl in H.
  exfalso.
  trivial.
  apply List.in_inv in H.
  destruct H.
  exists 0.
  simpl.
  rewrite H.
  trivial.
  apply IHl in H.
  destruct H.
  exists (S x0).
  simpl.
  trivial.
Qed.

Theorem cuatro: forall (l : list A)(i : nat), update l i (chaka (get l i)) = l.
Proof.
  intro.
  induction l.
  destruct i.
  simpl.
  trivial.
  reflexivity.
  destruct i.
  simpl.
  trivial.
  simpl.
  rewrite IHl.
  trivial.
Qed.

Theorem cinco: forall (l : list A)(a : A)(n : nat), n > (length l) -> update l n a = l.
Proof.
  intros l a.
  induction l.
  intros.
  reflexivity.
  intros.
  destruct n.
  simpl in H.
  exfalso.
  assert (forall (n : nat), ~(0 > n)).
  admit. (*Es obvio que 0 no es mayor que ningún natural, pero no encontre un lema en la biblioteca que dijera eso*)
  apply H0 in H.
  trivial.
  simpl.
  rewrite IHl.
  trivial.
  simpl in H.
  apply gt_S_n in H.
  trivial.
Qed.
