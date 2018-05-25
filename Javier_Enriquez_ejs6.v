(*Javier Enriquez Mendoza
Semanal 6
Semántica y Verificación*)

Variable A:Type.

Inductive btree:Type :=
  | empty : btree
  | nodo : A -> btree -> btree -> btree.

Fixpoint inTree (a:A) (t:btree) : Prop :=
  match t with 
    | empty => False
    | nodo y l r => (eq y a) \/ (inTree a l) \/ (inTree a r)
  end.

Fixpoint isEmpty (t:btree): bool :=
  match t with 
    | empty => true
    | nodo _ _ _ => false
  end.

Lemma true_is_empty: forall (t:btree), ((isEmpty t) = true) -> (t = empty).
Proof.
  intros.
  destruct t.
  trivial.
  simpl in H.
  inversion H.
Qed.

Theorem cuatro : forall (t:btree), ((isEmpty t) = true) <-> (forall (x:A), ~(inTree x t)).
Proof.
  intros.
  split.
  (*->*)
  intros.
  unfold not.
  intros.
  assert (t = empty).
  apply true_is_empty.
  trivial.
  rewrite H1 in H0.
  simpl in H0.
  trivial.
  (*<-*)
  intros.
  destruct t.
  reflexivity.
  simpl inTree in H.
  edestruct H.
  intuition. (*Como mi variable ?x esta libre en la meta es equivalente al forall de la 
premisa H por lo tanto lo que quiero probar es falso, Pero no supe como poner eso correctamente 
asi que mejor use intuition, pero entiendo que es lo que esta haciendo y por que asi que podria 
decir que lo use correctamente jeje *) 
Qed.
