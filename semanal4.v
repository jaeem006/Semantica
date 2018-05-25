Variable A: Type.
Variable empty: A.
Variable x z : A.

Inductive ls1: A -> Prop :=
  | ls1_empty: ls1 empty
  | ls1_x : ls1 x
  | ls1_xy: ls1 x ->  A -> ls1 x.


Inductive ls2: A -> Prop :=
  | ls2_empty: ls2 empty
  | ls2_x : ls2 x
  | ls2_xy: ls2 x -> ls2 x -> ls2 x.

Lemma uno: forall (y : A), ls1 y <-> ls2 y.
Proof.
  intro.
  split.
  (* ida *)
  intro.
  induction H.
  constructor.
  constructor.
  trivial.
  (*vuelta *)
  intros.
  induction H.
  constructor.
  constructor.
  trivial.
Qed.