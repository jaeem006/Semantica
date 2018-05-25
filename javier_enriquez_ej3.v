(* Ejercicio Semanal 3: Semántica y Verificación.
  Javier Enríquez Mendoza 
  415000073 *)

Require Import List.
Require Import ArithRing.
Require Import Bool.

Variable A : Type.

Fixpoint filterbool (p : A -> bool) (l : list A) : list A :=
  match l with
  | nil => nil
  | a :: t => if p a then a :: filterbool p t else filterbool p t
  end.

Check filterbool.

Fixpoint length (l: list A) : nat:=
  match l with
  | nil => 0
  | x :: xs => 1 + (length xs)
  end.

Variable p q : A -> bool.

Lemma primero: forall (xs: list A), length(filterbool p xs) <= length xs.
Proof.
intros.
induction xs.
simpl.
trivial.
destruct (bool_dec (p a) true).
simpl.
rewrite e.
simpl.
intuition.
apply not_true_is_false in n.
simpl.
rewrite n.
intuition.
Qed.

Fixpoint andB (a b: bool): bool :=
  match a,b  with
  | false, _ => false
  | _, false => false
  | true, true => true
  end.

Definition andp (r q: A -> bool): A-> bool:= fun (x:A) => andB(r x)(q x).

Lemma segundo: forall (xs: list A), filterbool (andp p q) xs = filterbool p (filterbool q xs).
Proof.
intros.
induction xs.
simpl.
trivial.
unfold andp in IHxs.
destruct (bool_dec (p a) true).
destruct (bool_dec (q a) true).
simpl.
unfold andp.
rewrite e0.
simpl.
rewrite e.
simpl.
rewrite <- IHxs.
trivial.
apply not_true_is_false in n.
simpl.
unfold andp.
rewrite e.
simpl.
rewrite n.
exact IHxs.
apply not_true_is_false in n.
destruct (bool_dec (q a) true).
simpl.
unfold andp.
rewrite e.
simpl.
rewrite n.
simpl.
exact IHxs.
apply not_true_is_false in n0.
simpl.
unfold andp.
rewrite n0.
rewrite n.
simpl.
exact IHxs.
Qed.

Lemma tercero: forall (xs: list A), filterbool p (filterbool p xs)= filterbool p xs.
Proof.
intros.
induction xs.
simpl.
trivial.
destruct (bool_dec (p a) true).
simpl.
rewrite e.
simpl.
rewrite e.
rewrite IHxs.
trivial.
apply not_true_is_false in n.
simpl.
rewrite n.
exact IHxs.
Qed. 




