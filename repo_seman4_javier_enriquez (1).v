Require Import String.
Require Import Ascii.

Definition L (s : ascii) : Prop := True.

Inductive L1 : string -> Prop :=
| epsilon1 : L1 ""
| cons1 : forall x y, L x -> L1 y -> L1 (String x y).

Inductive L2 : string -> Prop :=
| epsilon2 : L2 ""
| L_e_L2 : forall x, L x -> L2 (String x EmptyString)
| cons2 : forall x y, L2 x -> L2 y -> L2 (x ++ y).

Theorem eq_L1_L2 : forall s, L1 s -> L2 s.
Proof.
induction s. 
constructor.
intro.
inversion H.
apply L_e_L2 in H2.
apply IHs in H3.
assert ((append (String a EmptyString) s) = (String a s)).
reflexivity.
rewrite <- H4.
constructor.
exact H2.
exact H3.
Qed.
