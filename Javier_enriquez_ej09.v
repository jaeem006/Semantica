Require Import NPeano.
Require Import List.
Require Import Arith.

Variable A:Type.

Notation " [ ] " := nil.
Notation " [ x ] " := (cons x nil).
Notation " [ x , y , .. , z ] " := (cons x (cons y .. (cons z nil) ..)).
Notation " ( x :: l ) " := (cons x l).

Inductive Tree : Type :=
  | Leaf : A -> Tree
  | Node : A -> Tree -> Tree -> Tree.

Inductive RAList : Type :=
| NilRa : RAList
| ConsRa : Tree -> nat -> RAList -> RAList.

Fixpoint rahead (t : RAList): option A :=
match t with
| NilRa => None
| ConsRa b _ _ => match b with
                 | Leaf a  => Some a
                 | Node a _ _ => Some a
                 end
end.

Fixpoint ratail (l :RAList) : RAList :=
match l with 
| NilRa => NilRa
| ConsRa t n ts => match t with
                   | Leaf _ => ts
                   | Node _ tl tr => ConsRa tl (n / 2) (ConsRa tr (n / 2) ts)
                   end
end.

Fixpoint racons (a : A) (l : RAList) : RAList :=
match l with 
| NilRa => ConsRa (Leaf a) 1 NilRa
| ConsRa t n ls => match ls with
                   | ConsRa t1 n ls1 => ConsRa (Node a t t1) (n + 1) ls1
                   | otherwise => ConsRa (Leaf a) 1 l
                   end 
end.

Fixpoint flatTree (t : Tree) : list A :=
match t with
| Leaf a => [a]
| Node a tl tr => app (a :: (flatTree tl)) (flatTree tr)
end.

Fixpoint flat (l : RAList) : list A:=
match l with
| NilRa => []
| ConsRa t _ ls => (flatTree t) ++ (flat ls)
end.

Theorem corr_rahead : forall (r : RAList), rahead r = head (flat r).
Proof.
 intros.
 destruct r.
 reflexivity.
 destruct t;reflexivity.
Qed.

Theorem corr_ratail : forall (r : RAList), flat (ratail r) = tail (flat r).
Proof.
 intros.
 destruct r.
 reflexivity.
 destruct t.
 reflexivity.
 simpl.
 apply app_assoc.
Qed.

Fixpoint hight (t : Tree) : nat :=
match t with 
| Leaf _ => 1 
| Node _ t1 t2 => (max (hight t1) (hight t2)) + 1
end. 

Inductive perfect : Tree -> Prop :=
| p_leaf : forall (x : A), perfect  (Leaf x)
| p_node : forall (t1 t2 : Tree) (x : A), perfect t1 -> perfect t2 -> (eq (hight t2) (hight t2)) -> perfect (Node x t1 t2).

Inductive aux_valid : RAList -> nat -> Prop :=
| av_nil : forall n, aux_valid NilRa n
| av_cons : forall (t : Tree) (h n: nat) (ls : RAList), perfect t -> (eq (hight t) h) -> (lt n h) -> (aux_valid ls h) -> aux_valid (ConsRa t h ls) n.  

Inductive validRAL : RAList -> Prop :=
| vr_nil : validRAL NilRa
| vr_cons: forall (t : Tree) (h: nat) (ls : RAList), (perfect t) -> (eq (hight t) h) -> (aux_valid ls (h -1)) -> validRAL (ConsRa t h ls).

Theorem corr_racons : forall (a : A) (ls : RAList), validRAL ls -> validRAL (racons a ls).
Proof.
 intros.
 induction H.
 unfold racons.
 constructor.
 constructor.
 reflexivity.
 constructor.
 inversion H1.
 simpl.
 constructor.
 constructor.
 constructor.
 constructor.
 trivial.
 trivial.
 simpl.
 admit. (*tengo que h = hight t entonces al menos es 1 y forall (n : nat), 0 > S n *)
 constructor.
 constructor.
 constructor.
 trivial.
 exact H2.
 reflexivity.
 simpl.
 rewrite H3.
 rewrite H0.
 unfold lt in H4.
 unfold max.
 admit. (*Tengo en H4 que h <= h0 entonces el max h h0 = h0 porque en el peor de los casos son iguales*)
 cut (h0 = h0 + 1 - 1).
 intro.
 rewrite <- H8.
 trivial.
 cut (h0 + 1 - 1 = h0 + (1 - 1)).
 intros.
 rewrite H8.
 simpl.
 admit. (*Es obvio que si le sumo 1 a h0 y luego le resto uno e h0*)
Admitted.