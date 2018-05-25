Require Import String.

Inductive EA : Type :=
  |V: string -> EA 
  |N: nat -> EA 
  |Plus: EA -> EA -> EA
  |Suc: EA -> EA.

Definition State := string -> nat.

Print EA_ind.
Print State.

Fixpoint eval (e:EA) (s:State) : nat :=
  match e with
  | V x => s x
  | N n => n
  | Plus e1 e2 => (eval e1 s)+(eval e2 s)
  | Suc e => S (eval e s)
  end.

Fixpoint cf (e:EA):EA :=
 match e with
  | V x => V x
  | N n => N n
  | Plus e1 e2 => match cf e1 with
                   |N n => match cf e2 with 
                            |N k => N (n+k)
                            |_ => Plus (cf e1) (cf e2)
                           end
                   |_ => Plus (cf e1) (cf e2)
                  end
  | Suc e => match cf e with
              |N n => N(S n)
              |_ => Suc (cf e)
             end
 end.

Lemma eq_suc_nat : forall (n:nat), S n = n + 1.
Proof.
  induction n.
  reflexivity.
  simpl.
  rewrite <- IHn.
  trivial.
Qed.

(*a*)
Theorem eq_suc: forall (s:State) (e:EA), eval (Suc e) s = eval e s + 1.
Proof.
  intro.
  destruct e;simpl;apply eq_suc_nat.
Qed.

(*b*)
Theorem eval_cf: forall (s:State) (e:EA), eval e s = eval (cf e) s.
Proof.
  intros.
  induction e;simpl;trivial.
  rewrite IHe1;rewrite IHe2;destruct (cf e1);destruct (cf e2);reflexivity.
  rewrite (IHe);destruct (cf e); reflexivity.
Qed. 

Fixpoint plus (e1 e2:EA) :EA :=
match e1, e2 with
  | N n1, N n2 => N (n1 + n2)
  | N 0, e => e
  | e, N 0 => e
  | a, b => Plus a b
end.

Fixpoint cfp (e:EA):EA :=
 match e with
  | V x => V x
  | N n => N n
  | Plus e1 e2 => plus (cfp e1) (cfp e2)
  | Suc e1 => Suc (cfp e1)
 end.

Lemma mas_cero: forall (n:nat), n + 0 = n.
Proof.
  induction n.
  reflexivity.
  simpl.
  rewrite IHn.
  trivial.
Qed.

(*c*)
Theorem corr_cfp : forall (e:EA) (s:State), eval e s = eval (cfp e) s.
Proof.
  intros.
  induction e;simpl;trivial.
  rewrite IHe1.
  rewrite IHe2.
  destruct (cfp e1);destruct (cfp e2);trivial;destruct n;simpl;trivial;rewrite mas_cero;trivial.
  destruct (cfp e);rewrite IHe;trivial.
Qed.