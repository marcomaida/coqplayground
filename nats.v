(************ bools ************)
Module Nats.

Inductive nat : Type :=
  | O
  | S (n : nat).

Definition pred (n : nat) : nat :=
  match n with
  | O => O
  | S n' => n'
  end.

Fixpoint plus (a b : nat) :=
  match a with
  | O => b
  | S n' => S(plus n' b)
  end.

Fixpoint minus (a b : nat) :=
  match a,b with
  | O, _ => O
  | _, O => a
  | S a',S b' => minus a' b'
  end.

Fixpoint mult (a b : nat) :=
  match b with
  | O => O
  | S O => a
  | S b' => plus a (mult a b')
  end.

Fixpoint exp (a b : nat) :=
  match b with
  | O => S O
  | S O => a
  | S b' => mult a (exp a b')
  end.

Fixpoint fact (n : nat) :=
  match n with
  | O => O
  | S O => S O
  | S n' => mult n (fact n')
  end.

Fixpoint isEven (n : nat) :=
  match n with
  | O => true
  | S O => false
  | S(S n') => isEven n'
  end.

Definition isOdd (n : nat) := negb (isEven n).


Fixpoint eq (a b : nat) :=
  match a with
  | O => match b with
       | O => true
       | _ => false
       end
  | S a' => match b with
       | O => false
       | S (b') => eq a' b'
       end
  end.

Fixpoint isLessOrEqual (a b : nat) :=
  eq (minus a b) O. 
Fixpoint isLess (a b : nat) :=
  negb (isLessOrEqual b a).

Compute Nats.plus(S (S (S (S O)))) (S(S(O))).
Compute Nats.minus(S (S (S (S O)))) (S(S(O))).
Compute Nats.mult(S (S (S (S O)))) (S(S(O))).
Compute Nats.exp(S (S (S (S O)))) (S(S(O))).
Compute Nats.fact(S (S (S (S O)))).
Compute isEven (Nats.plus(S (S (S (S O)))) (S(S(O)))).
Compute isOdd (Nats.plus(S (S (S (S O)))) (S(S(O)))).

Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x - y" := (minus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.
Notation "x =? y" := (eq x y) (at level 70) : nat_scope.
Notation "x <=? y" := (isLessOrEqual x y) (at level 70) : nat_scope.
Notation "x <? y" := (isLess x y) (at level 70) : nat_scope.

Compute ((S(S O)) * (plus (S O) (S O)) =? S(S(S(S(O))))).
Compute (S(S O)) <=? (S(S(S(S(O))))).
Compute (S(S O)) <=? (S(S(O))).
Compute (S(S O)) <? (S(S(O))).
Compute (S(S O)) <? (S(S(S(O)))).

Compute S(O) + S(S(S(O))).



Check S.
Check pred.
Check Nats.plus.

End Nats.

Theorem neutral : forall n:nat, O + n = n.
Proof. intros n. simpl. reflexivity. Qed.

Theorem xPlusx : forall n m:nat, n = m -> n + n = m + m.
Proof. intros n m H. rewrite -> H. reflexivity. Qed.

Theorem plusId : forall n m o : nat, n = m -> m = o -> n + m = m + o.
intros n m o H H'. rewrite -> H. rewrite <- H'. reflexivity. Qed.

Theorem multZeroPlus : forall n m : nat, (O + n) * m = n * m.
Proof. intros n m. rewrite neutral. reflexivity. Qed.

Theorem multS1 : forall n m : nat,
  m = S n -> m * (S n) = m * m.
Proof. intros n m H. rewrite H. reflexivity. Qed.

Theorem succZero : forall n : nat, (eq (S n) O) = False.
Proof. intros n. destruct n as [|n'] eqn:E.
  - Abort.

Theorem negNeg: forall b : bool, negb(negb b) = b.
Proof. intros b. destruct b eqn:E.
  - simpl. reflexivity.
  - simpl. reflexivity. 
Qed.

Theorem andCommutative : forall a b : bool, andb a b = andb a b.
Proof. intros a b. destruct a eqn:E.
 -destruct b.
    +reflexivity.
    +reflexivity.
 -destruct b.
    +reflexivity.
    +reflexivity. 
Qed.

Theorem andb_commutative' :
  forall b c, andb b c = andb c b.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(* NEXT: More on Notation (Optional) and exercise https://softwarefoundations.cis.upenn.edu/lf-current/Basics.html *)

Theorem andTrueElim: forall b c : bool, 
                     andb b c = true -> c = true.
Proof. intros [] b.
  -simpl. reflexivity.
  -simpl. reflexivity.
  -simpl. reflexivity.
  -simpl. reflexivity.



