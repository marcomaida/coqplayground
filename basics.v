

(************ bools ************)

Inductive bool : Type :=
  | true
  | false.

Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Notation "a && b" := (andb a b).
Notation "a || b" := (orb a b).

Example test_orb1: (true || false) = true.
Proof. simpl. reflexivity. Qed.

Theorem demorgan : forall (b1:bool) (b2:bool), negb (b1 && b2) = (negb b1) || (negb b2).
Proof. intros b1 b2. destruct b1. simpl. reflexivity. simpl. reflexivity. Qed.

Definition nandb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => negb b2
  | false => true
  end.

Example test_nandb1: (nandb true false) = true.   Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.  Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.   Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.   Proof. simpl. reflexivity. Qed.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool := b1 && b2 && b3.

Example test_andb31: (andb3 true true true) = true.   Proof. simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false. Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false. Proof. simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false. Proof. simpl. reflexivity. Qed.

(* Checking Types of inductives/functions
Check true.
Check negb.
*)

(************ Inductives ************)

Inductive rgb : Type :=
  | red
  | green
  | blue.

Inductive color : Type :=
  | black
  | white
  | primary (p : rgb).

Definition monochrome (c : color) : bool :=
  match c with
  | black => true
  | white => true
  | primary q => false
  end.

Definition isred (c : color) : bool :=
  match c with
  | black => false
  | white => false
  | primary red => true
  | primary _ => false
  end.

Inductive bit : Type :=
  | B0
  | B1.

Inductive nybble : Type :=
  | bits (b0 b1 b2 b3 : bit).

Check (bits B1 B0 B1 B0).

Definition all_zero (nb: nybble) : bool :=
  match nb with
  | (bits B0 B0 B0 B0) => true
  | (bits _ _ _ _) => false
  end.

Compute (all_zero (bits B0 B0 B1 B0)).
Compute (all_zero (bits B0 B0 B0 B0)).
