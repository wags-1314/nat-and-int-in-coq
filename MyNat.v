Module MyNat.

Inductive Nat: Type :=
  | O
  | S (n : Nat).

Fixpoint plus(n m: Nat) : Nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
end.

Definition succ(n : Nat) : Nat := S n.

Definition pred(n : Nat) : Nat :=
  match n with
  | O => O
  | S n => n
end.

Notation "x + y" := (plus x y) (at level 50, left associativity).

Fixpoint mult(n m: Nat) : Nat :=
  match n with
  | O => O
  | S n' => (mult n' m) + m
end.

Notation "x * y" := (mult x y) (at level 40, left associativity).

Theorem plus_O_n : forall n: Nat,
  O + n = n.
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Theorem plus_n_O : forall n: Nat,
  n + O = n.
Proof.
  intros.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem plus_ident : forall n: Nat,
  n + O = O + n.
Proof.
  intros.
  rewrite plus_n_O.
  simpl.
  reflexivity.
Qed.

Theorem plus_n_Sm : forall n m: Nat,
  n + S m = S (n + m).
Proof.
  intros.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem plus_comm : forall n m: Nat,
  n + m = m + n.
Proof.
  intros.
  induction n as [| n' IHn'].
  - rewrite plus_ident. reflexivity.
  - simpl. rewrite IHn'. rewrite plus_n_Sm. reflexivity.
Qed.

Theorem plus_assoc : forall n m o: Nat,
  (n + m) + o = n + (m + o).
Proof.
  intros.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

(* Learn what tactics injection and apply do (IMP) *)
Theorem S_inject : forall n m: Nat,
  S(m) = S(n) -> m = n.
Proof.
  intros.
  injection H.
  intros.
  apply H0.
Qed.

Theorem mult_O_n : forall n: Nat,
  O * n = O.
Proof.
  simpl.
  reflexivity.
Qed.

Theorem mult_n_O : forall n: Nat,
  n * O = O.
Proof.
  intros.
  induction n as  [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. simpl. reflexivity.
Qed.

Theorem mult_ident : forall n: Nat,
  S O * n = n.
Proof.
  simpl. reflexivity.
Qed.

Theorem plus_swap : forall n m: Nat,
  n + S m = S n + m.
Proof.
  intros.
  rewrite plus_comm.
  simpl.
  replace (m + n) with (n + m).
  - reflexivity.
  - rewrite plus_comm. reflexivity.
Qed.

Theorem mult_n_Sm : forall n m: Nat,
  n * S m = n * m + n.
Proof.
  intros.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. rewrite plus_assoc. rewrite plus_swap. replace (S n' + m) with (m + S n').
    + rewrite plus_assoc. reflexivity.
    + rewrite plus_comm. reflexivity.
Qed.

Theorem mult_comm : forall n m: Nat,
  n * m = m * n.
Proof.
  intros.
  induction n as [| n' IHn'].
  - rewrite mult_n_O. simpl. reflexivity.
  - simpl. rewrite mult_n_Sm. rewrite IHn'. reflexivity.
Qed.

Fixpoint lt(n m: Nat) : bool :=
  match n, m with
  | O, _ => true
  | _, O => false
  | S n,S m => lt n m
end.

Fixpoint eqb(n m : Nat) : bool :=
  match n, m with
  | O, O => true
  | O, _ => false
  | _, O => false
  | S n', S m' => eqb n' m'
end.

Inductive List : Type :=
  | nil
  | cons (n : nat) (l : List).

Inductive Comparative : Type := 
  | LT
  | EQ
  | GT.

Fixpoint compare_nat (n m: Nat) : Comparative :=
  match n, m with
  | O, O => EQ
  | O, _ => LT
  | _, O => GT
  | S n', S m' => compare_nat n' m'
end.

Notation "x <? y" := (lt x y) (at level 55, left associativity).
Notation "x =? y" := (eqb x y) (at level 55, left associativity).
Notation "x <=> y" := (compare_nat x y) (at level 55, left associativity).

Fixpoint monus(n m: Nat): Nat :=
  match m with
  | O => n
  | S m' => pred (monus n m')
end.

Inductive Int : Type :=
  | ZO
  | ZP (n: Nat)
  | ZN (n: Nat).

Definition pos_sub (n' m': Nat) : Int :=
  match (n' <=> m') with
  | LT => ZN (monus m' n')
  | EQ => ZO
  | GT => ZP (monus n' m')
end.

Definition Zplus (n m: Int) : Int := 
  match n, m with
  | ZO, _ => m
  | _, ZO => n
  | ZP n', ZP m' => ZP (plus n' m')
  | ZN n', ZN m' => ZN (plus n' m')
  | ZP n', ZN m' => pos_sub n' m'
  | ZN n', ZP m' => pos_sub m' n'
end.

Definition Zmult (n m: Int) : Int := 
  match n, m with
  | ZO, _ => ZO
  | _, ZO => ZO
  | ZP n', ZP m' => ZP (mult n' m')
  | ZN n', ZN m' => ZP (mult n' m')
  | ZP n', ZN m' => ZN (mult n' m')
  | ZN n', ZP m' => ZN (mult n' m')
end.

Notation "x +/ y" := (Zplus x y) (at level 50, left associativity).
Notation "x */ y" := (Zmult x y) (at level 40, left associativity).

(* Identity of +/ *)

Theorem Zplus_ZO_n : forall n: Int,
  ZO +/ n = n.
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Theorem Zplus_n_ZO : forall n: Int,
  n +/ ZO = n.
Proof.
  intros.
  destruct n.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem Zplus_comm : forall n m: Int,
  n +/ m = m +/ n.
Proof.
  intros.
  destruct n.
  - simpl. rewrite Zplus_n_ZO. reflexivity.
  - destruct m.
    + simpl. reflexivity.
    + simpl. rewrite plus_comm. reflexivity.
    + simpl. reflexivity.
  - destruct m.
    + simpl. reflexivity.
    + simpl. reflexivity.
    + simpl. rewrite plus_comm. reflexivity.
Qed.

End MyNat.
Search plus.
