From Practice Require Import MyNat.

Module MyInt.

Inductive Int : Type :=
  | Pos (n : nat)
  | Neg (n : nat).

End MyInt.