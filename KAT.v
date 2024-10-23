Require Import KA.

Reserved Notation "! a" (at level 75, right associativity).

Class KAT (A : Type) `{KA : KleeneAlgebra A} := {
  neg : A -> A where "! a" := (neg a);

  plus_dist {a b c : A} : a + (b ** c) = (a + b) ** (a + c);
  plus_one {a : A} : a + 1 = 1;
  excl_mid {a : A} : a + (! a) = 1;
  seq_comm {a b : A} : a ** b = b ** a;
  contra {a : A} : a ** (! a) = 0;
  seq_idem {a : A} : a ** a = a;
}.

