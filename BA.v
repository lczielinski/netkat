Reserved Notation "p + q" (at level 50, left associativity).
Reserved Notation "p ** q" (at level 25, left associativity).
Reserved Notation "! a" (at level 75, right associativity).

Class BooleanAlgebra (A : Type) := {
    one : A where "1" := one;
    zero : A where "0" := zero;
    plus : A -> A -> A where "p + q" := (plus p q);
    times : A -> A -> A where "p ** q" := (times p q);
    neg : A -> A where "! a" := (neg a);

    plus_dist {a b c : A} : a + (b ** c) = (a + b) ** (a + c);
    plus_one {a : A} : a + 1 = 1;
    excl_mid {a : A} : a + (! a) = 1;
    seq_comm {a b : A} : a ** b = b ** a;
    contra {a : A} : a ** (! a) = 0;
    seq_idem {a : A} : a ** a = a;
}.

