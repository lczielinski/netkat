Reserved Notation "p + q" (at level 50, left associativity).
Reserved Notation "p ** q" (at level 25, left associativity).
Reserved Notation "p ^*" (at level 5, left associativity).
Reserved Notation "p <= q" (at level 70).

Definition relation (A : Type) := A -> A -> Prop.

Definition reflexive {A : Type} (R : relation A) := 
    forall a : A, R a a.
Definition transitive {A : Type} (R : relation A) :=
    forall a b c : A, (R a b) -> (R b c) -> (R a c).
Definition antisymmetric {A : Type} (R : relation A) :=
    forall a b : A, (R a b) -> (R b a) -> a = b.

Definition order {A : Type} (R : relation A) :=
  (reflexive R) /\ (antisymmetric R) /\ (transitive R).

Class KleeneAlgebra (A : Type) := {
    one : A where "1" := one;
    zero : A where "0" := zero;
    plus : A -> A -> A where "p + q" := (plus p q);
    times : A -> A -> A where "p ** q" := (times p q);
    star : A -> A where "p ^*" := (star p);

    plus_assoc {p q r : A} : p + (q + r) = (p + q) + r;
    plus_comm {p q : A} : p + q = q + p;
    plus_zero {p : A} : p + 0 = p;
    plus_idem {p : A} : p + p = p;
    
    seq_assoc {p q r : A} : p ** (q ** r) = (p ** q) ** r;
    one_seq {p : A} : 1 ** p = p;
    seq_one {p : A} : p ** 1 = 1;

    seq_dist_l {p q r : A} : p ** (q + r) = p ** q + p ** r;
    seq_dist_r {p q r : A} : (p ** q) + r = p ** q + p ** r;

    zero_seq {p : A} : 0 ** p = 0;
    seq_zero {p : A} : p ** 0 = 0;
    unroll_l {p : A} : 1 + p ** p ^* = p ^*;
    unroll_r {p : A} : 1 + (p ^*) ** p = p ^*;

    leq : relation A where "p <= q" := (leq p q);
    leq_order : order leq;
    leq_ordering {p q : A} : p <= q <-> p + q = q;

    lfp_l {p q r : A} : q + p ** r <= r -> p ^* ** q <= r;
    lfp_r {p q r : A} : p + q ** r <= q -> p ** r ^* <= q;
}.

Notation "p + q" := (plus p q).
Notation "p ** q" := (times p q).
Notation "p ^*" := (star p).
Notation "1" := one.
Notation "0" := zero.
