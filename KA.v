Reserved Notation "a + b" (at level 50, left associativity).
Reserved Notation "a ** b" (at level 25, left associativity).
Reserved Notation "a ^*" (at level 5, left associativity).
(* Reserved Notation "a <= b" (at level 79, left associativity). *)

Class KleeneAlgebra (A : Type) := {
    one : A where "1" := one;
    zero : A where "0" := zero;
    plus : A -> A -> A where "a + b" := (plus a b);
    times : A -> A -> A where "a ** b" := (times a b);
    star : A -> A where "a ^*" := (star a);

    plus_assoc : forall {p q r : A}, p + (q + r) = (p + q) + r;
    plus_comm : forall {a b : A}, a + b = b + a;
    plus_zero : forall {a : A}, a + 0 = a;
    plus_idem : forall {a : A}, a + a = a;
    
    seq_assoc : forall {p q r : A}, p ** (q ** r) = (p ** q) ** r;
    one_seq : forall {p : A}, 1 ** p = p;
    seq_one : forall {p : A}, p ** 1 = 1;

    seq_dist_l : forall {p q r : A}, p ** (q + r) = p ** q + p ** r;
    seq_dist_r : forall {p q r : A}, (p ** q) + r = p ** q + p ** r;

    zero_seq : forall {p : A}, 0 ** p = 0;
    seq_zero : forall {p : A}, p ** 0 = 0;
    unroll_l : forall {p : A}, 1 + p ** p ^* = p ^*;

    (* leq : forall {p q : A}, (p + q = q) -> Prop where "p <= q" := (leq p q);
    (* leq_star_r : forall {p : A}, (1 + p ** (p ^*)) <= (p ^ *)
    
}.
