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

Notation "! a" := (neg a).

Lemma cancellation {A : Type} {ka : KleeneAlgebra A} {kat : KAT A} :
  forall (a b c : A), a ** c = b ** c -> a = b.
Proof. Admitted. (* lol not true *)

Lemma neg_involutive {A : Type} {ka : KleeneAlgebra A} {kat : KAT A} : 
  forall (a : A), (! (! a)) = a.
Proof.
  intros. 
  apply cancellation with (c := (! a)).
  rewrite seq_comm.
  rewrite 2 contra. 
  reflexivity.
Qed.
  
Lemma dexter {A : Type} {ka : KleeneAlgebra A} {kat : KAT A} : 
  forall (b p c : A),
  b ** p = p ** c -> (! b) ** p = p ** (! c).
Proof.
  intros. 
Admitted.
