(* Sources:
   - http://www-sop.inria.fr/members/Enrico.Tassi/coqws15/coq-master1-2-exercises-morning.v
   - http://www-sop.inria.fr/members/Enrico.Tassi/coqws15/coq-master1-2-exercises.v *)

Require Import Bool Arith List.

Variables P Q R : Prop.

(* 5. Write the script that proves the following formula
   (P -> (P /\ Q) -> R) -> P /\ (Q /\ P) -> R. *)

Lemma ex5 :
   (P -> (P /\ Q) -> R) -> P /\ (Q /\ P) -> R.
Proof.
...
Qed.

(* 7. Write the script that proves the following formula
     (P /\ Q) \/ R -> P \/ R *)

Lemma ex7 : ...


(* 7. Write the script that proves the following formula
   ((P -> Q \/ P) -> R) -> R \/ Q  *)

Lemma ex8 : ...

(* 6. Write the script that proves the following formula
   forall (P Q : nat -> Prop),
   forall (x y : nat), (forall z, P z -> Q z) -> x = y -> P x ->
     P x /\ Q y. *)

Lemma ex6 : ...

(* 8. Write the script that proves the following formula
   forall P : nat -> Prop, (forall x, P x) ->
     exists y:nat, P y /\ y = 0 *)

Lemma ex8 : ...


(* 1. Write a predicate multiple_of type nat -> nat -> Prop,
   so that multiple a b expresses that a is a multiple of b
  (in other words, there exists a number k such that a = k * b). *)

Definition multiple_of a b := ...

(* 2. Write a formula using natural numbers that expresses that when
   n is even (a multiple of 2) then n * n is even. *)

... even n ...

Check forall n, even n -> even (n * n).

(* 3. Write a formula using natural numbers that expresses that when
   a number n is a multiple of some k, then n * n is a multiple of k
   (you don’t have to prove it yet). *)

Check ...

(* 4. Write a predicate odd of type nat -> Prop that characterize
   odd numbers like 3, 5, 37.  Avoid ~ (even ..). *)

... odd n ...

(* 9. Search the lemma proving associativity of multiplication *)

SearchAbout ...

(* 10. Write the script that proves that when n is a multiple of k,
   then n * n is also a multiple of k. *)

Lemma ex10 : ...

(* 11. Search the lemmas proving the following properties:
   - distributivity of plus and mult
   - associativity of plus
   - 1 is a neutral elelemt for multiplication *)

...

(* 12. Show that the sum of two even numbers is even *)

Lemma ex12 : ...

(* 13. Write the script that proves that when n is odd,
   then n * n is also odd. *)

Lemma ex13 : ...
