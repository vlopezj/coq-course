(* Source: http://www-sop.inria.fr/members/Enrico.Tassi/coqws15/coq-master1-1-exercises.v *)

Require Import Bool Arith List.

(* 1. Define a recursive function that takes as input a list of numbers
   and returns the product of these numbers, *)

Fixpoint prodlist (ns : list nat) := unit.

Compute prodlist nil.
Compute prodlist (0 :: 3 :: 7 :: nil).
Compute prodlist (3 :: 4 :: 2 :: nil).

(* 2. Define a recursive function that takes a list of numbers and
   returns true if and only if this list contains the number 0.
   Hint: pattern match on both the list and the elements of the list. *)

Fixpoint has_a_0 (ns : list nat) := unit.

Compute has_a_0 (2 :: 3 :: 0 :: 7 :: nil).
Compute has_a_0 nil.
Compute has_a_0 (3 :: 5 :: nil).

(* 3. Define a recursive function that takes as input two numbers and
   returns true if and only if these two numbers are the same natural
   number (such a function already exists in the Coq libraries
   (function beq_nat, but how would you define such a function), using
   only pattern-matching and recursion. *)

Fixpoint beq (n m : nat) := unit.

Compute beq 4 5.
Compute beq 7 7.

(* 4. Define a recursive function that takes a number n and a number
   a as input and returns a list of numbers containing n elements
   that are all a. *)

Fixpoint mklist (n a : nat) := unit.

Compute mklist 3 0.

(* 5. Define a function that takes a number n and a number a and returns
   the list of n elements a ::a + 1:: · · · ::a + n:: nil. *)

Fixpoint mklist1 (n a : nat) := unit.

Compute mklist1 3 0.

(* 6. Define a function that takes as input a natural number and returns
   an element of option nat containing the predecessor if it exists or
   None if the input is 0. *)

Fixpoint pred (n : nat) := unit.

Compute pred 0.
Compute pred 6.

(* 7. Define a recursive function that takes as input a list of numbers
   and returns the length of this list. *)

Fixpoint length (ns : list nat) := unit.

Compute length nil.
Compute length (2 :: 3 :: nil).

(* 8. Can you write a recursive function values that takes as input a
   function f of type nat -> nat, an initial value a of type nat
   and a count n of type nat and produces the list
   a :: f a :: f (f a) :: ... *)

Fixpoint fold (f : nat -> nat) (a : nat) (n : nat) := unit.

Compute fold (fun x : nat => x) 0 5.
Compute fold (fun x : nat => x + 1) 3 4.
Compute fold S 3 4.

(* 9. To every natural number, we can associate the list of its digits
   from right to left. For instance, 239 should be associated to the list
   9::3::2::nil. We also consider that 0 can be mapped to nil. If l is
   such a list, we can consider the successor of a list of digits.
   For instance, the successor of 9::3::2::nil is 0::4::2.
   Define the algorithm on lists of natural numbers that computes the
   successor of that list. *)

Fixpoint lsucc (ns : list nat) : list nat := nil.

Compute lsucc (3 :: 9 :: 1 :: nil).
Compute lsucc (9 :: 3 :: 1 :: nil).
Compute lsucc (9 :: 9 :: 1 :: nil).
Compute lsucc nil.
Compute lsucc (9 :: nil).

(* 10. Assuming that lsuc is the function defined at the previous
   exercise, define the function nat_digits that maps every natural
   number to the corresponding list of digits (naive solutions are
   welcome, as long as they run). *)

Fixpoint nat_digits_aux (n : nat) := unit.

Definition nat_digits (n : nat) := unit.

Compute nat_digits 2990.

(* 11. In the same context as the previous two exercises, define a function
   value that maps every list of digits to the natural number it
   represents. Thus, value (9::3::2::nil) should compute to 239. *)

Fixpoint value (ns : list nat) := unit.

Compute value (0 :: 2 :: 3 :: 4 :: nil).

(* 12. In the same context as the previous exercises, define a function
   licit that tells whether a list of integers corresponds to the digits
   of natural number: no digit should be larger than 9. For instance,
   licit (9::3::2::0::nil) should compute to true and licit (239::nil)
   should compute to false. *)

Fixpoint licit (ns : list nat) := unit.

Compute licit (9 :: 3 :: 2 :: 0 :: nil).
Compute licit (239 :: nil).

(* 13. In the same context as the previous exercises, define functions
   to add two lists of digits so that the result represents the sum of
   the numbers represented by the lists of digits. In other words
   addl (7::2::nil) (5::3::nil) should return 2::6::nil
   (Hint: you should implement the algorithm you learned in elementary
   school for adding numbers). *)

Fixpoint addl (ns ms : list nat) := unit.

Compute addl (7 :: 2 :: nil) (5 :: 3 :: nil).

(* 14. In the same context as the previous exercises, define a function
   for multiplying a list by a small natural number (by successive
   additions) and then a function mull for multiplying two lists of
   digits. *)

Fixpoint mulln (n : nat) (ms : list nat) := unit.

Compute mulln 3 (2 :: 1 :: nil).

Fixpoint mull (ns ms : list nat) := unit.

Compute 14 * 13.
Compute mull (4 :: 1 :: nil) (3 :: 1 :: nil).
Compute 437 * 25.
Compute mull (7 :: 3 :: 4 :: nil) (5 :: 2 :: nil).
Compute 97 * 75.
Compute mull (7 :: 9 :: nil) (5 :: 7 :: nil).
