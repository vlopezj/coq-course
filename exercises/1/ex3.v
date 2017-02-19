Section Three.

(* 1. Define a function lo that takes a natural number n as input
   and returns the list containing the first n odd natural numbers.
   For instance lo 3 = 5::3::1. *)

Fixpoint lo (n : nat) : list nat := nil.

(* 2. Prove that length (lo n) = n. *)

Lemma ex3_2 : forall n, length (lo n) = n.

(* 3. Define a function sl that takes a list of natural numbers as
      input and returns the sum of all the elements in the list. *)

Fixpoint sl (ns : list nat) : nat := 0.

(* 4. Prove that sl (lo n) = n * n. *)

Lemma ex3_4 : forall n, sl (lo n) = n * n.

(* 5. We define a function add with the following code: *)

Fixpoint add x y := match x with 0 => y | S p => add p (S y) end.

(*    Prove the following lemmas: *)

Lemma ex3_5a : forall x y, add x (S y) = S (add x y).

Lemma ex3_5b : forall x, add x 0 = x.

Lemma ex3_5c : forall x y, add (S x) y = S (add x y).

Lemma ex3_5d : forall x y z, add x (add y z) = add (add x y) z.

Lemma ex3_5e : forall x y, add x y = x + y.

(* 6. In the exercises part of the first chapter of these course
      notes, you are required to define a function that describes
      when a list of numbers is a licit representation of a natural
      number (it verifies that all digits are less than 10) and a
      function that computes the successor of a number when
      represented as a list of digits. Add the function to_nat that
      maps any list of digits to the natural number it represents
      and show that the successor function is correct in this
      context. *)

Load ex1.

Fixpoint to_nat (ns : list nat) : nat := 0.

Lemma ex3_6 : forall ns, to_nat (lsucc ns) = S (to_nat ns).

End Three.
