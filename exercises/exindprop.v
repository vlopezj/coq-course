(*
# Inductive propositions

```coq
*)

Section IndProp.

(*
```

We will use the following tactics:

  - `induction`
  - `apply`
  - `congruence`  (subsumes  `exact`, `assumption`, `reflexivity`)
  - `simpl`, `simpl <definition>`: Unfolding of definitions. Also `unfold`.
  - `trivial`: Like `auto`, but with a very limited search depth.
  - `repeat`: Milk a tactic dry. Good with `try`.
  - `tauto`: Solves propositional logic problems.
  - `replace`: Replaces a term by another, generates subgoal to show that they are equal.
  - `rewrite`: Replaces a term by another using a hypothesis.

We will introduce

  - `unfold` (and `fold`)

  - `discriminate`
  - `generalize`
  - `remember`
  - `inversion` (subsumes `destruct` (as) )


## Defining inductive properties

How to define the even natural numbers in Coq?

1. Mathematical characterisation.

   `unfold` and `discriminate`.

```coq
*)

Definition even_p (n : nat) : Prop := exists k, n = k + k.

Example even_8 : even_p 8.
unfold even_p.
exists 4.
simpl.
reflexivity.
Qed.


Example not_even_1 : ~(even_p 1).
unfold even_p.
intro.
destruct H as [ k Pk ].
destruct k.
simpl in Pk.
discriminate Pk.
simpl in Pk.
(* plus_n_Sm: forall n m : nat, S (n + m) = n + S m *)
rewrite <- plus_n_Sm in Pk.
discriminate Pk.
Qed.

(*
```

2. Decision algorithm.

```coq
*)

Fixpoint is_even (n : nat) : bool :=
  match n with
  | 0         => true
  | 1         => false
  | (S (S n)) => is_even n
  end.

Example is_even_5 : is_even 6 = true.
simpl. reflexivity.
Qed.

Example not_is_even_1 : is_even 1 = false.
simpl. reflexivity.
Qed.

(*
```

These are equivalent: proof in the appendix.

- Disadvantages

  - Mathematical characterizations are opaque
    (what does a proof of n = k + k look like?)
    They cannot be inspected, one can only gaze at them.

  - Decision procedures are only good for decidable properties.

Enter inductive predicates.

## Inductive predicates

Let’s take `even` as an example.

```coq
*)
Inductive even : nat -> Prop :=
  | even_0  : even 0
  | even_SS : forall n : nat, even n -> even (S (S (n))).

Example even_6 : even 6.
exact (even_SS 4 (even_SS 2 (even_SS 0 even_0))).
Qed.

Example even_4 : even 4.
apply even_SS.
apply even_SS.
apply even_0.
Qed.

Example even_200 : even 200.
repeat constructor.
Qed.

Example not_even_5 : ~(even 5).
intro H5.
inversion H5.
inversion H0.
inversion H2.
Qed.

(*
```

### Generalize

The importance of being general: `generalize`.

```coq
*)
Proposition even_correct : forall n, even n <-> even_p n.
  split.
  (* -> *)
    unfold even_p.
    intro H.
    induction H.
    (* H = even_0 *)
    exists 0. trivial.
    (* H = even_SS n' Hn' *)
    destruct IHeven as [ k Pk ].
    exists (S k).
    simpl "+". rewrite <- plus_n_Sm.
    congruence.

  (* <- *)
  unfold even_p.
  intros.
  destruct H as [ k Pk ].
  (* per AndreasLoow, you can do 'generalize dependent n' instead *)
  generalize n Pk.
  clear n Pk.
  induction k.
  intros. rewrite Pk. apply even_0.
  intros.
  rewrite Pk.
  simpl "+". rewrite <- plus_n_Sm.
  apply even_SS.
  apply IHk. trivial.
Qed.
(*
```

Exercises:

```coq
*)
Fixpoint nat_eq (m n : nat) : bool :=
  match m, n with
    | 0, 0 => true
    | S m, S n => nat_eq m n
    | _, _ => false
  end.

Lemma nat_eq_correct : forall m n, nat_eq m n = true <-> m = n.
Admitted.

(*
```

## Inductive relations

```coq
*)

Inductive le : nat -> nat -> Prop :=
  | le_n : forall n, le n n
  | le_S : forall m n, le m n -> le m (S n).

Notation "m ≤ n" :=  (le m n) (at level 30).

Example le_3_5 : 3 ≤ 5.
apply le_S.
apply le_S.
apply le_n.
Qed.

Example le_big : 2 ≤ 20.
apply le_S.
apply le_S.
repeat (try (apply le_n); apply le_S).
Qed.

Example not_le_2_1 : ~(2 ≤ 1).
intro.
inversion H as [|m n H1].
inversion H1.
Qed.

Example not_le_100_10 : ~(100 ≤ 10).
intro.
repeat (rename H into H'; inversion H' as [|? ? H]; clear H').
Qed.

(*
```

### Remember to `remember`

The `induction` tactic is an amnesiac fellow.

```coq
*)
Lemma le_Sm_n_bad : forall m n, S m ≤ n -> m ≤ n.
  intros.
  remember (S m) as sm.
  induction H.
  (* H = le_n *)
  rewrite Heqsm.
  apply le_S.
  apply le_n.
  (* H = le_S *)
  apply le_S.
  apply IHle.
  trivial.
Qed.

Fixpoint le_Sm_n (m n : nat) ( H : S m ≤ n) : m ≤ n.
  inversion H.
  apply le_S.
  apply le_n.
  (* H = le_S *)
  apply le_S.
  apply le_Sm_n.
  assumption.
Qed.

Print le_Sm_n.

(*
```

When doing induction on an inductive proposition, we need to
explicitly remember the indices.

```coq
*)
(*
```

### Exercises:

(Software Foundations, IndProp).
R_provability2, R_fact:

```coq
*)

Section R.

Inductive R : nat -> nat -> nat -> Prop :=
   | c1 : R 0 0 0
   | c2 : forall m n o, R m n o -> R (S m) n (S o)
   | c3 : forall m n o, R m n o -> R m (S n) (S o)
   | c4 : forall m n o, R (S m) (S n) (S (S o)) -> R m n o
   | c5 : forall m n o, R m n o -> R n m o.

(*
```
    * Which of the following propositions are provable?
```coq
*)
Example exR1 : R 1 1 2. Admitted.
Example exR2 : R 2 2 6. Admitted.
(*
```

    * If we dropped constructor c5 from the definition of R, would the set of provable propositions change?
    * If we dropped constructor c4 from the definition of R, would the set of provable propositions change?

```coq
*)
Definition fR : nat -> nat -> nat.
Admitted.


Theorem R_equiv_fR : forall m n o, R m n o <-> fR m n = o.
Admitted.

End R.
(*
```

## Case study: regular expressions

```coq
*)

Require Import Bool List.
Import ListNotations.

Inductive regex (T : Type) : Type :=
  | empty   : regex T
  | ε       : regex T
  | char    : T -> regex T
  | concat  : regex T -> regex T -> regex T
  | union   : regex T -> regex T -> regex T
  | star    : regex T -> regex T.

Notation "∅" := (empty _).
Arguments ε {T}.
Notation "« x »" := (char _ x).
Notation "x · y" := (concat _ x y) (at level 35, right associativity).
Notation "x ∪ y" := (union _ x y) (at level 55, right associativity).
Notation "x **" := (star _ x) (at level 10).
(*
```

Examples of regular expressions.

```coq
*)

Example re_all_true : regex bool := (« true » **).

Example re_length_one : regex bool := (« true » ∪ « false »).

Example re_even_length : regex bool :=
  ((« true » ∪ « false ») · (« true » ∪ « false »)) **.

Example re_odd_length : regex bool.
  refine (_ · (_ · _) **); exact re_length_one.
Defined.

Eval compute in re_odd_length.
(*
```

What does it mean for a regular expression to match a string?

```coq
*)
Inductive matches {T} : regex T -> list T -> Prop :=
  | m_empty  : matches ε []
  | m_char   : forall x, matches « x »  [x]
  | m_concat : forall xs ys r₁ r₂,
              matches r₁ xs ->
              matches r₂ ys ->
              matches (r₁ · r₂) (xs ++ ys)
  | m_unionL : forall xs r₁ r₂,
              matches r₁ xs ->
              matches (r₁ ∪ r₂) xs
  | m_unionR : forall xs r₁ r₂,
              matches r₂ xs ->
              matches (r₁ ∪ r₂) xs
  (* Alternative:
  | m_union : forall xs r₁ r₂,
              matches r₁ xs \/ matches r₂ xs ->
              matches (r₁ ∪ r₂) xs
  *)
  | m_star0  : forall r₁, matches (r₁ **) []
  | m_starS  : forall xs ys r,
      matches r xs ->
      matches (r **) ys ->
      matches (r **) (xs ++ ys).

Notation "s ∈ re" := (matches re s) (at level 80).

Example match_length_one : forall b, [b] ∈ re_length_one.
intros.
unfold re_length_one.
induction b.
apply m_unionL. apply m_char.
apply m_unionR. apply m_char.
Defined.


Eval compute in match_length_one.

Example match_odd_3 : [true;true;false] ∈ re_odd_length.
unfold re_odd_length.
apply (m_concat [true] [true; false]).
apply match_length_one.
apply (m_starS [true; false] []).
apply (m_concat [true] [false]).
apply match_length_one.
apply match_length_one.
apply m_star0.
Defined.

Eval compute in match_odd_3.

(*
```

Good!

### Exercises


1. Define a decision procedure to check if a regular expression
   accepts the empty string, and show it correct.

```coq
*)

Fixpoint ε_in (T : Type) (re : regex T) : bool.
Admitted.

Arguments ε_in {T} _.

Lemma ε_in_good {T} (re : regex T) : ε_in re = true <-> [] ∈ re.
Admitted.
(*
```

  Ultimately, we want to decide if an expression matches a given list.
  We can only do this if we have a way of comparing elements in the alphabet
  for equality.

  To simplify, we will work with regular expresions over the boolean alphabet.
  It is easy to generalize this to any type with decidable equality.

  There is a polymorphic version of the exercise in the appendix, which you can
  do instead.

```coq
*)

Section ExerciseMonomorphic.

Definition bool_eq (x y : bool) : bool :=
  match x, y with
    | true, true => true
    | false, false => true
    | _, _ => false
  end.
Notation "x == y" := (bool_eq x y) (at level 60).

Definition reflect_bool_eq (x y : bool) :  x == y = true -> x = y.
  (intros; induction x, y; trivial; (discriminate H)).
Qed.

Definition compute_bool_eq (x : bool) :  x == x = true.
  induction x; simpl; trivial.
Qed.

(*
```

2. Given a regular expression X accepting a language L, compute the regular expression
   that accepts the [Brzozowski derivative](https://en.wikipedia.org/wiki/Brzozowski_derivative) of L,
   and prove the definition correct.

```coq
*)

Fixpoint derivative (re : regex bool) (t : bool) : regex bool
. Admitted.

Lemma derivative_good  re a x : x ∈ derivative re a <-> a :: x ∈ re.
Admitted.

(*
```

3. Prove that the matching function is correct. You can do this before solving
   part 1. or part 2.

```coq
*)
Fixpoint matches_b (re : regex bool) (x : list bool) : bool :=
  match x with
  | [] => ε_in re
  | t :: ts => matches_b (derivative re t) ts
  end.

Eval compute in matches_b (re_odd_length) [true;true;false;true;false].
Eval compute in matches_b (re_odd_length) [true;false;true;false].

Lemma matches_b_good (re : regex bool) (x : list bool) : matches_b re x = true <-> x ∈ re.
Admitted.

End ExerciseMonomorphic.
(*
```

4. (From SF)

Given:

```coq
*)
Fixpoint regex_list {T} (l : list T) :=
  match l with
  | [] => ε
  | x :: l' => « x » · (regex_list l')
  end.

(*
```

Show:

```coq
*)


Lemma reg_exp_of_list_spec {T} (x : list T) : x ∈ regex_list x.
Admitted.
(*
```


## Appendix

### Equivalence between `is_even` and `even_p`

First, define a new induction principle on the natural numbers,
and prove it correct.

```coq
*)

Fixpoint is_even_ind (P : nat -> Prop)
         (P0 : P 0)
         (P1 : P 1)
         (PSS : forall n, P n -> P (S (S n)))
         (n : nat) : P n.
  destruct n as [|[|n']]; try assumption.
  apply PSS.
  apply is_even_ind; assumption.
Qed.

Lemma is_even_correct : forall n,  is_even n = true <-> even_p n.
  split.

  (* -> *)
  induction n using is_even_ind.

  (* n = 0 *)
  intros.
  unfold even_p.
  exists 0.
  reflexivity.

  (* n = 1 *)
  intros.
  simpl in H. discriminate H.

  (* n = S (S n') *)
  simpl.
  unfold even_p in *.
  intros.
  specialize (IHn H); clear H.
  destruct IHn as [k Pk].
  exists (S k).
  simpl.
  (* obs: plus_n_Sm: forall n m : nat, S (n + m) = n + S m *)
  rewrite <- plus_n_Sm.
  congruence.

  (* <- *)
  unfold even_p.
  intros.
  destruct H as [k Pk].
  generalize n Pk; clear n Pk.
  induction k; intros n Hn; rewrite Hn; trivial.
  (* k = S k' *)
  simpl "+".
  rewrite <- plus_n_Sm.
  simpl is_even.
  apply IHk.
  reflexivity.
Qed.
(*
```

## Derivative for arbitrary types with decidable equality

Define a notion of decidable equality.

```coq
*)

Section RegexDec.

Class eqDec (T : Type) : Type :=
  mkEqDec {
    eqDec_f  : T -> T -> bool
  ; eqDec_pf : forall x y, eqDec_f x y = true <-> x = y
  }.

Notation "x == y" := (eqDec_f x y) (at level 60).

Definition reflectEq {T} {eq : eqDec T} {a b : T} : a == b = true -> a = b.
  intros.
  apply eqDec_pf.
  trivial.
Defined.

Definition computeEq {T} {eq : eqDec T} (a : T) : a == a = true.
  intros.
  apply eqDec_pf.
  trivial.
Defined.
(*
```

An instance for `nat`

```coq
*)
Fixpoint nat_eqDec_f (m n : nat) : bool :=
  match m, n with
  | 0, 0 => true
  | S n, S m => nat_eqDec_f n m
  | _, _ => false
  end.

Instance nat_eqDec : eqDec nat := { eqDec_f := nat_eqDec_f}.
Proof.
  (** x = 0 *)
  (** x = S _ *)
Admitted.

Fixpoint derivativeD {T} {eq : eqDec T} (t : T) (re : regex T) : regex T
. Admitted.


Fixpoint matchesD {T} {eq : eqDec T} (re : regex T) (x : list T) : bool
. Admitted.

Eval compute in matchesD ((«1» · «1» · «1») **) [1;1;1;1;1].

Eval compute in matchesD ((«1» · «1» · «1») **) [1;1;1;1;1;1].

End RegexDec.

End IndProp.

(*
```
*)
