# Course plan
Each session covers some content with the objective of achieving some goals.
At the end of each session, we set exercises about what we covered to be
presented in the next session. We also make changes to the plan based on
what we have learnt, and what we need to know in order to make progress
with the exercises.

Before each session, participants are expected to go through the material
on their own.

Note: SSReflect does not have a dedicated session. Interested participants
are encouraged to approach proofs using the technique, and show the other
participants how it works.

## Session 1

**Date:** TBD
**Place:** TBD

### Goals

  Getting the hang of the IDE.

  Proving simple properties about functional programs:

   - Commutativity of addition
   - Transitivity of append for lists
   - Transitivity of append for vectors
     (i.e. lists of a certain length)

### Contents

  - Coq as a functional language:
    - Finite types
    - Recursive types
    - Parameterized types
    - Function definitions

  - Prop vs. Type
    - Metatheory

  - Proving properties in Prop:
    - Logical connectives
    - Equality
    - Induction tactics

### Material

   Parts 1, 2 and 3 of
   https://team.inria.fr/marelle/en/coq-winter-school-2016/

### Exercises

  - Exercises from parts 1, 2 and 3 of the material.

## Session 2

### Goals

 - Prove the correctness of sorting algorithm on lists.

### Contents

  - Discuss exercises from previous session.
  - Theorem search
  - More on induction proofs. Strong induction.
  - Induction on trees.
  - Correctness of merge-sort.

### Material

 Parts 4 and 5 of
 https://team.inria.fr/marelle/en/coq-winter-school-2016/

### Exercises

 - Exercises from parts 4 and 5 of the material.

## Session 3

### Goals

 - Define and prove properties about relations using induction in Prop.

### Material

 - http://www.cis.upenn.edu/~bcpierce/sf/current/IndPrinciples.html#lab273
 - http://www.cis.upenn.edu/~bcpierce/sf/current/Rel.html

### Exercises

 - http://www.cis.upenn.edu/~bcpierce/sf/current/Rel.html

## Session 4

### Goals

  - Use tactics and relations to reason about sets of (imperative) programs,
    and sets of expressions.

### Material

    http://www.cis.upenn.edu/~bcpierce/sf/current/Imp.html

### Exercises

    http://www.cis.upenn.edu/~bcpierce/sf/current/Imp.html#lab339

## Session …

…

## Topics for future sessions

  In no particular order

  - Writing tactics.

    - Tactic Notation (easy)

      http://www.cis.upenn.edu/%7Ebcpierce/sf/current/Imp.html#lab309

    - Ltac (“not the most beautiful part of Coq”)

      http://adam.chlipala.net/cpdt/cpdt.pdf#chapter.14

  - Small step semantics.

    http://www.cis.upenn.edu/%7Ebcpierce/sf/current/Smallstep.html

  - Prove strong normalization for the simply-typed lambda calculus
    using logical relations.

    This could take more than one session. Hopefully Coq tactics will make
    proving all the lemmas about substitutions easier.

    http://www.cis.upenn.edu/~bcpierce/sf/current/Norm.html

  - Generic programming

    http://adam.chlipala.net/cpdt/cpdt.pdf#chapter.11

  - Proof by reflection

    http://adam.chlipala.net/cpdt/cpdt.pdf#chapter.15


  - Proofs about arithmetic

    - Integers, fibonacci numbers, division …

      Part 5 of https://team.inria.fr/marelle/en/coq-winter-school-2016/

    - The ring and omega tactics.

      http://www.cis.upenn.edu/%7Ebcpierce/sf/current/UseAuto.html#lab915

    - Classical results:

      - Irrationality of the square root of two.
      - Infinitude of primes.

      [reference needed]

  - Infinite data

    http://adam.chlipala.net/cpdt/cpdt.pdf#chapter.5
