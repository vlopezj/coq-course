# Course plan
Each session covers some content with the objective of achieving some goals.
At the end of each session, we set exercises about what we covered to be
presented in the next session. We also make changes to the plan based on
what we have learnt, and what we need to know in order to make progress
with the exercises.

Before each session, participants are expected to go through the material
on their own.

## [Session 1](notes/session01.md) — Kickoff meeting

**Date:** Thu 2nd Feb 2017, 3:15pm — 5pm
**Place:** Room 6128, EDIT Building, Johanneberg

We will discuss what each of us wants to get out of the course, and update the course plan accordingly.
If we have the time and the inclination, we will get started with the Coq IDE/Proof General and do some basic examples.

### Before the session

- Look at the [session notes](notes/session01.md).
  Add questions you want to discuss, or comment on the existing ones.
  We will discuss these questions during the meeting.

- Install Coq IDE/Proof General in your machine. Take a look at the [tutorial](https://coq.inria.fr/distrib/V8.6/files/Tutorial.pdf).

### Goals

- **Plan the course.** See the [session notes](notes/session01.md) for questions to address.

- If there's time…

  - Get the hang of the IDE.
  - Prove simple properties about functional programs:
    - Commutativity of addition
    - Associativity of append for lists
    - ~~Associativity of append for vectors (i.e. lists of a certain length)~~

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

   Tutorial:
   https://coq.inria.fr/distrib/V8.6/files/Tutorial.pdf

   Cheat sheet:
   http://andrej.com/coq/cheatsheet.pdf

   Survival kit:
   https://coq.inria.fr/files/coq-itp-2015/CoqSurvivalKit.pdf

   Parts 1, 2 and 3 of
   https://team.inria.fr/marelle/en/coq-winter-school-2016/

   The tutorial, part 1, 2 and 3, and SF up to (and including) Logic minus Poly largely overlaps.

### Exercises

  - Exercises from parts [1](exercises/ex1.v), [2](exercises/ex2.v) and [3](exercises/ex3.v) of the material.

## [Session 2](notes/session02.md)

### Contents

* Inductive propositions.
* Tactics for effective induction on inductive propositions.

### Material

* Software Foundations, [Inductive Propositions](https://www.cis.upenn.edu/~bcpierce/sf/current/IndProp.html).

### Exercises

Exercises based on the material.

* [exercises/exindprop.v](exercises/exindprop.v).

## Session 3

### Goals

 - Define and prove properties about relations using induction in Prop.
 - Something more, e.g. equality?

### Material

 - IndProp (+ ProofObjects) + IndPrinciples + Rel from SF

 - Equality in Coq

   For the first meeting we said that one could prove "associativity
   of append for vectors (i.e. lists of a certain length)" as a
   warm-up exercise. This is, however, much more difficult than the
   analogous theorem for lists because we get different types on the
   two sides of the equality. (Daniel managed to prove this using JMeq.)

   - http://adam.chlipala.net/cpdt/html/Equality.html
   - http://sf.snu.ac.kr/gil.hur/publications/heq.pdf
   - http://web.mit.edu/jgross/Public/2014-splash/equality/exercises.v

### Exercises

 - TBD

## Session 4

### Goals

  - Use tactics and relations to reason about sets of imperative programs,
    and sets of expressions.
  - Program logics for imperative programs (Hoare logic)

### Material

  - Maps (needed for the rest) + Imp + Equiv + Hoare + Hoare2 from SF (this is a lot of material)
  - https://github.com/achlipala/frap?

### Exercises

  - TBD

## Session 5

Ideas: Either material from session 4 if it's too much for one session. Or some parts of the lambda and type stuff from SF.

Some more ideas:

  - Small step semantics

    http://www.cis.upenn.edu/%7Ebcpierce/sf/current/Smallstep.html

  - Prove strong normalization for the simply-typed lambda calculus
    using logical relations

    This could take more than one session. Hopefully Coq tactics will make
    proving all the lemmas about substitutions easier.

    http://www.cis.upenn.edu/~bcpierce/sf/current/Norm.html

## Session 6

  - Proof by reflection and SSReflect

    - http://adam.chlipala.net/cpdt/cpdt.pdf#chapter.15
    - https://team.inria.fr/marelle/en/advanced-coq-winter-school-2016/ -- difficult to follow (according to Andreas)
    - https://github.com/math-comp/wiki/wiki/tutorial-itp2016
    - https://math-comp.github.io/mcb/
    - http://ilyasergey.net/pnp/

  - Writing tactics (proof automation)

    - Tactic Notation (easy)

      http://www.cis.upenn.edu/%7Ebcpierce/sf/current/Imp.html#lab309

    - Ltac (“not the most beautiful part of Coq”)

      http://adam.chlipala.net/cpdt/cpdt.pdf#chapter.14

      [Nisse](http://www.cse.chalmers.se/~nad/) recommended going deep into Ltac with Chlipala's book if we have the time.
      (Which we should, getting the proof of normalization of the simply-typed
      lambda calculus using logical relations should be easy).

    - [Mtac](http://plv.mpi-sws.org/mtac/) (typed tactic programming)

## Session …

Suggestions are welcome.

In no particular order:

  - Infinite data, coinduction, codata and data

    http://adam.chlipala.net/cpdt/cpdt.pdf#chapter.5

  - Generic programming

    http://adam.chlipala.net/cpdt/cpdt.pdf#chapter.11

  - Proofs about arithmetic

    Classical results:

    - Irrationality of the square root of two ([Cocorico!](https://coq.inria.fr/cocorico/SquareRootTwo)).
    - Infinitude of primes ([MCB](https://math-comp.github.io/mcb/book.pdf#page=112) [proof](https://math-comp.github.io/mcb/ch4.html)).

  - Program extraction

    - Covered in one chapter in SF, but more info in Extraction in VFA
    - Examples with simple programs?
    - Efficiency of extracted programs?
    - [Coq.io](http://coq.io)
    - Any formal guarantees on extracted programs or are they simply pretty-printed?

  - Large proof projects

    - CompCert
    - [Formalized mathematics](https://coq.inria.fr/cocorico/List%20of%20Coq%20Math%20Projects) (four color theorem often mentioned)

  - Theoretical foundations

    - Something about CIC
    - `Set` vs. `Prop` vs. `Type`
    - Proof irrelevance, impredicativity, ...

  - More from CPDT?

  - Abus de notation: Type classes/Canonical structures/Coercions/Unification hints

    - Mooooooonads?

  - Matthieu Sozeau's program tactics.
