# Course plan

_No longer maintained, see [session notes](notes) instead._

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
    - Function definitions (primitive recursion and structural recursion)

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

  - Exercises from parts [1](exercises/1/ex1.v), [2](exercises/1/ex2.v) and [3](exercises/1/ex3.v) of the material.

## [Session 2](notes/session02.md)

### Contents

* Inductive propositions.
* Tactics for effective induction on inductive propositions.

### Material

* Software Foundations, [Inductive Propositions](https://www.cis.upenn.edu/~bcpierce/sf/current/IndProp.html).

### Exercises

Exercises based on the material.

* [exercises/2/exindprop.v](exercises/2/exindprop.v).

## Session ...
