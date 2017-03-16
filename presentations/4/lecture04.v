(** Certified Programming with Dependent Types by Adam Chlipala **)

(*
Biggest difference: Different proof style, prefer automation over manual sequencing of tactics.

Not confined to an "advanced chapter" in the end, used from the beginning.

In Part I (i.e., what I've read), only the crush tactic is mentioned.
Like a super auto/intuition/etc.:
*)

(* Plus is commutative *)

(* SF way *)
Theorem plus_comm : forall n m, n + m = m + n.
Proof.
  induction n; intros; simpl.
  * rewrite <- plus_n_O. reflexivity.
  * rewrite IHn. rewrite <- plus_n_Sm. reflexivity. Qed.

(* CPDT way, special configuration needed to be able to load this *)
Require Import Cpdt.CpdtTactics.

Theorem plus_comm' : forall n m, n + m = m + n.
Proof.
  induction n; crush. Qed.

(*
(In this particular case intuition would have been enough...

Note from "lecture": Note that this simply uses PeanoNat.Nat.add_comm from the standard library...
*)
Theorem plus_comm'' : forall n m, n + m = m + n.
Proof.
  induction n; intuition. Qed.
(* .) *)

(* Larger example, from CPDT 4.5 *)
Inductive even : nat -> Prop :=
| EvenO : even O
| EvenSS : forall n, even n -> even (S (S n)).

(* Andreas' manual proof *)
Lemma even_contra : forall n, even (S (n + n)) -> False.
Proof.
  intro. remember (S (n + n)). intros. generalize dependent n. induction H; intros.
  * discriminate Heqn0.
  * destruct n0; inversion Heqn0.
    eapply IHeven. rewrite <- plus_n_Sm in H1. eapply H1. Qed.

(*
CPDT, split into two for useful induction hypo.
Note that we do not mention any hypothesis names here!
*)
Lemma even_contra_help' : forall n', even n' -> forall n, n' = S (n + n) -> False.
Proof.
  Hint Rewrite <- plus_n_Sm.
  induction 1; crush;
    match goal with
    (* Note: destruct N no needed? Copy-paste from book. *)
    | [ H : S ?N = ?N0 + ?N0 |- _ ] => destruct N; destruct N0
    end; crush.
Qed.

Theorem even_contra' : forall n, even (S (n + n)) -> False.
  intros; eapply even_contra_help'; eauto.
Qed.

(* Mix of styles? *)
Lemma even_contra'' : forall n, even (S (n + n)) -> False.
Proof.
  intro. remember (S (n + n)). intros. generalize dependent n.
  Hint Rewrite <- plus_n_Sm.
  induction H; crush.
  match goal with
  | [ H : S ?N = ?N0 + ?N0 |- _ ] => destruct N0
  end; crush. Qed.

(*
Is this helpful in general? Will crush solve all our proof problems?

No, we are dealing with undecidable problems. Cannot expect an algorithm (heuristic) to be good in general.

So crush is not a universal answer, instead CPDT tells us how to develop custom Ltac decision procedures for the set of undecidable problems we have in our particular domain.

Relevant section: 1.6.2.
*)

(*
In general, a more "advanced" book than SF. Talks about dependent types, more advanced topics, etc.
*)

(*
Just another observation:

Curry-Howard: Proofs and programs are the same thing.
Coq: Programs and proofs separated (to some extent ...): Set and Prop.
Andreas: ???

"There is a certain aesthetic appeal to this point of view, but I want to argue that it is best to treat Curry-Howard very loosely in practical proving. There are Coq-specific reasons for preferring the distinction, involving efficient compilation and avoidance of paradoxes in the presence of classical math, but I will argue that there is a more general principle that should lead us to avoid conflating programming and proving." (p. 68)

"The essence of the argument is roughly this:
to an engineer, not all functions of type A -> B are created equal,
but all proofs of a proposition P -> Q are."

I.e., proof irrelevance.

"Most of this book is organized around that distinction, describing how to program, by applying standard functional programming techniques in the presence of dependent types; and how to prove, by writing custom Ltac decision procedures." (from intro I think)

"Agda does not have an analogous Prop-Set distinction at the moment." -- http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Main.AgdaVsCoq

Relevant sections: "4.2 What Does It Mean to Be Constructive?" and others (spread out).
*)

(** Infinite data and proofs **)

(*
The hello world of infinite data: infinite lists (aka streams)

Simple in e.g. lazy mainstream languages such as Haskell...

> let zeroes = 0 : zeroes
> take 50 zeroes
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
> take 100 zeroes
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]

But also...

> zeroes
*Non-terminating computation*

Can't have that is Coq (Curry-Howard etc.). What happens with the same definition in Coq?
*)

Fail Definition zeroes := cons 0 zeroes.
Fail Fixpoint zeroes := cons 1 zeroes.
Fail Fixpoint zeroes (x:nat) := cons 0 (zeroes x).
Fail Fixpoint zeroes (x:nat) := cons 0 (zeroes 0).

(* But easy with coinductive stream instead of inductive list *)
CoInductive stream A : Type :=
| Cons : A -> stream A -> stream A.
Arguments Cons {A} _ _.
Infix "::" := Cons.

(* No nil, so can in fact only build infinite lists *)
CoFixpoint zeroes : stream nat := 0::zeroes.
Print zeroes.
Compute zeroes.

CoFixpoint incstream_n n : stream nat := n::incstream_n (S n).
Definition incstream := incstream_n 0.
Print incstream.
Compute incstream.

(*
Fixpoint function for coinductive stream!
We only build a finite list here. So data and codata do not live in separate worlds that never interact.
*)
Fixpoint take {A} (n : nat) (s : stream A) : list A :=
  match n, s with
  | O, _ => nil
  | S n', h::t => cons h (take n' t)
  end.

Compute (take 20 zeroes).
Compute (take 30 incstream).

(*
But of course, the usual recursion restrictions applies here also:
*)
Fail Fixpoint length {A} (s : stream A) : nat :=
  match s with
  | h::t => S (length t)
  end.

(*
And here is a cofixpoint ("corecursive") function.
Here we build an infinite list.
*)
CoFixpoint map {A B} (f : A -> B) (s : stream A) : stream B :=
  match s with
  | h::t => (f h)::(map f t)
  end.

Compute (take 20 (map (fun x => x * x) incstream)).

(*
Ok, but what about termination?

Cannot expect termination with infinite data ...

Instead Coq demands "productivity".

But, as termination (halting problem), productivity is undecidable.

Instead approximated, as termination:

For termination, recursive calls must be on structurally smaller elements than input, as seen above. (Something more?) This is a syntactic criterion.

Productivity is guaranteed by (the also syntactic criterion) guardedness in Coq.

For example, this is not allowed:
*)

Fail CoFixpoint loop : stream nat := loop.

(*
The guardedness criterion is satisfied when every corecursive call is

 * a direct argument to a constructor of the coinductive data type we are building,
 * and nested only inside of other constructor calls or fun or match expressions.

("The guard condition ensures that every corecursive call produces at least one constructor of the co-inductive type being considered. Thus, a pattern matching operation on data in a co-inductive type requires a finite number of co-recursive calls to decide the branch to follow." -- Coq'Art, p. 353)

E.g.:
*)

CoFixpoint zip {A} (s1 s2 : stream A) : stream (A * A) :=
  match s1, s2 with
  (* Not using :: syntax here to be extra clear.
     Note that the call to zip is inside Cons. *)
  | h1::t1, h2::t2 => Cons (h1, h2) (zip t1 t2)
  end.

(* (Works as expected: *)
Compute (take 20 (zip zeroes incstream)).
(* ) *)

(*
(From 13.3.4.2 Recursive Calls in a Non-constructor Context from Coq'Art, but modified.)

Must be a _direct_ argument, i.e. this is not allowed:
*)
Fail CoFixpoint F (s : stream nat) : stream nat :=
  match s with
  | h::t => h::(F (F t))
  end.

(* Fixpoint version of this not allowed either, one can note: *)
Fail Fixpoint F (l : list nat) :=
  match l with
  | nil => nil
  | cons h t => cons h (F (F t))
  end.

(* Bla bla bla codata. What about proofs? *)

CoFixpoint ones : stream nat := Cons 1 ones.
Definition ones' := map S zeroes.

Compute (take 20 ones).
Compute (take 20 ones').

Theorem ones_eq : ones = ones'.
(*
:(, can only prove "thing = other thing" with finite arguments.
"=" is an inductive definition.
 *)
Print eq.
Abort.

(* But, e.g., the following works perfectly fine: *)
Theorem ones_eq_take : forall n, take n ones = take n ones'.
Proof.
  induction n.
  * reflexivity.
  * simpl.
    (* Just to see what is going on: *) fold ones'.
    rewrite IHn. reflexivity. Qed.

(* The following coinductive definition to rescue for the infinite case: *)

CoInductive stream_eq {A} : stream A -> stream A -> Prop :=
| Stream_eq : forall h t1 t2,
    stream_eq t1 t2 -> stream_eq (h::t1) (h::t2).

Check eq

(*
This is sometimes called "bisimilar" instead of stream_eq, but I don't see the direct connection to bisimilarity. But will prove a connection to something similar below.

As a comparison, consider the following definition for finite lists:
*)

Inductive list_eq {A} : list A -> list A -> Prop :=
| List_nil_eq :
    list_eq nil nil
| List_cons_eq : forall h t1 t2,
    list_eq t1 t2 -> list_eq (h::t1) (h::t2).

Theorem list_eq_eq_eq : forall {A} (l1 l2 : list A), list_eq l1 l2 <-> l1 = l2.
Proof.
  split.
  * induction 1; crush.
  * intro. rewrite H.
    (* ugly ... should be separate thm: *)
    clear H. induction l2; constructor; assumption. Qed.

(* But, back to the actual/important thm: *)

Theorem ones_eq : stream_eq ones ones'.
Proof.
  (* New tactic: *) cofix.
  assumption.
  (* Qed. *)

  (*
  If this was accepted, we could prove any coinduction thm in one step...

  The function we built does not satisfy the guardedness criterion:
  *)
  Show Proof.
  Undo.

  (* This also breaks automation: *)
  auto.
  Show Proof.
  (* Side note: Given Adam's preferred proof-style, this is very bad, and he has suggestions how to fix this. *)
  Undo.

  simpl.
  (* Nothing happened? *)
  Abort.

(*
Cofixpoints only reduce if it's clear how the result will be used. (For usual fixpoints, the arguments are the important thing.)

Cofixpoints will only reduce when they are the argument to match expression.

(Probably has something to do with avoid "unproductive" infinite loops.)

The following definition and thm allow us to introduce matches in proofs:
*)

(* Coq'Art calls this decompose, this name is from CPDT *)
Definition frob {A} (s : stream A) : stream A :=
  match s with
  | h::t => h::t
  end.

Theorem frob_eq : forall {A} (s : stream A), s = frob s.
Proof. destruct s; reflexivity. Qed.

(* Let's try with ones_eq again: *)
Theorem ones_eq : stream_eq ones ones'.
Proof.
  cofix.
  rewrite frob_eq.
  (* Just to illustrate: *) unfold frob.
  rewrite (frob_eq ones).
  simpl.
  constructor. (* apply Stream_eq. *)
  assumption.
  Show Proof. Qed.

(*
So now we have seen infinite proofs in Coq.

That was much more scary than induction :(

Let's look at ones_eq_take again:
*)

Theorem ones_eq_take' : forall n, take n ones = take n ones'.
Proof.
  (* Proof from above. *)
  induction n.
  * reflexivity.
  * simpl. rewrite IHn. reflexivity.

  (* We did this without thinking about only using structurally smaller arguments in recursive calls *)
  Restart.

  fix H 1.
  auto.
  Show Proof.
  (* Qed. *)
  Abort.

(*
Great success: We managed to make induction as scary as coinduction!

From the manual: [fix] is a primitive tactic to start a proof by induction. In general, it is easier to rely on higher-level induction tactics such as the ones described in Section 8.5.2.

Can we do the same for the coinductive case? I.e., can we find coinduction principles (rather than the usual induction principles)?

They are not auto-generated as the inductive case, but can build them manually.

This takes us to bisimulation, following rules backwards etc.

Recall, induction is "forward":
*)

Print nat_ind.
Print list_ind.

(* From session 2 *)
Inductive regex (T : Type) : Type :=
  | empty   : regex T
  | ε       : regex T
  | char    : T -> regex T
  | concat  : regex T -> regex T -> regex T
  | union   : regex T -> regex T -> regex T
  | star    : regex T -> regex T.

Print regex_ind.

(* Bisimulation(?) for streams *)
Definition head {A} (s : stream A) : A :=
  match s with
  | h::t => h
  end.

Definition tail {A} (s : stream A) : stream A :=
  match s with
  | h::t => t
  end.

Theorem stream_eq_bisim : forall {A} (R : stream A -> stream A -> Prop),
    (forall s1 s2, R s1 s2 -> head s1 = head s2) ->
    (forall s1 s2, R s1 s2 -> R (tail s1) (tail s2)) ->
    forall s1 s2, R s1 s2 -> stream_eq s1 s2.
Proof.
  intros A R H_head H_tail. cofix. destruct s1, s2. intros.
  generalize (H_head _ _ H). intros. simpl in H0. rewrite H0. constructor.
  apply stream_eq_bisim.
  apply (H_tail _ _ H). Qed.

Theorem ones_eq_ones' : stream_eq ones ones'.
Proof.
  (* Easy to automate more, but want to be able to follow the proof *)
  apply (stream_eq_bisim (fun s1 s2 => s1 = ones /\ s2 = ones')); intros.
  * destruct H. subst. reflexivity.
  * destruct H. subst. split.
   + reflexivity.
   + reflexivity.
  * split; reflexivity. Qed.

(*
Notice that we didn't use any frobs here. Also, this is easier to automate I think.

This should hopefully be enough to apply coinduction, e.g.:

 * Coinductive semantics (in CPDT)
 * Linear temporal logic (LTL) semantics (in Coq'Art) -- there we have infinite executions etc.
 * LTSes in Coq? (E.g., formalize things from the coinduction book.) (There's something about automata in Coq'Art.)
 * I saw something about coinduction and Turing machines -- formally verified computability theory?
 * More coinduction principles and automation
 * ...
*)
