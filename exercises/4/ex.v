(** Some examples with streams **)

(* Potentially infinite streams *)
CoInductive pstream A : Type :=
| pNil : pstream A
| pCons : A -> pstream A -> pstream A.

Arguments pNil {A}.
Arguments pCons {A} _ _.

(* From the "lecture", but with pnil case also *)
CoInductive pstream_eq {A} : pstream A -> pstream A -> Prop :=
| Pstream_eq_pnil :
    pstream_eq pNil pNil
| Pstream_eq_pcons : forall h t1 t2,
    pstream_eq t1 t2 -> pstream_eq (pCons h t1) (pCons h t2).

(* Implement the standard map function for potentially infinite streams *)
CoFixpoint pmap {A B} (f : A -> B) (s : pstream A) : pstream B. Admitted.

CoFixpoint pzeroes : pstream nat := pCons 0 pzeroes.
CoFixpoint pones : pstream nat := pCons 1 pones.
Definition pones' := pmap S pzeroes.

(* Reusing the name from CPDT, maybe unfold, destruct or something else would be a better name
   (as mentioned during the "lecture") *)
Definition pfrob {A} (s : pstream A) : pstream A :=
  match s with
  | pNil => pNil
  | pCons h t => pCons h t
  end.

Theorem pfrob_eq : forall {A} (s : pstream A), s = pfrob s.
Proof. destruct s; reflexivity. Qed.

(* Warm up: Same as from the "lecture", but here with potentially infinite stream instead *)
Theorem ones_eq : pstream_eq pones pones'.
Admitted.

(* Some problems stolen from http://www.labri.fr/perso/casteran/RecTutorial.pdf,
   section "7.2 About injection, discriminate, and inversion".
   Illustrates that these things work for co-inductive reasoning also.
   Warning: Note that the proofs are given in the PDF... *)
Theorem pNil_not_pCons : forall {A} (a : A) (s : pstream A),
    pNil <> pCons a s.
Admitted.

Inductive Finite {A} : pstream A -> Prop :=
| pNil_fin : Finite pNil
| pCons_fin : forall a s, Finite s -> Finite (pCons a s).

(* Provide a definition analogous to Finite *)
CoInductive Infinite {A} : pstream A -> Prop :=.

Theorem pNil_not_Infinite : forall {A:Type}, ~ Infinite (pNil : pstream A).
Admitted.

Theorem Finite_not_Infinite : forall {A} (s : pstream A), Finite s -> ~Infinite s.
Admitted.

Theorem Not_Finite_Infinite : forall {A} (s : pstream A), ~Finite s -> Infinite s.
Admitted.

(* And now we will need similar definitions for (always infinite) streams... *)
CoInductive stream A : Type :=
| Cons : A -> stream A -> stream A.
Arguments Cons {A} _ _.
Infix "::" := Cons.

CoInductive stream_eq {A} : stream A -> stream A -> Prop :=
| Stream_eq : forall h t1 t2,
    stream_eq t1 t2 -> stream_eq (h::t1) (h::t2).

(* Some standard functions on streams also *)
Definition head {A} (s : stream A) : A :=
  match s with
  | h::t => h
  end.

Definition tail {A} (s : stream A) : stream A :=
  match s with
  | h::t => t
  end.

(* repeatedly apply a function [n] times *)
Fixpoint iterate {A} (n : nat) (f : A -> A) (a : A) : A :=
  match n with
  | O => a
  | S n' => f (iterate n' f a)
  end.

Definition tail_n {A} (n : nat) (s : stream A) : stream A := iterate n tail s.

Definition head_n {A} (n : nat) (s : stream A) : A := head (tail_n n s).

(* For example, this holds *)
Theorem tail_n_plus_m :
  forall {A} (n m : nat) (s : stream A), tail_n n (tail_n m s) = tail_n (n + m) s.
Admitted.

(* Some more examples of inductive and co-inductive definitions,
   from the standard library *)
Inductive Exists {A} (s : stream A) (P : stream A -> Prop) : Prop :=
| Here : P s -> Exists s P
| Further : Exists (tail s) P -> Exists s P.

(* Provide a definition analogous to Exists *)
CoInductive ForAll {A} (s : stream A) (P : stream A -> Prop) : Prop :=.

(* A simple thm *)
Theorem ForAll_tail : forall {A} n (P : stream A -> Prop) (s : stream A),
  ForAll s P -> ForAll (tail_n n s) P.
Admitted.

(* But, of course, the analogous thm for Exists does not hold.
   I only found ugly/long proofs for this... *)
Theorem Exists_tail : ~(forall {A} n (P : stream A -> Prop) (s : stream A),
                       Exists s P -> Exists (tail_n n s) P).
Admitted.

(* Let's prove things about this class of streams %[%#[#an element repeated indefinitely#]#%]% instead of general thms *)
CoFixpoint repeat n : stream nat := n::(repeat n).

Theorem tail_n_zeroes : forall n, stream_eq (tail (repeat n)) (repeat n).
Admitted.

Theorem iterate_n_tail_repeat : forall n m, stream_eq (tail_n n (repeat m))
                                                      (repeat m).
Admitted.

(* Mutual recursion, nothing exciting *)
CoFixpoint flip1 : stream nat := 1::flip0
with       flip0 := 0::flip1.

Theorem tail_flip1_flip0_eq : stream_eq (tail flip1) flip0.
Admitted.

(** Infinite trees **)

(* T(h)ree exercises stolen from https://www.eecs.northwestern.edu/~robby/courses/395-495-2013-fall/HW6.v: *)

(* Define the coinductive types representing the following infinite data structures: *)

(* 1. Infinite binary trees *)

(* 2. Infinitely branching infinite trees (i.e. infinitely wide and infinitely deep) *)

(* 3. Finitely and infinitely branching infinite trees (i.e. finitely or infinitely wide and infinitely deep) *)

(** Back to streams again: Bisimilarity **)
Definition Bisimulation {A} (R : stream A -> stream A -> Prop) :=
    (forall s1 s2, R s1 s2 -> head s1 = head s2) /\
    (forall s1 s2, R s1 s2 -> R (tail s1) (tail s2)).

Theorem stream_eq_bisim : forall {A}, @Bisimulation A stream_eq /\ forall (R : stream A -> stream A -> Prop),
    Bisimulation R ->
    forall s1 s2, R s1 s2 -> stream_eq s1 s2.
Proof.
  (* Same proof as in the "lecture" *)
  split.
  split; destruct 1; trivial.
  intros R [H_head H_tail]. cofix. destruct s1, s2. intros.
  generalize (H_head _ _ H). intros. simpl in H0. rewrite H0. constructor.
  apply stream_eq_bisim.
  apply (H_tail _ _ H). Qed.

(* Same as above, but use stream_eq_bisim here *)
Theorem tail_flip1_flip0_eq' : stream_eq (tail flip1) flip0.
Admitted.

(* I suggest using stream_eq_bisim again *)
Theorem heads_iff_eq : forall {A} (s1 s2 : stream A),
    (forall (n : nat), head_n n s1 = head_n n s2) <-> stream_eq s1 s2.
Admitted.

(** Optional: Do the co-inductive big-step operational semantics for an imperative language optimization example from 5.3 in CPDT in SF-style instead of CPDT-style. **)

(** Even more exercise in case you're interested: In the coinduction chapter in Coq'Art there are some exercises. Consider especially 13.9 and 13.10, for some non-stream examples. **)
