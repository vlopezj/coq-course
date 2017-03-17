(*
Just some extra (optional) thms/stuff, feel free to add more.
*)

(* Thm references etc. are to "Introduction to Bisimulation and Coinduction". *)
Section LTS.

(* Stolen from coq-contribs/ccs on Github *)

Variable process action : Set.
Variable transition : process -> action -> process -> Prop.

(*
This is bisimilarity characterized as the largest bisimilation. I.e. thm 1.4.15,
but taken as a definition.

This definition (and its name) is from the above repo.
*)
CoInductive strong_eq : process -> process -> Prop :=
  str_eq : forall p q : process,
    (forall (a : action) (p' : process),
        transition p a p' ->
        exists q' : process, transition q a q' /\ strong_eq p' q') ->
    (forall (a : action) (q' : process),
        transition q a q' ->
        exists p' : process, transition p a p' /\ strong_eq p' q') ->
    strong_eq p q.

(*
Now we want a co-induction principle for this thing! This does not correspond directly to the definition in the book, because we do not want the /\ inside the forall ...
(This is not from the above repo.)
*)
Theorem strong_eq_coind : forall (R : process -> process -> Prop),
    (forall (p q : process),
    (forall (a : action) (p' : process),
        R p q -> transition p a p' ->
        exists q' : process, transition q a q' /\ R p' q')) ->
    (forall (p q : process),
    (forall (a : action) (q' : process),
        R p q -> transition q a q' ->
        exists p' : process, transition p a p' /\ R p' q')) ->
    forall (p q : process), R p q -> strong_eq p q.
Admitted.

Require Import Coq.Relations.Relation_Definitions.

(*
People asked about this during the "lecture", so why not prove it formally?
(Why isn't the first argument implicit for equiv? Strange design!)
Also, warning: The transitivity proof seemed long in the original file (but not necessarily complicated or unreasonably long).
*)
Theorem strong_eq_equiv' : equiv _ strong_eq.
Admitted.

(* 2.1.1 Finite traces and ω-traces on processes *)

(* Finite traces *)
Inductive ft : process -> Prop :=
| ft_stopped p : (forall (a : action), ~(exists (p' : process), transition p a p')) -> ft p
| ft_step p : forall (a : action) (p' : process), transition p a p' -> ft p' -> ft p.

Theorem strong_eq_ft : forall (p q : process),
    ft p -> strong_eq p q -> ft q.
Admitted.

(* ω-traces *)
CoInductive wt (a : action) : process -> Prop :=
| wt_step p : forall (p' : process), transition p a p' -> wt a p' -> wt a p.

(* Co-induction principle for ω-traces *)
Theorem wt_coind : forall (a : action) (R : process -> Prop),
    (forall (p : process), R p -> exists (p' : process), R p' /\ transition p a p') ->
    (forall (p : process), R p -> wt a p).
Admitted.

Theorem strong_eq_wt : forall (a : action) (p q : process),
    wt a p -> strong_eq p q -> wt a q.
Admitted.

End LTS.

(* Shows that P1 and Q1 from fig. 1.2 (in the book), i.e. one of the examples from the "lecture", are bisimilar *)
Inductive ex1_processes :=
  P1 | P2 | Q1 | Q2 | Q3.

Inductive ex1_actions :=
  a | b.

Inductive ex1_trans : ex1_processes -> ex1_actions -> ex1_processes -> Prop :=
(* Left system *)
| P1P2 : ex1_trans P1 a P2
| P2P1 : ex1_trans P2 b P1
(* Right system *)
| Q1Q2 : ex1_trans Q1 a Q2
| Q2Q3 : ex1_trans Q2 b Q3
| Q3Q2 : ex1_trans Q3 a Q2.

Inductive ex1_R : ex1_processes -> ex1_processes -> Prop :=
| P1Q1_R : ex1_R P1 Q1
| P1Q3_R : ex1_R P1 Q3
| P2Q2_R : ex1_R P2 Q2.

Theorem P1_Q1_bisim : strong_eq _ _ ex1_trans P1 Q1.
Proof.
  apply (strong_eq_coind _ _ _ ex1_R); intros.
  * destruct p; inversion H; inversion H0; subst.
   + (* R (P1, Q1) *) exists Q2. split; constructor.
   + (* R (P1, Q3) *) exists Q2. split; constructor.
   + (* R (P2, Q2) *) exists Q3. split; constructor.
  * destruct q; inversion H; inversion H0; subst.
   + (* R (P1, Q1) *) exists P2. split; constructor.
   + (* R (P2, Q2) *) exists P1. split; constructor.
   + (* R (P1, Q3) *) exists P2. split; constructor.
  * constructor. Qed.
