(** Here is an inductively defined proposition describing whether a
    natural number is even. *)
Inductive even : nat -> Prop :=
| even_O : even O
| even_SS : forall n, even n -> even (S (S n)).

Lemma even_4 : even 4.
Proof.
  apply even_SS.
  Show Proof.
  apply even_SS.
  Show Proof.
  apply even_O.
Qed.

Print even_4.

(** Provide a proof term (not a script) for the following propositions. *)
Definition even_8 : even 8
. (* Proof term here *) Admitted.

Definition even_4plusn : forall n, even n -> even (4 + n)
. (* Proof term here *) Admitted.

(* Recall the definition of the inductive types corresponding to
   logical connectives. *)
Print and.

Print or.

(* For the following propositions, provide a proof term. Do not use
   the proof mode and tactics. *)

Definition and_comm : forall P Q, P /\ Q -> Q /\ P
. (* Proof term here *) Admitted.

Definition or_comm : forall P Q, P \/ Q -> Q \/ P
. (* Proof term here *) Admitted.

(* The type of false proposition is the empty type, meaning that there
   is no constructor to build such a proposition. *)
Print False.

(* Use patter-matching over this empty type to define the principle of
   explosion. *)
Definition ex_falso : forall P, False -> P
. (* Proof term here *) Admitted.

(* Inductive proofs correspond to recursive functions. *)

(* Let us first prove the base case and inductive step separately. *)
Definition base_case : 0 = 0 + 0
. (* Proof term here *) Admitted.

(* This proof can be difficult to write, as often with equality-based
   proofs.  Hint: It can be done using only [eq_rect]. *)
Definition inductive_step : forall n, n = n + 0 -> S n = S n + 0
. (* Proof term here *) Admitted.

(** Combine the two lemmas into an inductive proof/recursive
    function. Use [fix] to define the recursion (see presentation), or
    alternatively replace <<Definition>> by <<Fixpoint>>. *)
Definition add_0 : forall n, n = n + 0
. (* Proof term here *) Admitted.

(** Use tactics to define addition over natural numbers, instead of
    writing the term directly. Use the keyword <<Defined>> instead of
    the usual <<Qed>> at the end of your script: This ensures that the
    proof term that you created is transparent (not opaque as proofs
    usually are). *)
Definition add' : nat -> nat -> nat.
Admitted.

(* If your definition is correct, the following lemmas should be
   proved as given. *)
Example ex1 : add' 0 3 = 3.
Proof.
  reflexivity.
Qed.

Example ex2 : add' 2 4 = 6.
Proof.
  reflexivity.
Qed.

Example ex3 : add' 3 8 = 11.
Proof.
  reflexivity.
Qed.
