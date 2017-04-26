Load "ex6.v".

(** * Norm: Normalization of STLC *)

(* Based on a chapter written and maintained by Andrew Tolmach *)
(* I recommend not looking at the chapter in SF, as it gives the whole
   proof away. *)

Definition halts (t:tm) : Prop :=  exists t', t ⇒* t' /\ value t'.

<<<<<<< HEAD
(* The logical relation we will use.
   Check Chapter 12 of Types and Programming Languages (Pierce)
=======
(* Exercise 1: Define R such that these properties hold:
   Check chapter 12 of Types and Programming Languages (Pierce)
>>>>>>> ecbf98bfee50b6060e799ed675047616ada3bcc8
*)
Fixpoint R (T:ty) (t:tm) : Prop :=
    halts t /\ empty ⊢ t ∈ T /\
    match T with
      TBool         => True
    | TArrow T1 T2  => forall u, R T1 u -> R T2 (tapp t u)
    end.

Lemma R_halts : forall {T} {t}, R T t -> halts t.
  intros.
  induction T.
  all: simpl in H; tauto.
Defined.

Lemma R_typable_empty : forall {T} {t}, R T t -> has_type empty t T.
  intros.
  induction T.
  all: simpl in H; tauto.
Defined.

(* Exercise 1 (warm up): Show that the reduction relation is deterministic.
   This is a very strong property; one may want to do the proof with a non-deterministic
   reduction relation. *)
Lemma red_deterministic : forall t a b  (r : t ⇒ a) (s :  t ⇒ b), a = b.
Admitted.

(* Exercise 2: Show that R is preserved by the reduction relation, back and forth: *)
Lemma step_preserves_R : forall T t t', (t ⇒ t') -> R T t -> R T t'.
Admitted.

Lemma step_preserves_R' : forall T t t', empty ⊢ t ∈ T ->  (t ⇒ t') -> R T t' -> R T t.
Admitted.

(* Exercise 3: *)

(* We define the analogous of `R` for substitutions: *)
Definition Rsubst Γ σ : Prop := has_types empty σ Γ /\ forall x T, Γ x = Some T -> R T (σ x).

(* Show that R holds for all closed terms. 
   For the induction to work, we need to consider a stronger property:  *)
Lemma subst_R : forall Γ t T σ,
    Rsubst Γ σ ->
    Γ ⊢ t ∈ T ->
    R T (t.[σ]).
Admitted.

(* Then, proving closed_R is easy. *)
Lemma closed_R : forall t T,  empty ⊢ t ∈ T -> R T t.
Admitted.

<<<<<<< HEAD
(* Exercise 4: Prove that the STλC is strongly normalizing.
   You can do this exercise even before doing any of the earlier exercises.
=======
(* Exercise 3: Using R_halts and subst_R, prove that the STλC is
   strongly normalizing.
   You can do this even before doing Exercises 1 and 2.
>>>>>>> ecbf98bfee50b6060e799ed675047616ada3bcc8
 *)
Lemma strong_normalization (t : tm) (T : ty) : empty ⊢ t ∈ T -> halts t.
Admitted.

(* BONUS: Extend the logical relation and the rest of the proof to work with sum types. *)