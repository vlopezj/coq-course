Load "ex6.v".

(** * Norm: Normalization of STLC *)

(* Based on a chapter written and maintained by Andrew Tolmach *)
(* I recommend not looking at the chapter in SF, as it gives the whole
   proof away. *)

Definition halts (t:tm) : Prop :=  exists t', t ⇒* t' /\ value t'.

(* Exercise 1: Define R such that these properties hold:
   Check Chapter 12 of Types and Programming Languages (Pierce)
*)
Definition R (T:ty) (t:tm) : Prop. Admitted.

Lemma R_halts : forall {T} {t}, R T t -> halts t.
Admitted.

Lemma R_typable_empty : forall {T} {t}, R T t -> has_type empty t T.
Admitted.

Lemma step_preserves_R : forall T t t', (t ⇒ t') -> R T t -> R T t'.
Admitted.

Lemma multistep_preserves_R : forall T t t', (t ⇒* t') -> R T t -> R T t'.
Admitted.

(* Exercise 2: Prove that R holds for well-typed, closed terms *)
Lemma subst_R : forall Γ t T γ,
    has_types empty γ Γ ->
    has_type Γ t T ->
    R T (t.[γ]).
Admitted.

(* Exercise 3: Using R_halts and subst_R, prove that the STλC is
   strongly normalizing. 
   You can do this even before doing Exercises 1 and 2.
 *)
Lemma strong_normalization (t : tm) (T : ty) : empty ⊢ t ∈ T -> halts t.
Admitted.

(* BONUS: Do the exercise for the calculus extended with sums. *)