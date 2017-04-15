(* https://www.ps.uni-saarland.de/autosubst/ *)
Require Import Autosubst.Autosubst.

Module STLC.

Inductive ty : Type :=
  | TBool : ty
  | TArrow : ty -> ty -> ty.

Inductive tm : Type :=
  | tvar : var -> tm
  | tapp : tm -> tm -> tm
  | tabs : ty -> {bind tm} -> tm
  | ttrue : tm
  | tfalse : tm
  | tif : tm -> tm -> tm -> tm.

Print _bind.

Instance Ids_tm : Ids tm. derive. Defined.
Instance Rename_tm : Rename tm. derive. Defined.
Instance Subst_tm : Subst tm. derive. Defined.
Instance SubstLemmas_tm : SubstLemmas tm. derive. Qed.

Lemma up_unfold (σ : var -> tm) : up σ = (ids 0 .: σ >> ren (+1)).
  asimpl.
  trivial.
Qed.

Lemma up_upren (ξ : var -> var) : up (ren ξ) = ren (upren ξ).
  autosubst.
Qed.

Lemma upren_unfold (xi : nat -> nat) :
               upren xi 0     = 0
  /\ forall n, upren xi (S n) = S (xi n).
  split. trivial. intro. trivial.
Qed.

Inductive value : tm -> Prop :=
  | v_abs : forall T t,
      value (tabs T t)
  | v_true :
      value ttrue
  | v_false :
      value tfalse.
Hint Constructors value.


Reserved Notation "t1 '⇒' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall T t12 v2,
         value v2 ->
         (tapp (tabs T t12) v2) ⇒ t12.[v2 .: ids]
  | ST_App1 : forall t1 t1' t2,
         t1 ⇒ t1' ->
         tapp t1 t2 ⇒ tapp t1' t2
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 ⇒ t2' ->
         tapp v1 t2 ⇒ tapp v1 t2'
  | ST_IfTrue : forall t1 t2,
      (tif ttrue t1 t2) ⇒ t1
  | ST_IfFalse : forall t1 t2,
      (tif tfalse t1 t2) ⇒ t2
  | ST_If : forall t1 t1' t2 t3,
      t1 ⇒ t1' ->
      (tif t1 t2 t3) ⇒ (tif t1' t2 t3)

where "t1 '⇒' t2" := (step t1 t2).


Hint Constructors step.

Inductive multi {X:Type} (R: X -> X -> Prop) : X -> X -> Prop :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

Notation multistep := (multi step).
Notation "t1 '⇒*' t2" := (multistep t1 t2) (at level 40).



Tactic Notation "print_goal" :=
  match goal with |- ?x => idtac x end.

(* Tactic Notation "normalize" := *)
(*   repeat (print_goal; eapply multi_step ; *)
(*             [ (eauto 10; fail) | (instantiate; simpl)]); *)
(*   apply multi_refl. *)

Tactic Notation "normalize" :=
  repeat (print_goal; eapply multi_step ;
          [ (eauto 10; fail) | (instantiate; simpl)]);
  apply multi_refl.


Definition context := var -> option ty.

Definition empty : context := fun x => None.

Reserved Notation "Gamma '⊢' t '∈' T" (at level 40).

Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Γ x T,
      Γ x = Some T ->
      Γ ⊢ tvar x ∈ T
  | T_Abs : forall Γ T11 T12 t12,
      (Some T11 .: Γ) ⊢ t12 ∈ T12 ->
      Γ ⊢ tabs T11 t12 ∈ TArrow T11 T12
  | T_App : forall T11 T12 Γ t1 t2,
      Γ ⊢ t1 ∈ TArrow T11 T12 ->
      Γ ⊢ t2 ∈ T11 ->
      Γ ⊢ tapp t1 t2 ∈ T12
  | T_True : forall Γ,
       Γ ⊢ ttrue ∈ TBool
  | T_False : forall Γ,
       Γ ⊢ tfalse ∈ TBool
  | T_If : forall t1 t2 t3 T Γ,
       Γ ⊢ t1 ∈ TBool ->
       Γ ⊢ t2 ∈ T ->
       Γ ⊢ t3 ∈ T ->
       Γ ⊢ tif t1 t2 t3 ∈ T

where "Γ '⊢' t '∈' T" := (has_type Γ t T).

Hint Constructors has_type.

End STLC.

Import STLC.

Definition has_types (Γ : context)(σ : var -> tm) (Δ : context)
  := forall x T,  Δ x = Some T -> Γ ⊢ σ x ∈ T.


Lemma upren_typing : forall Γ σ Δ T,
                     has_types Γ (ren σ) Δ ->
                     has_types (Some T .: Γ) (ren (upren σ)) (Some T .: Δ).
Proof.
  intros * H. intros x U p.
  destruct x; simpl; eauto.
  - inversion p as [H1]. assert (tt := H x U H1). inversion tt. eauto.
Qed.

Lemma ren_typing : forall Γ σ Δ T t,
                     has_type Δ t T ->
                     has_types Γ (ren σ) Δ ->
                    has_type Γ t.[ren σ] T.
Proof.
  intros * tt. generalize Γ σ. clear Γ σ.
  induction tt; intros; asimpl; eauto.
  constructor. apply IHtt. apply upren_typing. assumption.
Qed.


(* Exercises *)

Lemma up_typing : forall Γ σ Δ T,
                    has_types Γ σ Δ ->
                    has_types (Some T .: Γ) (up σ) (Some T .: Δ).
Admitted.

Lemma substitution_preserves_typing : forall Γ Δ σ t T,
     Δ ⊢ t ∈ T ->
     has_types Γ σ Δ ->
     Γ ⊢ (t.[σ]) ∈ T.
Admitted.

Theorem preservation t t' T (tt : empty ⊢ t ∈ T) :
     t ⇒ t' ->
     empty ⊢ t' ∈ T.
Admitted.

Lemma canonical_forms_bool : forall t,
  empty ⊢ t ∈ TBool ->
  value t ->
  (t = ttrue) \/ (t = tfalse).
Admitted.

Lemma canonical_forms_fun : forall t T1 T2,
  empty ⊢ t ∈ (TArrow T1 T2) ->
  value t ->
  exists u, t = tabs T1 u.
Admitted.

Theorem progress : forall t T,
     empty ⊢ t ∈ T ->
     value t \/ exists t', t ⇒ t'.
Admitted.


(* Extra exercise, add sums! If you proved them with enough automation
the substitution lemmas shouldn't need to be updated! *)
