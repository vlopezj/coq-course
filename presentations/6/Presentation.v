(* https://www.ps.uni-saarland.de/autosubst/,
   only branch coq86-devel builds with the latest version of Coq. *)
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

(* λ (x : Bool). x *)
Notation idB :=
  (tabs TBool (tvar 0)).

(* λ (x : Bool → Bool). x *)
Notation idBB :=
  (tabs (TArrow TBool TBool) (tvar 0)).

(* λ (x : (Bool → Bool) → Bool → Bool). x *)
Notation idBBBB :=
  (tabs (TArrow (TArrow TBool TBool)
                      (TArrow TBool TBool))
        (tvar 0)).

(* λ (x y : Bool). y *)
Notation k := (tabs TBool (tabs TBool (tvar 1))).

(* λ (x : Bool). if x then false else true *)
Notation notB := (tabs TBool (tif (tvar 0) tfalse ttrue)).

Instance Ids_tm : Ids tm. derive. Defined.
Instance Rename_tm : Rename tm. derive. Defined.
Instance Subst_tm : Subst tm. derive. Defined.
Instance SubstLemmas_tm : SubstLemmas tm. derive. Qed.

(* var -> tm *)
Print Ids_tm.


Compute (tapp (tvar 0) (tvar 1)).[idBB .: idB .: ids].

Print scons.
(* 
(t .: σ) 0     = t
(t .: σ) (S n) = σ n
*)

(*
Print Subst_tm.
Subst_tm = 
fix dummy (sigma : var -> tm) (s : tm) {struct s} : tm :=
  match s as t return (annot tm t) with
  | tvar v => sigma v
  | tapp s1 s2 => tapp s1.[sigma] s2.[sigma]
  | tabs T t => tabs T t.[up sigma]
  | ttrue => ttrue
  | tfalse => tfalse
  | tif s1 s2 s3 => tif s1.[sigma] s2.[sigma] s3.[sigma]
  end
     : Subst tm
 *)


Lemma up_unfold (σ : var -> tm) : up σ = (ids 0 .: σ >> ren (+1)).
  asimpl.
  trivial.
Qed.

Print up.
Print Rename_tm.

Lemma demo (σ : var -> tm) (u t : tm) : u.[up σ].[t.[σ] .: ids] = u.[t .: ids].[σ].
  (* asimpl. trivial. *)
  autosubst.
Qed.


Lemma rewriting_rules (σ τ θ : var -> tm) (s : tm) : 
     ids >> σ = σ
  /\ σ >> ids = σ
  /\ (ids 0).[s .: σ] = s
  /\ ren (+1) >> (s .: σ) = σ
  /\ (σ >> τ) >> θ = σ >> (τ >> θ)
  /\ (s .: σ) >> τ = s.[τ] .: σ >> τ
  /\ s.[ids] = s
  /\ s.[σ].[τ] = s.[σ >> τ]
  /\ (ids 0).[σ] .: (ren (+1) >> σ) = σ
  /\ ids 0 .: ren (+1) = ids.
Proof.
  repeat split; autosubst.
Qed.

(* uses functional extensionality *)
Print subst_idX.



Lemma up_upren (ξ : var -> var) : up (ren ξ) = ren (upren ξ).
  autosubst.
Qed.

Lemma upren_unfold (xi : nat -> nat) :
               upren xi 0     = 0
  /\ forall n, upren xi (S n) = S (xi n).
  split. trivial. intro. trivial.
Qed.

(*
Print SubstLemmas.
Record SubstLemmas (term : Type) (Ids_term : Ids term)
(Rename_term : Rename term) (Subst_term : Subst term) : Prop
  := Build_SubstLemmas
  { rename_subst : forall (xi : var -> var) (s : term),
                   rename xi s = s.[ren xi];
    subst_id : forall s : term, s.[ids] = s;
    id_subst : forall (sigma : var -> term) (x : var),
               (ids x).[sigma] = sigma x;
    subst_comp : forall (sigma tau : var -> term) (s : term),
                 s.[sigma].[tau] = s.[sigma >> tau] }
*)




(* Exercise, give inductive spec for subst and prove it correct *)

Inductive substi (σ : var -> tm) : tm -> tm -> Prop :=
| s_var : forall n, substi σ (tvar n) (σ n)
| s_app : forall s s' t t',
            substi σ s s' -> substi σ t t' ->
            substi σ (tapp s t) (tapp s' t')
| s_abs : forall T t t',
            substi (up σ) t t' ->
            substi σ (tabs T t) (tabs T t')
| s_true : substi σ ttrue ttrue
| s_false : substi σ tfalse tfalse
| s_if : forall s t u s' t' u',
           substi σ s s' -> substi σ t t' -> substi σ u u' ->
           substi σ (tif s t u) (tif s' t' u').
Hint Constructors substi.


Theorem substi_correct : forall σ t t',
  subst σ t = t' <-> substi σ t t'.
Proof.
  intros. split.
  - intro. subst. generalize σ. clear σ.
           induction t; intros; asimpl; auto.
  - intro H. induction H; asimpl; congruence.
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


Lemma step_example1 : 
  (tapp idBB idB) ⇒* idB.
Proof.
  eapply multi_step.
  apply ST_AppAbs.
    apply v_abs.
  simpl.
  apply multi_refl.
Qed.

Lemma step_example2 :
  (tapp idBB (tapp idBB idB)) ⇒* idB.
Proof.
  eapply multi_step.
    apply ST_App2. auto.
    apply ST_AppAbs. auto.
  eapply multi_step.
    apply ST_AppAbs. simpl. auto.
    simpl. apply multi_refl. Qed.

Lemma step_example3 :
  tapp (tapp idBB notB) ttrue ⇒* tfalse.
Proof.
  eapply multi_step.
    apply ST_App1. apply ST_AppAbs. auto. simpl.
  eapply multi_step.
    apply ST_AppAbs. auto. simpl.
  eapply multi_step.
    apply ST_IfTrue. apply multi_refl. Qed.

Lemma step_example4 :
  tapp idBB (tapp notB ttrue) ⇒* tfalse.
Proof.
  eapply multi_step.
    apply ST_App2. auto.
    apply ST_AppAbs. auto. simpl.
  eapply multi_step.
    apply ST_App2. auto.
    apply ST_IfTrue.
  eapply multi_step.
    apply ST_AppAbs. auto. simpl.
  apply multi_refl. Qed.


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

Lemma step_example1' :
  (tapp idBB idB) ⇒* idB.
Proof. normalize. Qed.

Lemma step_example2' :
  (tapp idBB (tapp idBB idB)) ⇒* idB.
Proof. normalize. Qed.

Lemma step_example3' :
  tapp (tapp idBB notB) ttrue ⇒* tfalse.
Proof. normalize. Qed.

Lemma step_example4' :
  tapp idBB (tapp notB ttrue) ⇒* tfalse.
Proof. normalize. Qed.


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

Example typing_example_1 :
  empty ⊢ tabs TBool (tvar 0) ∈ TArrow TBool TBool.
Proof.
  apply T_Abs. apply T_Var. reflexivity. Qed.

Example typing_example_1' :
  empty ⊢ tabs TBool (tvar 0) ∈ TArrow TBool TBool.
Proof. auto. Qed.

Lemma no_cycle (s : ty) (t : ty) : ~ (t = TArrow t s).
Proof.
generalize s. clear s.
induction t; intro; try discriminate. intro. inversion H.
eapply IHt1. eassumption.
Qed.

Example typing_nonexample_3 :
  ~ (exists S, exists T,
        empty ⊢
          (tabs S
             (tapp (tvar 0) (tvar 0))) ∈
          T).
Proof.
  intro.
  destruct H. destruct H. inversion H. subst. inversion H4.
  subst. inversion H3. inversion H6. subst. simpl in *. inversion H2.
  inversion H9. subst. apply no_cycle with T12 T11. congruence.
Qed.


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
