(** * The calculus of (co)inductive constructions *)

(** ** Abstraction *)

(** The calculus used in Coq is based on the calculus of constructions
    [Coquand, Huet, '88] with the addition of several later extensions
    such as an infinite hierarchy of types [Luo, '89], inductively
    defined data types [Pfenning, Paulin-Morhing, '88] and
    co-inductively defined data types [Giménez, 95].

    The CoC is a higher-order typed lambda calculus. It sits at the
    top of the "Lambda cube", as it allows all 4 forms of abstraction.

    The first type of abstraction is simply lambda-abstraction,
    i.e. values depending on values.*)

Definition add_two := fun (x : nat) => x + 2.

Check add_two.

(** Another type of abstraction is polymorphism, with which we can
    define value depending on types. *)

Definition id := fun (A : Type) (x : A) => x.

Check id.

(** Type operators offer a third form of abstraction, which allows
    defining types that depend on types*)

Definition arrow := fun (A B : Type) => A -> B.

Check arrow.

(** The last form of abstraction is dependent types, or types whose
    definition depends on values *)

Definition arrow_n :=
  fun (A : Type) =>
    fix F (n : nat) :=
    match n with
    | 0 => A
    | S n' => arrow A (F n')
    end.

Compute (arrow_n bool 3).

Check arrow_n.

(** ** Terms and types *)

(** In fact in the CoC there is no real distinction between values and
    types.

    - At the lowest level, there are concrete values (e.g. 0, true...)
      and programs (add, negb...)

    - The types of these terms (nat, bool, nat -> nat -> nat...) are
      also terms themselves. This means that they can be passed as
      arguments to functions, be used in the definition of a type. It
      also means that they have a type themselves *)

(** We can keep checking the types upward *)

Check 0.

Check nat.

Check Set.

Check Type.

(** This last answer should be surprising. It is known that this kind
    of typing results in an inconsistent system, for reasons similar
    to Russell's paradox in naive set theory (this is called Girard's
    paradox and is not quite as easy to exhibit as Russell's).

    Coq actually hides some technical detail when it comes to printing
    Type. These can be reactivated. *)

Set Printing Universes.

Check Set.

Check Type.

(** We now see that Type actually stands for an infinite hierarchy of
    types, thus preventing Girard's paradox. Each occurrence of Type is
    called a universe. Conveniently, any universe of rank i also has
    rank j for any j > i (so for example Set has the type Type(i) for
    any i).*)

Unset Printing Universes.

(** ** Terms in the CoC *)

(** Let us take a look at the different ways to form terms.*)

(** First we fix some constants *)
Axiom A : Set.

Axiom B : Set.

(** We can form terms by lambda abstraction.*)
Definition lambda := fun (x : A) => B.

(** This next construct is called product. This becomes a bit
    confusing later when we'll add inductively defined data types and
    the more common notion of product type.*)
Definition product := forall (x : A), B.

(** We fix another constant of the proper type to form a term by
    application *)
Axiom a : A.

Definition application := lambda a.

(** Note that A -> B is actually equivalent to forall (_ : A), B *)

(** In this definition, the second lambda is dependent on P. Observe
    the type.*)

Check fun (P : Set) (x : P) => x.

(** In this second definition, P is not used in the second
    lambda. This results in a simpler type, using -> instead of
    forall.*)

Check fun (P : Set) (x : A) => x.

(** These rules (constant, abstraction, product, application) are the
    only ones on which to build terms in the original calculus of
    constructions. *)

(** ** Inductively defined types *)

(** While it is possible to define a higher-order logic with only
    these rules, the addition of inductively defined data types is a
    useful feature.*)

(** Here is an example of an inductive data type *)

Inductive vector (T : Type) : nat -> Type :=
| vnil : vector T 0
| vcons : forall n, T -> vector T n -> vector T (S n).

(** There is a slight difference between the two arguments of the type
    (vector A n): the argument A has the same value in the return type
    of all the constructors. This is sometimes called an 'inductive
    parameter'. The value of the second argument varies across
    different constructors: 0 for vnil, (S n) for vcons. This is
    sometimes called a 'real argument'

    An inductive parameter can be turned into a real argument :

Inductive vector : Type -> nat -> Type :=
| vnil : forall T, vector T 0
| vcons : forall n T, T -> vector T n -> vector T (S n).

    But a real argument cannot in general be replaced by an inductive
    parameter.*)

(** Values from inductively defined data types can be manipulated by
    pattern matching. *)

Fixpoint vapp (A : Type) (n m : nat) (v1 : vector A n) (v2 : vector A m) : vector A (n + m) :=
  match v1 with
  | vnil _ => v2
  | vcons _ _ x v' => vcons _ _ x (vapp _ _ _ v' v2)
  end.

(** ** Programs and proofs *)

(** For a more eloquent presentation of the Curry-Howard
    correspondence, see [Wadler, 15] *)

(** x : T is usually understood as "x has type T", but it can also be
    understood as "x is a proof of T"*)

(** A -> B is the type of functions from A to B but also reads as "A
    implies B". Indeed a proof of A -> B must be a program that takes
    a proof of A as input and produce a proof of B as output.*)

(** Logical connectives (other than forall/->) can be defined
    inductively.*)

(** Conjunction corresponds to product type (using the usual
    definition of product here)*)
Inductive and (A B : Prop) : Prop :=
| conj : A -> B -> and A B.

Arguments conj {_ _} _ _.

(** Disjunction corresponds to sum *)
Inductive or (A B : Prop) : Prop :=
| disj_l : A -> or A B
| disj_r : B -> or A B.

Arguments disj_l {_ _} _.
Arguments disj_r {_ _} _.

(** False is the empty type, the type for which there exists no
    inhabitant/proof *)
Inductive False :=.

(** For True, are inhabited type will do, so unit is as good as any.*)
Inductive True :=
| unit : True.

(** ** Tactics and proof terms *)

(** So far we have written terms only when we needed functions, and
    used tactics to build proofs. But tactics are just a convenient
    mechanism to build terms. We can write proof terms directly (or
    more unusually, use tactics to build a function over small
    types).*)

Lemma and_comm (A B : Prop) : and A B -> and B A.
Proof.
  (* we must provide a term of type A /\ B -> B /\ A, it seems that
     this term should be a function with one argument of type A /\ B,
     although we don't really know what the body the function is going
     to look like. The tactic intro builds that lambda-abstraction for
     us, leaving a hole where the body of the function is.*)
  intros.
  Show Proof.
  (* We now have an element of type A /\ B in the context (the
     argument of the lambda abstraction, and we must build a term of
     type B /\ A. One way to construct this term is to pattern-match
     something in context, and later provide a term of type A /\ B for
     every match. destruct H creates this pattern-matching over H,
     leaving a hole in each branch.*)
  destruct H.
  (* the type (and A B) of H has only one constructor with two
     arguments of type A and B. Therefore we are now in a context with
     two terms H : A and H0 : B*)
  Show Proof.
  (* there is only one constructor for the type (and B A), so we apply
     it. After that we have to fill two holes, corresponding to the
     two arguments of the constructor.*)
  apply conj.
  Show Proof.
  (* for the next two holes, we have terms of the needed type in
     context, so we can use them directly using exact.*)
  - exact H0.
  - exact H.
Qed.

Print and_comm.

(** The tactic refine is a more general version of exact. Instead of a
    fully-formed term, it lets us put a term with holes (of course the
    type of this term must unify with the expected type of the
    hole). We can fill each hole later.

    This script emulates the action of the previous tactics, using
    only refine.*)
Lemma and_comm' (A B : Prop) : and A B -> and B A.
Proof.
  refine (fun H => _).
  refine (match H with conj H H0 => _ end).
  refine (conj _ _).
  - refine H0. (* without holes, this is identical to 'exact H0'*)
  - refine H.
Qed.

(** ** Equality *)

(** Here is the definition of the equality Prop *)

(*
Inductive eq (T : Type) (x : T) : T -> Prop :=
| eq_refl : eq T x x.
*)

(** This definition says that (eq T x y) holds only if x and y are
    equivalent terms. On the meta-level, two terms are considered
    equivalent if they have identical normal forms.

    For example 0 + (0 + (0 + n)) is equivalent n. However n + 0 does
    not normalize to n, so it is not considered equivalent.*)

(** ** Inductive proofs *)

(** Proofs by induction correspond naturally to recursive functions*)

(** Let us write an induction proof, separating the two steps. *)

(** *)
Definition base_case : forall (n m : nat), 0 + n + m = 0 + (n + m) :=
  fun (n m : nat) => eq_refl.

(** Proofs involving equational reasoning are not fun to write by
    hand, let's use tactics for now.*)
Lemma ind_step : forall (n m p : nat), n + m + p = n + (m + p) -> S n + m + p = S n + (m + p).
Proof.
  intros. simpl. rewrite <- H. apply eq_refl.
Qed.

Lemma add_assoc : forall (n m p : nat), n + m + p = n + (m + p).
Proof.
  intros. induction n as [| n'].
  - exact (base_case m p).
  - exact (ind_step n' m p IHn').
Qed.

Definition add_assoc' : forall (n m p : nat), n + m + p = n + (m + p) :=
  fix F (n m p : nat) :=
    match n with
    | O => base_case m p
    | S n' => ind_step n' m p (F n' m p)
    end.

(** If you print the proof term created by the script, you will see
    that induction actually applies nat_ind, the induction principle
    generated at the same time as nat was declared, rather than
    building a recursive function from the ground up.*)

Print add_assoc.

(** But it is important to note that nat_ind is not an axiom, just a
    simple function that we could define ourselves, if Coq didn't do
    it automatically (actually nat_ind is defined with nat_rect, so
    let us print that instead).*)

Print nat_rect.

(** Every inductively defined type has its associated induction
    principle *)

(** We mentioned equality reasoning earlier. Equality reasoning is
    based on the induction generated from the eq type*)

Print eq_rect.

(** Here are some useful lemmas/functions if you want to write
    equational proofs.*)
Print eq_ind.
Print eq_sym.
Print eq_ind_r.

(** However be advised, the resulting proof terms are not particularly
    pretty.*)
Print ind_step.

(** ** Prop vs Set *)

(** We found the lowest universe by checking the type of Set. There is
    another native sort which lives in Type(0), named Prop. Although
    Prop and Set share the same universe, there are some important
    differences between the two.

    Prop is often described as the type of proof-irrelevant
    propositions. What this means is that for a given proposition of
    type prop (e.g. forall (P Q : Prop), P /\ Q -> Q /\ P), we don't
    really care about specifics elements of this types (different
    proofs). The existence or non-existence of a proof matters, but
    the specifics of a given proof can usually be ignored.

    In contrast, for types in Set (so-called small types, such as
    bool, nat -> nat -> nat), we tend to care about the specifics of
    the elements that implement the type: true is different from
    false, mult from add...

    This distinction is useful when using the code extraction feature
    of Coq: objects in Set can be extracted to OCaml/Haskell/Scheme
    while elements of Prop are left aside.

    One important difference is that Prop is impredicative. Concretely
    this means that a term formed by quantification over Prop can
    itself be in Prop. *)

Check forall (P Q : Prop), ((P -> Q) -> P) -> P.

(** On the other hand a term quantifying over Set has to live in the
    next universe. *)

Check forall (P Q : Set), ((P -> Q) -> P) -> P.

(** ** Elimination and impredicativity *)

(** An impredicative universe seems more expressive, but it comes with
    its own risks. Unrestricted impredicativity leads to
    inconsistency, therefore Coq must put some restrictions on
    elimination (patter-matching) over Prop.*)

Inductive ex {T : Type} (P : T -> Prop) : Prop :=
  ex_intro : forall (t : T), P t -> ex P.

(** exists (x : T), P      ex T (fun x => P x *)

(** The following definition is forbidden because it attempts to
    eliminate a term whose type is Prop in a higher context Type *)

(*
Definition witness_prop {T : Type} {P : T -> Prop} (H : ex P) : T :=
  match H with
  | ex_intro _ t _ => t
  end.
*)

(** However it is possible to eliminate a proof to produce a proof.

    The next Prop describes types that are inhabited (have at least
    one element) *)

Inductive inhabited (T : Type) : Prop :=
  inhabits : T -> inhabited T.

(** The next lemma indicates that if we have a proof of some
    existentially quantified property over a type T, this type must be
    inhabited.*)

(** The proof can be constructed by elimination on the proof (destruct
    H)*)

Lemma exists_inhabited : forall (T : Type) (P : T -> Prop),
    ex P -> inhabited T.
Proof.
  intros. destruct H. apply inhabits. exact t.
Qed.

(** Or equivalently, here is the proof term, which pattern-matches the
    proof.*)

Definition exists_inhabited' : forall (T : Type) (P : T -> Prop), ex P -> inhabited T :=
  fun (T : Type) (P : T -> Prop) (H : ex P) =>
    match H with
    | ex_intro _ t _ => inhabits _ t
    end.

(** Let us now define a type that is very similar to ex, except that
    it doesn't live in Prop.

    Instead of being a proof that some element verifies a property P,
    an element of type (sig P) is usually understood as being the set
    of elements that verifies P.*)

Inductive sig {T : Type} (P : T -> Prop) : Type :=
  sig_intro : forall (t : T), P t -> sig P.

(** The following function, similar to witness, extracts a member from
    a type (sig P). The definition can pattern match S without
    restriction since (sig P) is not in Prop*)

Definition member {T : Type} {P : T -> Prop} (S : sig P) : T :=
  match S with
  | sig_intro _ t _ => t
  end.