(*
Just some extra (optional) thms, feel free to add more.
*)

Require Import exindprop.
Import IndProp.

Theorem empty_star : forall {T} (x : T) (xs : list T),
  ~(x::xs ∈ (ε : regex T)**).
Admitted.

Definition regex_eq {T} (re1 re2 : regex T) := forall (x : list T),
  x ∈ re1 <-> x ∈ re2.

Notation "re1 ∋∈ re2" := (regex_eq re1 re2) (at level 75, no associativity).

Theorem concat_left_id : forall {T} (re : regex T),
  (ε·re) ∋∈ re.
Admitted.

Theorem concat_assoc : forall {T} (re1 re2 re3 : regex T),
  ((re1·re2)·re3) ∋∈ (re1·re2·re3).
Admitted.

Theorem concat_replace : forall {T} (re1 re2 re3 : regex T),
  re1 ∋∈ re2 -> (re1·re3) ∋∈ (re2·re3).
Admitted.

Theorem union_comm : forall {T} (re1 re2 : regex T),
  (re1 ∪ re2) ∋∈ (re2 ∪ re1).
Admitted.

(* splitting this proof into some lemmas might be useful *)
Theorem many_stars : forall {T} (re : regex T),
  (re** ** ** ** ** ** ** ** ** ** ** ** ** ** ** ** ** ** ** ** ** ** ** **) ∋∈ (re**).
Admitted.
