(** * Abstract Reduction Systems

    Useful lemmas when working with small-step reduction relations. *)
From mathcomp Require Import ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope prop_scope with PROP.
Open Scope prop_scope.

Definition Rel  (T : Type) := T -> T -> Prop.

(** **** Reflexive, Transitive closure *)

Section Definitions.

Variables (T : Type) (e : Rel T).
Implicit Types (R S : T -> T -> Prop).

Inductive star (x : T) : T -> Prop :=
| starR : star x x
| starSE y z : star x y -> e y z -> star x z.

Hint Resolve starR.

Lemma star1 x y : e x y -> star x y.
Proof. now apply starSE. Qed.

Lemma star_trans y x z : star x y -> star y z -> star x z.
Proof. move=> A. elim=> //={z} y' z _. exact: starSE. Qed.

End Definitions.

Hint Resolve starR.
Arguments star_trans {T e} y {x z} A B.

Lemma star_img T1 T2 (f : T1 -> T2) (e1 : Rel T1) e2 :
  (forall x y, e1 x y -> star e2 (f x) (f y)) ->
  (forall x y, star e1 x y -> star e2 (f x) (f y)).
Proof.
  move=> A x y. elim=> //=y' z _ B /A. exact: star_trans.
Qed.

Lemma star_hom T1 T2 (f : T1 -> T2) (e1 : Rel T1) (e2 : Rel T2) :
  (forall x y, e1 x y -> e2 (f x) (f y)) ->
  (forall x y, star e1 x y -> star e2 (f x) (f y)).
Proof.
  move=> A. apply: star_img => x y /A. exact: star1.
Qed.

Arguments star_hom {T1 T2} f e1 {e2} A x y B.

(** **** Strong Normalization *)

Inductive sn T (e: Rel T) x : Prop :=
| SNI : (forall y, e x y -> sn e y) -> sn e x.

Lemma sn_preimage {T1 T2} (R1 : Rel T1) (R2 : Rel T2) (h : T1 -> T2) x :
  (forall x y, R1 x y -> R2 (h x) (h y)) -> sn R2 (h x) -> sn R1 x.
Proof.
  move eqn:(h x) => v A B. elim: B h x A eqn => {v} v _ ih h x A eqn.
  apply: SNI => y /A. rewrite eqn => /ih; eauto.
Qed.
