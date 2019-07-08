(* Version: 17.10. *)

(** * Finite Types and Mappings
    Our development utilises well-scoped de Bruijn syntax. This means that the de Bruijn indices are taken from finite types. As a consequence, any kind of substitution or environment used in conjunction with well-scoped syntax takes the form of a mapping from some finite type _I^n_. In particular, _renamings_ are mappings _I^n -> I^m_. Here we develop the theory of how these parts interact.
*)
Require Export axioms.
Set Implicit Arguments.
Unset Strict Implicit.

Definition ap {X Y} (f : X -> Y) {x y : X} (p : x = y) : f x = f y :=
  match p with eq_refl => eq_refl end.

Definition apc {X Y} {f g : X -> Y} {x y : X} (p : f = g) (q : x = y) : f x = g y :=
  match q with eq_refl => match p with eq_refl => eq_refl end end.

(** ** Forward Function Composition
    Substitutions represented as functions are ubiquitious in this development and we often have to compose them, without talking about their pointwise behaviour.
    That is, we are interested in the forward compostion of functions, _f o g_, for which we introduce a convenient notation, "f >> g". The direction of the arrow serves as a reminder of the _forward_ nature of this composition, that is first apply _f_, then _g_. *)

(** ** Finite Types
    We implement the finite type with _n_ elements, _I^n_, as the _n_-fold iteration of the Option Type. _I^0_ is implemented as the empty type.
*)

Fixpoint fin (n : nat) : Type :=
  match n with
  | 0 => False
  | S m => option (fin m)
  end.

Definition funcomp {X Y Z} (g : Y -> Z) (f : X -> Y)  :=
  fun x => g (f x).


(** * Type classes for renamings. *)

Class Ren1 (X1  : Type) (Y Z : Type) :=
  ren1 : X1 -> Y -> Z.

Class Ren2 (X1 X2 : Type) (Y Z : Type) :=
  ren2 : X1 -> X2 -> Y -> Z.

Class Ren3 (X1 X2 X3 : Type) (Y Z : Type) :=
  ren3 : X1 -> X2 -> X3 -> Y -> Z.

Class Ren4 (X1 X2 X3 X4 : Type) (Y Z : Type) :=
  ren4 : X1 -> X2 -> X3 -> X4 -> Y -> Z.

Class Ren5 (X1 X2 X3 X4 X5 : Type) (Y Z : Type) :=
  ren5 : X1 -> X2 -> X3 -> X4 -> X5 -> Y -> Z.

Notation "s ⟨ xi1 ⟩" := (ren1  xi1 s) (at level 7, left associativity, format "s  ⟨ xi1 ⟩") : subst_scope.

Notation "s ⟨ xi1 ; xi2 ⟩" := (ren2 xi1 xi2 s) (at level 7, left associativity, format "s  ⟨ xi1 ; xi2 ⟩") : subst_scope.

Notation "s ⟨ xi1 ; xi2 ; xi3 ⟩" := (ren3 xi1 xi2 xi3 s) (at level 7, left associativity, format "s  ⟨ xi1 ; xi2 ; xi3 ⟩") : subst_scope.

Notation "s ⟨ xi1 ; xi2 ; xi3 ; xi4 ⟩" := (ren4  xi1 xi2 xi3 xi4 s) (at level 7, left associativity, format "s  ⟨ xi1 ; xi2 ; xi3 ; xi4 ⟩") : subst_scope.

Notation "s ⟨ xi1 ; xi2 ; xi3 ; xi4 ; xi5 ⟩" := (ren5  xi1 xi2 xi3 xi4 xi5 s) (at level 7, left associativity, format "s  ⟨ xi1 ; xi2 ; xi3 ; xi4 ; xi5 ⟩") : subst_scope.

Notation "⟨ xi ⟩" := (ren1 xi) (at level 1, left associativity, format "⟨ xi ⟩") : fscope.

Notation "⟨ xi1 ; xi2 ⟩" := (ren2 xi1 xi2) (at level 1, left associativity, format "⟨ xi1 ; xi2 ⟩") : fscope.


(** * Type Classes for Substiution *)

Class Subst1 (X1 : Type) (Y Z: Type) :=
  subst1 : X1 -> Y -> Z.

Class Subst2 (X1 X2 : Type) (Y Z: Type) :=
  subst2 : X1 -> X2 -> Y  -> Z.

Class Subst3 (X1 X2 X3 : Type) (Y Z: Type) :=
  subst3 : X1 -> X2 -> X3 ->  Y  -> Z.

Class Subst4 (X1 X2 X3 X4: Type) (Y Z: Type) :=
  subst4 : X1 -> X2 -> X3 -> X4 -> Y  -> Z.

Class Subst5 (X1 X2 X3 X4 X5 : Type) (Y Z: Type) :=
  subst5 : X1 -> X2 -> X3 -> X4 -> X5  -> Y  -> Z.

Notation "s [ sigma ]" := (subst1 sigma s) (at level 7, left associativity, format "s '/' [ sigma ]") : subst_scope.

Notation "s [ sigma ; tau ]" := (subst2 sigma tau s) (at level 7, left associativity, format "s '/' [ sigma ; '/'  tau ]") : subst_scope.



Arguments funcomp {X Y Z} (g)%fscope (f)%fscope.


Notation "f >> g" := (funcomp g f) (*fun x => g (f x)*) (at level 50).
Open Scope subst_scope.


(** *** Extension of Finite Mappings
    Assume we are given a mapping _f_ from _I^n_ to some type _X_, then we can _extend_ this mapping with a new value from _x : X_ to a mapping from _I^n+1_ to _X_. We denote this operation by _x . f_ and define it as follows:
*)
Definition scons {X : Type} {n : nat} (x : X) (f : fin n -> X) (m : fin (S n)) : X :=
  match m with
  | None => x
  | Some i => f i
  end.
Notation "x .: f" := (@scons _ _ x f) (at level 55) : subst_scope.

(** *** Renamings and Injective Renamings
    As mentioned above, _renamings_ are mappings between finite types.
*)
Definition ren (m n : nat) : Type := fin m -> fin n.


(** We give a special name, _bound_, to the newest element in a non-empty finite type, as it usually corresponds to a freshly bound variable. We also concisely capture that _I^0_ really is empty with an exfalso proof principle. *)
Definition var_zero {n : nat} : fin (S n) := None.

Definition null {T} (i : fin 0) : T := match i with end.

Definition shift {n : nat} : ren n (S n) :=
  Some.

Definition up_ren m n (xi : ren m n) : ren (S m) (S n) :=
  var_zero .: xi >> shift.


Definition idren {k: nat} : ren k k :=
  fun x => x.

Definition comp := @funcomp.

Lemma up_ren_ren k l m (xi: ren k l) (zeta : ren l m) (rho: ren k m) (E: forall x, (xi >> zeta) x = rho x) :
  forall x, (up_ren xi >> up_ren zeta) x = up_ren rho x.
Proof.
  intros [x|].
  - simpl. unfold funcomp. now rewrite <- E.
  - reflexivity.
Qed.

Arguments up_ren_ren {k l m} xi zeta rho E.

(** Lemmas for one sort. **)

(* AsimplConsEta *)
Lemma scons_eta {T} {n : nat} (f : fin (S n) -> T) :
  f var_zero .: shift >> f = f.
Proof. fext. intros [x|]; reflexivity.  Qed.

Definition id {X} (x : X) := x.

Lemma scons_eta_id {n : nat} : var_zero .: shift = id :> (fin (S n) -> fin (S n)).
Proof. fext. intros [x|]; reflexivity. Qed.

Lemma scons_comp (T: Type) U {m} (s: T) (sigma: fin m -> T) (tau: T -> U ) :
  (s .: sigma) >> tau = (tau s) .: (sigma >> tau) .
Proof.
  fext. intros [x|]. reflexivity. simpl. reflexivity.
Qed.

Ltac fsimpl :=
  repeat match goal with
         | [|- context[id >> ?f]] => change (id >> f) with f (* AsimplCompIdL *)
         | [|- context[?f >> id]] => change (f >> id) with f (* AsimplCompIdR *)
         | [|- context [id ?s]] => change (id s) with s
         | [|- context[comp ?f ?g]] => change (comp f g) with (g >> f) (* AsimplCompIdL *)
         | [|- context[(?f >> ?g) >> ?h]] =>
           change ((f >> g) >> h) with (f >> (g >> h)) (* AsimplComp *)
         | [|- context[(?s.:?sigma) var_zero]] => change ((s.:sigma) var_zero) with s
         | [|- context[(?s.:?sigma) var_zero]] => change ((s.:sigma) var_zero) with s
         | [|- context[(?s.:?sigma) (shift ?m)]] => change ((s.:sigma) (shift m)) with (sigma m)
         | [|- context[idren >> ?f]] => change (idren >> f) with f
         | [|- context[?f >> idren]] => change (f >> idren) with f
         | [|- context[(?f >> ?g) >> ?h]] =>
           change ((f >> g) >> h) with (f >> (g >> h))
         | [|- context[?f >> (?x .: ?g)]] =>
           change (f >> (x .: g)) with g
         | [|- context[?x2 .: shift >> ?f]] =>
           change x2 with (f var_zero); rewrite (@scons_eta _ _ f)
         | [|- context[?f var_zero .: ?g]] =>
           change g with (shift >> f); rewrite scons_eta
         | _ => first [progress (rewrite scons_comp) | progress (rewrite scons_eta_id)]
         end.

Ltac fsimplc :=
  repeat match goal with
         | [H: context[id >> ?f] |- _] => change (id >> f) with f in H(* AsimplCompIdL *)
         | [H: context[?f >> id]|- _] => change (f >> id) with f in H(* AsimplCompIdR *)
         | [H: context [id ?s]|- _] => change (id s) with s in H
         | [H: context[comp ?f ?g]|- _] => change (comp f g) with (g >> f) in H (* AsimplCompIdL *)
         | [H: context[(?f >> ?g) >> ?h]|- _] =>
           change ((f >> g) >> h) with (f >> (g >> h)) in H (* AsimplComp *)
         | [H: context[(?s.:?sigma) var_zero]|- _] => change ((s.:sigma) var_zero) with s in H
         | [H: context[(?s.:?sigma) var_zero]|- _] => change ((s.:sigma) var_zero) with s in H
         | [H: context[(?s.:?sigma) (shift ?m)]|- _] => change ((s.:sigma) (shift m)) with (sigma m) in H
         | [H: context[idren >> ?f]|- _] => change (idren >> f) with f in H
         | [H: context[?f >> idren]|- _] => change (f >> idren) with f in H
         | [H: context[(?f >> ?g) >> ?h]|- _] =>
           change ((f >> g) >> h) with (f >> (g >> h)) in H
         | [H: context[?f >> (?x .: ?g)]|- _] =>
           change (f >> (x .: g)) with g in H
         | [H: context[?x2 .: shift >> ?f]|- _] =>
           change x2 with (f var_zero) in H; rewrite (@scons_eta _ _ f) in H
         | [H: context[?f var_zero .: ?g]|- _] =>
           change g with (shift >> f) in H; rewrite scons_eta in H
         | _ => first [progress (rewrite scons_comp in *) | progress (rewrite scons_eta_id in *)]
         end.

Tactic Notation "fsimpl" "in" "*" :=
  fsimpl; fsimplc.

Opaque scons.
Opaque var_zero.
Opaque null.
Opaque shift.
Opaque up_ren.
Opaque var_zero.
Opaque idren.
Opaque comp.
Opaque funcomp.
Opaque id.

(** * Notations *)

Class Var X Y :=
  ids : X -> Y.

Module CommaNotation.
Notation "s , sigma" := (scons s sigma) (at level 60, format "s ,  sigma", right associativity) : subst_scope.
End CommaNotation.

Notation "s '..'" := (scons s ids) (at level 1, format "s ..") : subst_scope.

Notation "↑" := (shift) : subst_scope.

Tactic Notation "auto_case" tactic(t) :=  (match goal with
                                           | [|- forall (i : fin 0), _] => intros []; t
                                           | [|- forall (i : fin (S (S (S (S _))))), _] => intros [[[[|]|]|]|]; t
                                           | [|- forall (i : fin (S (S (S _)))), _] => intros [[[|]|]|]; t
                                           | [|- forall (i : fin (S (S _))), _] => intros [[?|]|]; t
                                           | [|- forall (i : fin (S _)), _] =>  intros [?|]; t
                                           end).
    Ltac unfold_funcomp := match goal with
                           | |-  context[(?f >> ?g) ?s] => change ((f >> g) s) with (g (f s))
                           end.
