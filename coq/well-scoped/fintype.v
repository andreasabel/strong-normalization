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

(* TODO : Having both funcomp and comp doesn't make sense. *)
Definition funcomp {X Y Z} (g : Y -> Z) (f : X -> Y)  :=
  fun x => g (f x).

Notation "f >> g" := (funcomp g f) (*fun x => g (f x)*) (at level 50) : subst_scope.
Open Scope subst_scope.

(** ** Finite Types
    We implement the finite type with _n_ elements, _I^n_, as the _n_-fold iteration of the Option Type. _I^0_ is implemented as the empty type.
*)

Fixpoint fin (n : nat) : Type :=
  match n with
  | 0 => False
  | S m => option (fin m)
  end.

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
Definition bound {n : nat} : fin (S n) := None.
Definition null {T} (i : fin 0) : T := match i with end.

Definition shift {n : nat} : ren n (S n) :=
  Some.

Definition up_ren m n (xi : ren m n) : ren (S m) (S n) :=
  bound .: xi >> shift.

Definition var_zero {n : nat} : fin (S n) := None.

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
  f bound .: shift >> f = f.
Proof. fext. intros [x|]; reflexivity.  Qed.

Definition id {X} (x : X) := x.

Lemma scons_eta_id {n : nat} : bound .: shift = id :> (fin (S n) -> fin (S n)).
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
         | [|- context[(?s.:?sigma) bound]] => change ((s.:sigma) bound) with s
         | [|- context[(?s.:?sigma) (shift ?m)]] => change ((s.:sigma) (shift m)) with (sigma m)
         | [|- context[idren >> ?f]] => change (idren >> f) with f
         | [|- context[?f >> idren]] => change (f >> idren) with f
         | [|- context[(?f >> ?g) >> ?h]] =>
           change ((f >> g) >> h) with (f >> (g >> h))
         | [|- context[?f >> (?x .: ?g)]] =>
           change (f >> (x .: g)) with g
         | [|- context[?x2 .: shift >> ?f]] =>
           change x2 with (f bound); rewrite (@scons_eta _ _ f)
         | [|- context[?f bound .: ?g]] =>
           change g with (shift >> f); rewrite scons_eta
         | _ => first [progress (rewrite scons_comp) | progress (rewrite scons_eta_id)]
         end.


Opaque scons.
Opaque bound.
Opaque null.
Opaque shift.
Opaque up_ren.
Opaque var_zero.
Opaque idren.
Opaque comp.
Opaque funcomp.
Opaque id.
