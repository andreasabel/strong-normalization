(** * Finite Types and Mappings
    Our development utilises well-scoped de Bruijn syntax. This means that the de Bruijn indices are taken from finite types. As a consequence, any kind of substitution or environment used in conjunction with well-scoped syntax takes the form of a mapping from some finite type _I^n_. In particular, _renamings_ are mappings _I^n -> I^m_. Here we develop the theory of how these parts interact.
*)
From mathcomp Require Import ssreflect.all_ssreflect.
Require Import axioms.
Set Implicit Arguments.
Unset Strict Implicit.

(** *** Forward Function Composition
    Substitutions represented as functions are ubiquitious in this development and we often have to compose them, without talking about their pointwise behaviour.
    That is, we are interested in the forward compostion of functions, _f o g_, for which we introduce a convenient notation, "f >> g". The direction of the arrow serves as a reminder of the _forward_ nature of this composition, that is first apply _f_, then _g_. *)

Notation "f >> g" := (funcomp tt g f) (*fun x => g (f x)*) (at level 50) : subst_scope.
Open Scope subst_scope.

(** *** Finite Types
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

(** _Injective renamings_ are renamings packaged witha a proof of injectivity. *)
Set Primitive Projections.
Structure iren (m n : nat) := IRen {
  iren_fun :> fin m -> fin n;
  iren_inj : injective iren_fun
}.
Arguments IRen {m n} iren_fun iren_inj.

(** Functional extensionality lifts to injective renamings, courtesy of proof irrelevance. *)
Lemma iren_eq {m n} (f g : iren m n) :
  (forall x, f x = g x) -> f = g.
Proof.
  move: f g => -[f fP] [g gP] /= H. have E: f = g by fext.
  destruct E. f_equal. exact: pi.
Qed.

(** We give a special name, _bound_, to the newest element in a non-empty finite type, as it usually corresponds to a freshly bound variable. We also concisely capture that _I^0_ really is empty with an exfalso proof principle. *)
Definition bound {n : nat} : fin n.+1 := None.
Definition null {T} (i : fin 0) : T := match i with end.

(** We define forward composition for injective renamings, which has to compose the renamings and combine the injectivity proofs. *)
Definition rcomp {m n k : nat} (f : iren m n) (g : iren n k) : iren m k :=
  @IRen m k (f >> g) (fun x y e => iren_inj (iren_inj e)).
Notation "f >>> g" := (rcomp f g) (at level 50) : subst_scope.

(** We identify the identity function as an injective renaming. *)
Definition idren {n : nat} : iren n n :=
  @IRen n n id (fun x y e => e).

(** The _shift_ operation of the sigma-calculus is also an injective renaming. *)
Definition shift {n : nat} : iren n n.+1 :=
  @IRen n n.+1 Some (fun x y e => f_equal (fun o => if o is Some z then z else x) e).
Arguments shift {n} : simpl never.

(** With _shift_ and _bound_ we can implement the _up_ operation which constitutes the adjustment of renamings that are moved underneath a binder. *)
Definition up {m n : nat} (f : iren m n) : iren m.+1 n.+1.
  refine (@IRen m.+1 n.+1 (bound .: f >>> shift) _).
  abstract (by move=>/=[x|] [y|] //= [/iren_inj->]).
Defined.

(** We now establish the relevant interactions of _extension_, _composition_, _shift_ and  _up_. *)
Lemma shift_up {m n} (f : iren m n) :
  shift >>> up f = f >>> shift.
Proof. exact: iren_eq. Qed.

Lemma scons_eta {T} {n : nat} (f : fin n.+1 -> T) :
  f bound .: shift >> f = f.
Proof. by fext=>/=;case. Qed.

Lemma scons_eta_id {n : nat} : bound .: shift = id :> (fin n.+1 -> fin n.+1).
Proof. by fext=>/=;case. Qed.

Lemma scons_comp {T1 T2} {n : nat} (x : T1) (f : fin n -> T1) (g : T1 -> T2) :
  (x .: f) >> g = (g x) .: f >> g.
Proof. by fext=>/=;case. Qed.

(** Lastly we provide a tactic that simplifies expressions containing the structures defined here with the help of the associated properties. *)
Ltac fsimpl :=
  repeat match goal with
    | [|- context[id >> ?f]] => change (id >> f) with f
    | [|- context[?f >> id]] => change (f >> id) with f
    | [|- context[(?f >> ?g) >> ?h]] =>
        change ((f >> g) >> h) with (f >> (g >> h))
    | [|- context[idren >>> ?f]] => change (idren >>> f) with f
    | [|- context[?f >>> idren]] => change (f >>> idren) with f
    | [|- context[(?f >>> ?g) >>> ?h]] =>
        change ((f >>> g) >>> h) with (f >>> (g >>> h))
    | [|- context[?f >> (?x .: ?g)]] =>
        change (f >> (x .: g)) with g
    (*| [|- context[shift >> (?x1 .: ?xr)]] =>
        change (shift >> (x1 .: xr)) with xr*)
    (*| [|- context[Some >> (?x1 .: ?xr)]] =>
        change (Some >> (x1 .: xr)) with xr*)
    | [|- context[?x2 .: shift >> ?f]] =>
        change x2 with (f bound); rewrite (@scons_eta _ _ f)
    | [|- context[?f bound .: ?g]] =>
        change g with (shift >> f); rewrite scons_eta
    (*| [|- context[?x2 .: Some >> ?f]] =>
        change x2 with (f bound); rewrite (@scons_eta _ _ f)*)
    | _ => progress (rewrite ?scons_comp ?scons_eta_id)
  end.
