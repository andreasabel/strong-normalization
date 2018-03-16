Require Import base.

(** ** Types *)
Inductive ty := Base | Fun (A B : ty) | Plus (A B : ty).
Definition ctx := seq ty.

Fixpoint at_ty (G : ctx) (A : ty) : Type :=
  match G with
  | [::] => False
  | B :: G' => (A = B) + at_ty G' A
  end.

(** ** Environment structure *)
Definition env (G : ctx) (T : ty -> Type) := forall A, at_ty G A -> T A.
Definition ren (G1 G2 : ctx) := env G1 (at_ty G2).

Definition scons {G : ctx} {P : ty -> Type} {A : ty} (hd : P A) (tl : env G P) : env (A :: G) P :=
  fun B i =>
    match i with
    | inl p => eq_rect_r P hd p
    | inr j => tl B j
    end.
Notation "hd .: tl" := (@scons _ _ _ hd tl) (at level 55).

Definition scomp {P Q R : ty -> Type} (f : forall A, P A -> Q A) (g : forall A, Q A -> R A) :  forall A, P A -> R A := fun A x => g A (f A x).
Notation "eta >> eps" := (scomp eta eps) (at level 40).

Definition var0 {G : ctx} {A : ty} : at_ty (A :: G) A := inl erefl.
Definition shift {G : ctx} {B : ty} : ren G (B :: G) := fun A i => inr i.

Definition idren {G : ctx} : ren G G := fun A i => i.

Lemma scons_eta G P A (f : env (A :: G) P) :
  f A var0 .: shift >> f = f.
Proof. fext=>/=B -[]//= E. by destruct E. Qed.

Lemma scons_eta_id G A : var0 .: shift = @idren (A :: G).
Proof. fext=>/=B -[]// E. by destruct E. Qed.

Lemma scons_comp G P Q A (x : P A) (f : env G P) (g : forall A, P A -> Q A) :
  (x .: f) >> g = (g A x) .: f >> g.
Proof. fext=>/=B-[]//E. by destruct E. Qed.

Ltac fsimpl :=
  repeat match goal with
    | [|- context[idren >> ?f]] => change (idren >> f) with f
    | [|- context[?f >> idren]] => change (f >> idren) with f
    | [|- context[(?f >> ?g) >> ?h]] =>
        change ((f >> g) >> h) with (f >> (g >> h))
    | [|- context[@scons ?G ?P ?A ?x ?tl ?B var0]] =>
      change (@scons G P A x tl B var0) with x
    | [|- context[shift >> (?x1 .: ?xr)]] =>
        change (shift >> (x1 .: xr)) with xr
    | [|- context[?x2 .: shift >> ?f]] =>
        change x2 with (f _ var0); rewrite (@scons_eta _ _ _ f)
    | [|- context[?f _ var0 .: ?g]] =>
        change g with (shift >> f); rewrite scons_eta
    | _ => progress (rewrite ?scons_comp ?scons_eta_id)
  end.
