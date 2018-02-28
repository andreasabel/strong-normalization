Require Export mathcomp.ssreflect.all_ssreflect.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.
Require Import Program.Tactics.

(* dependent destruction/induction *)
Require Export Coq.Program.Equality.

Global Set Implicit Arguments.
Global Unset Strict Implicits.
Global Unset Printing Implicit Defensive.

Tactic Notation "nointr" tactic(t) :=
  let m := fresh "marker" in
  pose (m := tt);
  t; revert_until m; clear m.

Ltac fext := nointr repeat (
  match goal with
    [ |- ?x = ?y ] =>
    (refine (@functional_extensionality_dep _ _ _ _ _) ||
     refine (@forall_extensionality _ _ _ _) ||
     refine (@forall_extensionalityP _ _ _ _) ||
     refine (@forall_extensionalityS _ _ _ _)); intro
  end).

Lemma pext {P Q : Prop} :
  (P -> Q) -> (Q -> P) -> P = Q.
Proof.
  move=> pq qp. exact: propositional_extensionality.
Qed.

Lemma pi {P : Prop} (p q : P) : p = q.
Proof.
  have e: P = True by exact: pext. move: p q. by rewrite e => -[] [].
Qed.
