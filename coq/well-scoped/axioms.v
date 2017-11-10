(** * Functional and Propositional Extensionality *)
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Program.Tactics.

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

Axiom pext : forall P Q : Prop, (P <-> Q) -> (P = Q).

Lemma pi {P : Prop} (p q : P) : p = q.
Proof.
  assert (P = True) by (apply pext; tauto). subst. now destruct p,q.
Qed.
