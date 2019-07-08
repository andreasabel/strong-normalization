(* Version: 17.09. *)

(** * Axiomatic Assumptions
    For our development, we have to extend Coq with two well known axiomatic assumptions, namely _functional extensionality_ and _propositional extensionality_. The latter entails _proof irrelevance_.
*)

(** ** Functional Extensionality
    We import the axiom from the Coq Standard Library and derive a utility tactic to make the assumption practically usable.
*)
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

(** ** Propositional Extensionality
    We state the axiom of _propositional extensionality_ directly and use it to prove _proof irrelevance_.
*)
Axiom pext : forall P Q : Prop, (P <-> Q) -> (P = Q).

Lemma pi {P : Prop} (p q : P) : p = q.
Proof.
  assert (P = True) by (apply pext; tauto). subst. now destruct p,q.
Qed.
