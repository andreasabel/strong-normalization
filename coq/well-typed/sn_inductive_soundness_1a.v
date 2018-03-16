(** * Different Characterisations Strong Normalisation *)

Require Import base contexts stlc reduction sn_defs.
Set Implicit Arguments.
Unset Strict Implicit.

(** ** Closure Properties of sn *)
Lemma sn_preimage {G1 G2 A1 A2} (f : tm G1 A1 -> tm G2 A2) (s : tm G1 A1) :
  (forall t u, step t u -> step (f t) (f u)) ->
  sn (f s) -> sn s.
Proof.
  move=> H sns. dependent induction sns. apply: snI => t st.
  apply: H0; last by reflexivity. apply: H. eassumption. exact: H.
Qed.

Lemma sn_appL {G A B} (s : tm G (Fun A B)) (t : tm G A) :
  sn (app s t) -> sn s.
Proof. apply: (@sn_preimage _ _ _ _ (app^~ t)); eauto using @step. Qed.

Lemma sn_inst {G1 G2 A} (f : subst G1 G2) (s : tm G1 A) :
  sn (inst f s) -> sn s.
Proof. apply: sn_preimage. exact: step_inst. Qed.

Lemma closed_lam {g} A B (s : tm (A ::g)  B) :
  sn s -> sn (lam s).
Proof.
  induction 1 as [M H IH]. constructor. intros M' C. inv C. auto.
Qed.

Lemma closed_appR g A B (M: tm g (Fun A B)) (N: tm g A)  :
  sn (app M N) -> sn N.
Proof. eapply sn_preimage. apply step_appR. Qed.

(* Weak Head Reduction *)
Inductive redsn : forall g A,  tm g A -> tm g A -> Prop :=
 | redsn_beta g A B (M: tm (A :: g) B) (N: tm g A) : sn N -> redsn (app (lam M) N) (inst (N.:ids) M)
 | redsn_app g A B (R R' : tm g (Fun A B)) (M : tm g A) : redsn R R' -> redsn (app R M) (app R' M).

Lemma fundamental_backwards g A B (M: tm (A::g) B) (N: tm g A):
   sn N -> sn (inst (N.: ids) M) -> sn (app (lam M) N).
Proof.
  intros sn_N sn_M'.
  assert (H: sn M) by (now apply sn_inst in sn_M').
  revert M H sn_M'. induction sn_N as [N sn_N IH_N].
  induction 1 as [M sn_M IH_M]. intros H. constructor. intros M' C. inv C.
  - constructor. intros M' H'. inv H. now apply H.
  - inv C. rename b2 into M'. eapply IH_M. assumption.
    eauto using sn_mstep, mstep_beta, mstep_step.
  - eapply IH_N; eauto.
    + now constructor.
    + eauto using sn_mstep, mstep_beta, mstep_step.
Qed.

(* Neutral terms *)
Fixpoint neutral g A (M: tm g A) :=
  match M with
  | var _ x => True
  | app _ _  s t => neutral s
  | _ => False
  end.

Lemma neutral_preservation g A (M N: tm g A):
  neutral  M -> step M N ->  neutral N.
Proof. intros H. induction 1; simpl in *; intuition. Qed.

Lemma sn_confluence g A (M: tm g A):
  forall M' M'', redsn M M' -> step M M'' -> M' = M'' \/ exists M''', redsn M'' M''' /\ mstep M' M'''.
Proof.
  induction M as [x | T M IHM | M1 IHM1 M2 IHM2]; intros M' M'' D E; inv D; inv E.
  - now left.
  - inv E. right. eexists. split.
    + now constructor.
    + apply mstep_inst. eauto using mstep_step.
  - right. eexists. split. econstructor. inv H; eauto. apply mstep_beta; eauto using mstep_step.
  - inv D.
  - destruct (IHM1 _ _ D E) as [IH|(M''&IH1&IH2)].
    + subst. now left.
    + right. eexists. split.
      * econstructor. eassumption.
      * eapply mstep_app. assumption. constructor.
  - right. eexists. split.
    + constructor. eassumption.
    + eapply mstep_app. constructor. eauto using mstep_step.
Qed.

Lemma redsn_backwards g A (M M': tm g A):
 redsn M M' -> sn M' -> sn M.
Proof.
 induction 1 as [|g A B M M' N H IH].
 - intros D. eapply fundamental_backwards; eauto.
 - intros D. specialize (IH (sn_appL D)).
   assert (sn_N: sn N) by (now apply closed_appR in D).
   revert M IH M' D H. induction sn_N as [N sn_N IH_N]. induction 1 as [M sn_M IH_M].
   constructor. intros M_N C. inv C.
   + inv H.
   + destruct (sn_confluence H C) as [E|(M'''&C1&C2)].
     * now subst.
     * eapply IH_M with (M' := M'''); eauto.
       eapply sn_mstep; [|eassumption]. eapply mstep_app; eauto.
   + eapply IH_N; eauto.
     * now constructor.
     * inv D. apply H. now constructor.
Qed.

Lemma sn_app_neutral g A (N : tm g A) :
   sn N -> forall B (M: tm g (Fun A B)), neutral M -> sn M -> sn (app M N).
Proof.
  induction 1 as [N sn_N IH_N].
  induction 2 as [M sn_M IH_M].
  constructor. intros M' C. inv C.
  - contradiction.
  - eauto using neutral_preservation.
  - eauto using snI.
Qed.
