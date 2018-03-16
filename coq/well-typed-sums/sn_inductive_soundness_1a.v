(** * Different Characterisations Strong Normalisation *)

Require Import base contexts stlc reduction sn_defs.

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
Proof.
  apply: (@sn_preimage _ _ _ _ (app^~ t)); eauto using @step.
Qed.

Lemma sn_inst {G1 G2 A} (f : subst G1 G2) (s : tm G1 A) :
  sn (inst f s) -> sn s.
Proof.
  apply: sn_preimage. exact: step_inst.
Qed.

Lemma closed_lam {g} A B (s : tm (A ::g)  B) :
  sn (lam s) <-> sn s.
Proof.
  split.
  - eapply sn_preimage. exact: step_abs.
  - induction 1 as [M H IH].
    constructor. intros M' C. inv C. auto.
Qed.

Lemma closed_appR g A B (M: tm g (Fun A B)) (N: tm g A)  :
  sn (app M N) -> sn N.
Proof. eapply sn_preimage. apply step_appR. Qed.

Lemma closed_inl g A B (M: tm g A)  :
  sn M -> sn (inl (B := B) M).
Proof. induction 1 as [M H IH]. constructor. intros M' C. inv C. auto. Qed.

Lemma closed_inr g A B (M: tm g B)  :
  sn M -> sn (inr (A := A) M).
Proof. induction 1 as [M H IH]. constructor. intros M' C. inv C. auto. Qed.

Lemma closed_orelim g A B C (M: tm g (Plus A B)) (N1: tm (A::g) C) N2:
  sn (orelim M N1 N2) -> sn M /\ sn N1 /\ sn N2.
Proof.
  intros H. split.
  - revert H. apply sn_preimage with (f := fun x => orelim x N1 N2).
    intros t t' H. now apply step_orelim.
  - split.
    + revert H. apply sn_preimage with (f := fun x => orelim M x N2).
      intros. now apply step_orelimL.
    + revert H. eapply sn_preimage. apply step_orelimR.
Qed.

(* Weak Head Reduction *)
Inductive redsn : forall g A,  tm g A -> tm g A -> Prop :=
 | redsn_beta g A B (M: tm (A :: g) B) (N: tm g A) : sn N -> redsn (app (lam M) N) (inst (N.:ids) M)
 | redsn_app g A B (R R' : tm g (Fun A B)) (M : tm g A) : redsn R R' -> redsn (app R M) (app R' M)
 | redsn_or g A B C (M M' : tm g (Plus A B)) (N1 : tm (A ::g) C) N2: redsn M M' -> redsn (orelim M N1 N2) (orelim M' N1 N2)
 | redsn_caseL G A B C (s: tm G A) t t' (u: tm (B :: G) C) : sn s -> sn t -> sn u -> t' = (inst (s.:ids) t) -> redsn (orelim (inl s) t u) t'
| redsn_caseR G A B C (s: tm G B) (t: tm (A :: G) C) u u': sn s -> sn t -> sn u -> u' = (inst (s.:ids) u) ->  redsn (orelim (inr s) t u) u'.

Lemma fundamental_backwards g A B (M: tm (A::g) B) (N: tm g A):
   sn N -> sn (inst (N.: ids) M) -> sn (app (lam M) N).
Proof.
  intros sn_N sn_M'.
  assert (H: sn M) by (now apply sn_inst in sn_M').
  revert M H sn_M'. induction sn_N as [N sn_N IH_N].
  induction 1 as [M sn_M IH_M]. intros H. constructor. intros M' C. inv C.
  - assumption.
  - inv C. rename b2 into M'. eapply IH_M. assumption.
    eauto using sn_mstep, mstep_beta, mstep_step.
  - eapply IH_N; eauto.
    + now constructor.
    + eauto using sn_mstep, mstep_beta, mstep_step.
Qed.

Lemma fundamental_backwards_orl g A B C (s : tm g A) (t: tm (A::g) C) (u: tm (B::g) C):
   sn s -> sn u -> sn (inst (s.: ids) t) -> sn (orelim (inl s) t u).
Proof.
  intros sn_s sn_u H. assert (H': sn t) by (now apply sn_inst in H).
  revert t H' u sn_u H.
  induction sn_s as [s sn_s IHs].
  induction 1 as [u sn_u IHu].
  induction 1 as [t sn_t IHt].  intros H. constructor. intros s' D. inv D.
  - inv D. apply IHs. assumption. now constructor. now constructor.
    eauto using sn_mstep, mstep_beta, mstep_step.
  - apply IHu; eauto. now constructor. eauto using sn_mstep, mstep_beta, mstep_step.
  - eapply IHt; eauto.
  - assumption.
Qed.

Lemma fundamental_backwards_orr g A B C (s : tm g B) (t: tm (A::g) C) (u: tm (B::g) C):
   sn s -> sn t -> sn (inst (s.: ids) u) -> sn (orelim (inr s) t u).
Proof.
  intros sn_s sn_t H. assert (H': sn u) by (now apply sn_inst in H).
  revert u H' t sn_t H.
  induction sn_s as [s sn_s IHs].
  induction 1 as [t sn_t IHt].
  induction 1 as [u sn_u IHu].  intros H. constructor. intros s' D. inv D.
  - inv D. apply IHs; eauto. now constructor. now constructor.
    eauto using sn_mstep, mstep_beta, mstep_step.
  - eapply IHu; eauto.
  - eapply IHt; eauto.  now constructor. eauto using sn_mstep, mstep_beta, mstep_step.
  - assumption.
Qed.

(* Neutral terms *)
Fixpoint neutral g A (M: tm g A) :=
  match M with
  | var _ x => True
  | app _ _  s t => neutral s
  | orelim _ _ _ s t u => neutral s
  | _ => False
  end.

Lemma neutral_preservation g A (M N: tm g A):
  neutral  M -> step M N ->  neutral N.
Proof. intros H. induction 1; simpl in *; intuition. Qed.

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

Lemma sn_case_neutral g A B C (N1 : tm (A ::g) C):
  sn N1 -> forall N2,  sn N2 -> forall (M: tm g (Plus A B)), sn M -> neutral M ->  sn (orelim M N1 N2).
Proof.
  induction 1 as [N1 snN1 IHN1].
  induction 1 as [N2 snN2 IHN2].
  induction 1 as [M snM IHM].
  intros H. constructor. intros M' H'. inv H'.
  * apply IHM. assumption. eapply neutral_preservation; eassumption.
  * now apply IHN1.
  * now apply IHN2.
  * contradiction.
  * contradiction.
Qed.

Lemma sn_confluence g A (M: tm g A):
  forall M' M'', redsn M M' -> step M M'' -> M' = M'' \/ exists M''', redsn M'' M''' /\ mstep M' M'''.
Proof.
  induction M as [g A x | g A B M IHM N IHN |g A B M IHM| g A B M IHM | g A B M IHM | g A B C M IHM N1 IHN1 N2 IHN2]; intros M' M'' D E; inv D; inv E.
  - now left.
  - inv E. right. eexists. split.
    + now constructor.
    + apply mstep_inst. eauto using mstep_step.
  - right. eexists. split. econstructor. inv H; eauto. apply mstep_beta; eauto using mstep_step.
  - inv D.
  - destruct (IHM _ _ D E) as [IH|(M''&IH1&IH2)].
    + subst. now left.
    + right. eexists. split.
      * econstructor. eassumption.
      * eapply mstep_app. assumption. constructor.
  - right. eexists. split.
    + constructor. eassumption.
    + eapply mstep_app. constructor. eauto using mstep_step.
  - destruct (IHM _ _ D E) as [-> | (M''&IH1&IH2)].
    + now left.
    + right. exists (orelim M'' N1 N2). split; [now constructor|].
      eauto using mstep_orelim.
  - right. exists (orelim M' t2 N2). split.
    + now constructor.
    + eauto using mstep_orelim, mstep_step.
  - right. exists (orelim M' N1 u2). split.
    * now constructor.
    * eauto using mstep_orelim, mstep_step.
  - inv D.
  - inv D.
  - inv E. right. exists (inst (s0 .: ids) N1). split.
    + constructor; auto. inv H. now apply H.
    + apply mstep_beta; eauto using mstep_step.
  - right. exists (inst (s .: ids) t2). split.
    + constructor; eauto. inv H0. now apply H0.
    + apply mstep_beta; eauto using mstep_step.
  - right.  exists (inst (s .: ids) N1). split.
    + constructor; auto. inv H1. now apply H1.
    + constructor.
  - now left.
  - inv E. right. exists (inst (s0 .: ids) N2). split.
    + constructor; auto. inv H. now apply H.
    + apply mstep_beta; eauto using mstep_step.
  - right. exists (inst (s .: ids) N2). split.
    + constructor; auto. inv H0. now apply H0.
    + constructor.
  - right. exists (inst (s .: ids) u2). split.
    + constructor; auto. inv H1. now apply H1.
    + apply mstep_beta; eauto using mstep_step.
  - now left.
Qed.

Lemma redsn_backwards g A (M M': tm g A):
 redsn M M' -> sn M' -> sn M.
Proof.
 induction 1 as [|g A B M M' N H IH|g A B C M M' N1 N2 H IH|g A B C s t t' u h1 h2 h3|g A B C s t u u' h1 h2 h3].
 - intros D. eapply fundamental_backwards; eauto.
 - intros D. specialize (IH (sn_appL D)).
   assert (sn_N: sn N) by (now apply closed_appR in D).
   revert M IH M' D H.
   induction sn_N as [N sn_N IH_N]. induction 1 as [M sn_M IH_M].
   constructor. intros M_N C. inv C.
   + inv H.
   + destruct (sn_confluence H C) as [E|(M'''&C1&C2)].
     * now subst.
     * eapply IH_M with (M' := M'''); eauto.
       eapply sn_mstep; [|eassumption]. eapply mstep_app; eauto.
   + eapply IH_N; eauto.
     * now constructor.
     * inv D. apply H. now constructor.
 - intros D.
   destruct (closed_orelim D) as (D1%IH&D2&D3). clear IH.
   revert N1 D2 N2 D3 M' H D.
   induction D1 as [M snM IHM].
   induction 1 as [N1 snN1 IHN1].
   induction 1 as [N2 snN2 IHN2].
   constructor. intros M'' E. inv E.
   + destruct (sn_confluence H E) as [F|(M''&F1&F2)].
     * now subst.
     * apply IHM with (M' := M''); eauto. now constructor. now constructor.
       eapply sn_mstep; [|eassumption]. eapply mstep_orelim; eauto.
   + eapply IHN1; eauto. now constructor. inv D. apply H0. now constructor.
   + eapply IHN2; eauto. inv D. eapply H0. now constructor.
   + inv H.
   + inv H.
 - subst. intros H'. now apply fundamental_backwards_orl.
 - subst. intros H'. now apply fundamental_backwards_orr.
Qed.
