(** * Different Characterisations Strong Normalisation *)

Require Import stlc reduction sn_defs Coq.Program.Equality.
Set Implicit Arguments.
Unset Strict Implicit.

(** ** Closure Properties of sn *)
Lemma sn_preimage {m n} (f : tm m -> tm n) (s : tm m) :
  (forall t u, step t u -> step (f t) (f u)) ->
  sn (f s) -> sn s.
Proof.
  intros H sns. dependent induction sns. apply snI. intros t st.
  eapply H0; eauto.
Qed.

Lemma sn_appL {n} (s : tm n) (t : tm n) :
  sn (app s t) -> sn s.
Proof. apply (@sn_preimage _ _ (fun s => app s t)); eauto using @step. Qed.

Lemma sn_subst_tm {m n} (f : fin m -> tm n) (s : tm m) :
  sn (subst_tm f s) -> sn s.
Proof. apply sn_preimage. apply step_inst. Qed.

Lemma closed_lam {n}  (s : tm (S n)) A:
  sn s -> sn (lam A s).
Proof.
  induction 1 as [M H IH]. constructor. intros M' C. inv C. auto.
Qed.

Lemma closed_appR n (M: tm n) (N: tm n)  :
  sn (app M N) -> sn N.
Proof. eapply sn_preimage. apply step_appR. Qed.

(* Weak Head Reduction *)
Inductive redsn : forall n,  tm n -> tm n -> Prop :=
 | redsn_beta n A (M: tm (S n)) (N: tm n) : sn N -> redsn (app (lam A M) N) (subst_tm (N.:ids) M)
 | redsn_app n (R R' : tm n) (M : tm n) : redsn R R' -> redsn (app R M) (app R' M).

Lemma fundamental_backwards n (M: tm (S n)) (N: tm n) A:
   sn N -> sn (subst_tm (N.: ids) M) -> sn (app (lam A M) N).
Proof.
  intros sn_N sn_M'.
  assert (H: sn M) by (now apply sn_subst_tm in sn_M').
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
Fixpoint neutral n (M: tm n) :=
  match M with
  | var_tm  x => True
  | app  s t => neutral s
  | _ => False
  end.

Lemma neutral_preservation n (M N: tm n):
  neutral  M -> step M N ->  neutral N.
Proof. intros H. induction 1; simpl in *; intuition. Qed.

Lemma sn_confluence n (M: tm n):
  forall M' M'', redsn M M' -> step M M'' -> M' = M'' \/ exists M''', redsn M'' M''' /\ mstep M' M'''.
Proof.
  induction M as [x | T M IHM | M1 IHM1 M2 IHM2]; intros M' M'' D E; inv D; inv E.
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
Qed.

Lemma redsn_backwards n (M M': tm n):
 redsn M M' -> sn M' -> sn M.
Proof.
 induction 1 as [|n M M' N H IH].
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

Lemma sn_app_neutral n (N : tm n) :
   sn N -> forall (M: tm n), neutral M -> sn M -> sn (app M N).
Proof.
  induction 1 as [N sn_N IH_N].
  induction 2 as [M sn_M IH_M].
  constructor. intros M' C. inv C.
  - contradiction.
  - eauto using neutral_preservation.
  - eauto using snI.
Qed.
