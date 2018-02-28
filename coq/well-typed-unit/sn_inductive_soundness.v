(** * Different Characterisations Strong Normalisation *)

Require Import base contexts stlc reduction sn_inductive.
Set Implicit Arguments.
Unset Strict Implicit.

(** ** Closure Properties of sn *)
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

(* Weak Head Reduction *)
Inductive redsn : forall g A,  tm g A -> tm g A -> Prop :=
 | redsn_beta g A B (M: tm (A :: g) B) (N: tm g A) : sn N -> redsn (app (lam M) N) (inst (N.:ids) M)
 | redsn_app g A B (R R' : tm g (Fun A B)) (M : tm g A) : redsn R R' -> redsn (app R M) (app R' M)
.

Lemma redsn_step g A (M N : tm g A) :
  redsn M N -> step M N.
Proof. induction 1; try (now repeat econstructor). Qed.

Lemma fundamental_backwards g A B (M: tm (A::g) B) (N: tm g A):
   sn N -> sn (inst (N.: ids) M) -> sn (app (lam M) N).
Proof.
  intros sn_N sn_M'.
  assert (H: sn M) by (now apply sn_inst in sn_M').
  revert M H sn_M'. induction sn_N as [N sn_N IH_N].
  induction 1 as [M sn_M IH_M]. intros H. constructor. intros M' C. inv C.
  - constructor. intros M' H'. now inv H'.
  - assumption.
  - inv C. rename b2 into M'. eapply IH_M. assumption.
    eapply sn_mstep; [exact H|]. eauto using mstep_beta, mstep_step.
  - eapply IH_N; eauto.
    + now constructor.
    + eauto using sn_mstep, snI, mstep_beta, mstep_step.
Qed.

(* Neutral terms *)
Fixpoint neutral g A (M: tm g A) :=
  match M with
  | var _ x => True
  | unit => True
  | app _ _  s t => neutral s
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
  - apply sn_unit.
  - contradiction.
  - eauto using neutral_preservation.
  - eauto using snI.
Qed.

Lemma sn_confluence g A (M: tm g A):
  forall M' M'', redsn M M' -> step M M'' -> M' = M'' \/ neutral M'' \/ (exists M''',  mstep M' M''' /\ redsn M'' M''').
Proof.
   induction M as [x | T M IHM | M1 IHM1 M2 IHM2 |]; intros M' M'' H1 H2; inv H1; inv H2; eauto.
   - right. left. intuition. reflexivity.
   - inv H2. right. right. exists (inst (M2 .: ids) b2). split.
     + eauto using mstep_beta, mstep_step.
     + now constructor.
   - right. right. exists (inst (t2 .: ids) M0). split.
     + eauto using mstep_beta, mstep_step.
     + constructor. inv H. now apply H.
   - right. left. intuition. reflexivity.
   - inv H1.
   - destruct (IHM1 _ _ H1 H2) as [-> |[E|(M''&E1&E2)]].
     + now left.
     + right. now left.
     + right. right. exists (app M'' M2). split. now eapply mstep_app. now constructor.
   - right. right. exists (app R' t2). split. eauto using mstep_step, step_appR.  now constructor.
Qed.


Lemma redsn_backwards g A (M M': tm g A):
 redsn M M' -> sn M' -> sn M.
Proof.
 induction 1 as [|g A B M M' N H IH].
 - intros D. eapply fundamental_backwards; eauto.
 - intros D. specialize (IH (sn_appL D)).
   assert (sn_N: sn N) by (now apply closed_appR in D).
   revert B M IH M' D H.
   induction sn_N as [N sn_N IH_N]. induction 1 as [M sn_M IH_M].
   constructor. intros M_N C. inv C.
   + apply sn_unit.
   + inv H.
   + rename s2 into M''. destruct (sn_confluence H C) as [E|[E|(M'''&C1&C2)]].
     * congruence.
     * eapply sn_app_neutral; eauto.
       -- now apply closed_appR in D.
     * eapply IH_M; [assumption| |eassumption].
          eapply sn_mstep. exact D. eauto using mstep_step, mstep_app.
   + eapply IH_N; eauto.
     * now constructor.
     * inv D. apply H. now constructor.
Qed.

Lemma SN_sn :
  (forall g A (M: tm g A), SN M -> sn M)
/\ (forall g A (M: tm g A), SNe M -> sn M /\ neutral M)
/\ (forall g A (M: tm g A) M', SNRed M M' -> redsn M M') .
Proof.
  apply SN_multind; intros.
  - apply sn_unit.
  - intuition.
  - now apply closed_lam.
  - eauto using redsn_backwards.
  - split; [|now constructor].
    + constructor. intros M H. inv H.
  - apply sn_unit.
  - split; [|intuition].
    + now apply sn_app_neutral.
  - subst. now constructor.
  - now constructor.
Qed.
