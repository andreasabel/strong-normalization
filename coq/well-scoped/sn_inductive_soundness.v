(** * Different Characterisations Strong Normalisation *)

From mathcomp Require Import ssreflect.all_ssreflect.
Require Import axioms fintype graded stlc ARS sn.
Set Implicit Arguments.
Unset Strict Implicit.

(** This is a simple implementation of the rewriting technique of Autosubst. *)
Local Ltac asimpl :=
  repeat progress (cbn; fsimpl; gsimpl; tm_simpl).
Ltac inv H := inversion H; subst; clear H.

(** ** Closure Properties of sn *)
Lemma closed_lam {n} T (s : tm n.+1) :
  sn (Tm.lam T s) <-> sn s.
Proof.
  split.
  - eapply sn_preimage. exact: step_abs.
  - induction 1 as [M H IH].
    constructor. intros M' A. inv A. auto.
Qed.

Lemma closed_appR {n} (M N : tm n) :
  sn (Tm.app M N) -> sn N.
Proof. eapply sn_preimage. exact: step_appR. Qed.

(* Weak Head Reduction *)
Inductive redsn {n} :  tm n -> tm n -> Prop :=
 | redsn_beta T M (N: tm n) : sn N -> redsn (Tm.app (Tm.lam T M) N) (M.[N.:Tm.var])%tm
 | redsn_app (R R' M : tm n) : redsn R R' -> redsn (Tm.app R M) (Tm.app R' M).

Lemma redsn_step {n} (M N : tm n) :
  redsn M N -> step M N.
Proof. induction 1; now repeat econstructor. Qed.

(* destruct *)
Lemma sn_red k (M M' : tm k):
  sn M -> red M M' -> sn M'.
Proof. intros A. induction 1; auto. inv IHstar; auto. Qed.

Lemma fundamental_backwards n M T (N: tm n):
   sn N -> sn (M.[N.: Tm.var])%tm -> sn (Tm.app (Tm.lam T M) N).
Proof.
  intros sn_N sn_M'. remember (M.[N.: Tm.var])%tm as M'.
  revert M' sn_M' T M HeqM'. induction sn_N as [N sn_N IH_N].
  intros M' sn_M'; revert N sn_N IH_N. induction sn_M' as [M' sn_M' IH_M']; intros N sn_N IH_N T M A; subst.
  constructor. intros M' A. inv A.
   + now constructor.
   + inv H2. eapply IH_M'; eauto using Reduction.substitutivity.
   + eapply IH_N; [assumption| |reflexivity].
     eauto using sn_red, SNI, ManyStepReduction.red_beta.
Qed.

Lemma sn_confluence {k} (M: tm k):
  forall M' M'', redsn M M' -> step M M'' -> M' = M'' \/ exists M''', redsn M'' M''' /\ red M' M'''.
Proof.
  induction M as [x | T M IHM | M1 IHM1 M2 IHM2]; intros M' M'' A B; inv A; inv B.
  - now left.
  - inv H3. right. eexists. split.
    + now constructor.
    + apply ManyStepReduction.red_inst. unfold red. eauto using star.
  - right. eexists. split. econstructor. inv H2; eauto. now apply ManyStepReduction.red_beta.
  - inv H2.
  - destruct (IHM _ _ H2 H3) as [IH|(M''&IH1&IH2)].
    + subst. now left.
    + right. eexists. split.
      * econstructor. eassumption.
      * eapply ManyStepReduction.red_app. assumption. constructor.
  - right. eexists. split.
    + constructor. eassumption.
    + eapply ManyStepReduction.red_app. constructor. unfold red. eauto using star.
Qed.

Lemma redsn_backwards {k} (M M': tm k):
  redsn M M' -> sn M' -> sn M.
Proof.
 intros H. induction H as [|M M' N A IHA].
 - now apply fundamental_backwards.
 - intros B. specialize (IHA (SN.closed_app B)).
   assert (sn_N: sn N) by (now apply closed_appR in B).
   revert M IHA M' A B. induction sn_N as [N sn_N IH_N].
   induction 1 as [M sn_M IH_M].
   constructor. intros M_N C. inv C.
   + inv A.
   + destruct (sn_confluence A H2) as [C|(M'''&C1&C2)].
     * now subst.
     * eapply IH_M; eauto.
       eapply sn_red. exact B. eapply ManyStepReduction.red_app. assumption. constructor.
 - eapply IH_N; eauto.
   + now constructor.
   + inv B. apply H. now constructor.
Qed.

(** ** Definition à la van Raamsdonk *)

Inductive SNe : forall n, tm n -> Prop :=
 |SNe_var n (x: fin n)  : SNe (Tm.var x)
 |SNe_app n (R M: tm n) : SNe R -> SN M -> SNe (Tm.app R M)
 with
 SN : forall n, tm n -> Prop :=
 | SN_lam n (M: tm n .+1) T: SN M -> SN (Tm.lam T M)
 | SN_SNe n (M: tm n) : SNe M -> SN M
 | SN_step n (M M': tm n) : redSN M M' ->  SN M' -> SN M
 with
 redSN : forall n, tm n -> tm n -> Prop :=
 | redSN_beta n T M (N: tm n) : SN N -> redSN (Tm.app (Tm.lam T M) N) (M.[N.:Tm.var])%tm
 | redSN_app n (R R' M : tm n) : redSN R R' -> redSN (Tm.app R M) (Tm.app R' M).


(** ** Direction SN -> sn *)

(* Other definition of neutral. *)

(* Als rekursive Definition aufschreiben. *)
Inductive neutral {n} : tm n -> Prop :=
  | neutralVar x: neutral (Tm.var x)
  | neutralApp M N : neutral M -> neutral (Tm.app M N).

Lemma neutral_preservation {n} (M N: tm n):
  neutral  M -> step M N ->  neutral N.
Proof. intros A. induction 1; inv A; try constructor; auto. inv H0. Qed.

(* INduction SN? *)
Lemma sn_app_neutral {n} (N : tm n) :
   sn N -> forall M, neutral M -> sn M -> sn (Tm.app M N).
Proof.
  induction 1 as [N sn_N IH_N].
  induction 2 as [M sn_M IH_M].
  constructor. intros M' A. inv A.
  - inv H.
  - eauto using neutral_preservation.
  - eauto using SNI.
Qed.

(* Generated Induction Principle of Coq *)
Scheme SNe_ind_2 := Minimality for SNe Sort Prop
                    with SN_ind_2  := Minimality for SN Sort Prop
                                      with redSN_ind_2 := Minimality for redSN Sort Prop.

Combined Scheme SN_multind from SN_ind_2, SNe_ind_2, redSN_ind_2.

Lemma SN_sn :
  (forall k (M: tm k), SN M -> sn M) /\ (forall k (M: tm k), SNe M -> sn M /\ neutral M)
/\ (forall k (M: tm k) M', redSN M M' -> redsn M M') .
Proof.
  apply SN_multind; intros.
  - split.
    + constructor. intros M H. inv H.
    + now constructor.
  - split.
    + now apply sn_app_neutral.
    + now constructor.
  - now apply closed_lam.
  - intuition.
  - eapply redsn_backwards; eassumption.
  - now constructor.
  - now constructor.
Qed.
