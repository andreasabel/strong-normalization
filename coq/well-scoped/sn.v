(** * Proof of Strong Normalisation *)

Require Import axioms fintype stlc ARS.
Set Implicit Arguments.
Unset Strict Implicit.

Ltac inv H := inversion H; subst; clear H.
Notation "M .[ sigma ]'" := (ren_tm sigma M) (at level 60, format "M .[ sigma ]'").
Notation "M .[ sigma ]" := (subst_tm sigma M) (at level 60, format "M .[ sigma ]").

(** ** One-Step Reduction *)
Inductive step {n} : tm n -> tm n -> Prop :=
| step_beta (T : ty) (M : tm (S n)) (N : tm n) :
    step (app (lam T M) N) (M.[N .: var_tm])
| step_appL M N M' :
    step M M' -> step (app M N) (app M' N)
| step_appR M N N' :
    step N N' -> step (app M N) (app M N')
| step_abs T M M' :
    @step (S n) M M' -> step (lam T M) (lam T M').

Lemma step_ebeta {n} T M N (M' : tm n) :
  M' = M.[N .: var_tm] -> step (app (lam T M) N) M'.
Proof. intros ->. apply step_beta. Qed.

Module Reduction.
Lemma substitutivity {n1 n2} (sigma : fin n1 -> tm n2) M M' :
  step M M' -> step (M.[sigma]) (M'.[sigma]).
Proof.
  intros H. revert n2 sigma. induction H; intros n2 sigma; asimpl; eauto using @step.
  - apply step_ebeta. now asimpl.
Qed.

Lemma naturality m n (M: tm m) (rho: fin m -> fin n) N :
  step (M.[rho]') N -> exists N', step M N' /\ N = (ren_tm rho N').
Proof.
  revert n N rho. induction M as [m x | m M1 IHM1 M2 IHM2 | m T M IHM]; intros n N rho H.
  - inv H.
  - inv H.
    + assert (exists s1', M1 = lam T s1' ) as [s1' B].
      { destruct M1; simpl in *; try congruence; eauto. inversion H1. subst. eauto. }
      subst.
      exists (s1'.[M2 .: var_tm]). split.
      * constructor.
      * revert H1. asimpl. intros H1. inv H1. asimpl. reflexivity.
    + destruct (IHM1 _ _ _ H3) as (M1'&IH11&IH12). subst.
      exists (app M1' M2). split. constructor. assumption.
      reflexivity.
    + destruct (IHM2 _ _ _ H3) as (M2'&IH21&IH22).
      subst. exists (app M1 M2').  split. now constructor. reflexivity.
  - inv H.
    destruct (IHM _ _ _ H3) as (N'&IH1&->).
    exists (lam T N'). split. now apply step_abs. reflexivity.
Qed.

End Reduction.

(** ** Many-Step Reduction *)
Definition red {n} := star (@step n).

Definition sred {n k} (sigma tau : fin n -> tm k) :=
  forall x, @red k (sigma x) (tau x).

Module ManyStepReduction.
Lemma red_app {n} (M M' N N' : tm n) :
  red M M' -> red N N' -> red (app M N) (app M' N').
Proof.
  intros T B. apply (star_trans (app M' N)).
  - eapply (star_hom (fun M => @app n M N)); [|eauto].
    + intros. eapply step_appL; exact H.
  - eapply star_hom; [|eauto]. eauto using step_appR.
Qed.

Lemma red_abs {n} T (M M' : tm (S n)) :
  red M M' -> red (lam T M) (lam T M').
Proof. apply star_hom. eauto using step_abs. Qed.

Lemma red_inst {n1 n2} (f : fin n1 -> tm n2) s t :
  red s t -> red (s.[f]) (t.[f]).
Proof. apply star_hom. eauto using Reduction.substitutivity. Qed.

Lemma red_compat {n1 n2} (f1 f2 : fin n1 -> tm n2) s :
  sred f1 f2 -> red (s.[f1]) (s.[f2]).
Proof.
  revert n2 f1 f2; induction s; intros n2 f1 f2 H; asimpl; eauto using red_app, red_abs.
  - apply red_abs, IHs. intros [i|]; [|constructor].
    apply red_inst, H.
Qed.

Lemma red_beta {n} s (N N' : tm n) :
  step N N' -> red (s.[N .: var_tm]) (s.[N' .: var_tm]).
Proof. intros h. apply red_compat. intros [i|]; [now apply starR|now apply star1]. Qed.

End ManyStepReduction.
Import ManyStepReduction.

(** ** Strong Normalisation *)
Notation sn := (sn (@step _)).
Module SN.
Lemma closed_app {n} (t s : tm n) :
  sn (app s t) -> sn s.
Proof. apply (sn_preimage (h := fun M => @app n M t)). eauto using step_appL. Qed.

Lemma substitutivity {n1 n2} (f : fin n1 -> tm n2) s :
  sn (s.[f]) -> sn s.
Proof. apply sn_preimage. apply Reduction.substitutivity. Qed.

(** *** Lemma 2.4 - SN Closure under Weakening *)
Lemma weak k (M: tm k) k' (rho : fin k -> fin k'):
  sn M -> sn (M .[rho]').
Proof.
  intros H. revert k' rho. induction H as [x H IH]; intros k' rho.
  apply SNI. intros x' A.
  destruct (Reduction.naturality A) as (x''&B1&B2); subst.
  now apply IH.
Qed.
End SN.

(** ** Syntactic typing *)
Definition ctx n := fin n -> ty.
Inductive has_type {n} (Gamma : ctx n) : tm n -> ty -> Prop :=
| ty_var_tm (x : fin n) :
    has_type Gamma (var_tm x) (Gamma x)
| ty_abs (S1 S2 : ty) (M : tm (S n)) :
    @has_type (S n) (S1 .: Gamma) M S2 ->
    has_type Gamma (lam S1 M) (arr S1 S2)
| ty_app (T S : ty) (M N : tm n) :
    has_type Gamma M (arr T S) ->
    has_type Gamma N T ->
    has_type Gamma (app M N) S.
Notation "Gamma |- M : T" := (has_type Gamma M T) (at level 20, M at level 99).
Definition ltc {k k'} (Gamma: ctx k) (Delta: ctx k') rho := forall x, Delta (rho x) = Gamma x.

Module Typing.
Lemma typing_ren n k (Gamma: ctx n) (Delta: ctx k) (rho: fin n -> fin k) (M: tm n) T :
  ltc Gamma Delta rho  -> Gamma |- M : T ->  Delta |- (M .[rho]') : T.
Proof.
  intros H B. revert k rho Delta H. induction B as [x | n Gamma T1 T2 M A IH | n Gamma T1 T2 M N A IHA B IHB]; intros k rho Delta H.
  - rewrite <- H. apply ty_var_tm.
  - apply ty_abs. apply IH.
    intros [x|]; [|constructor]. asimpl. apply H.
  - eapply ty_app; eauto.
Qed.

Lemma typing_inst n k (Gamma: ctx n) (Delta: ctx k) (sigma: fin n -> tm k) (M: tm n) T :
  (forall x, Delta |- sigma x : Gamma x) -> Gamma |- M : T ->  Delta |- (M.[sigma]) : T.
Proof.
  intros A B. revert k sigma Delta A.  induction B as [x | n Gamma T1 T2 M A IH | n Gamma T1 T2 M N A IHA B IHB]; intros k sigma Delta H.
  - apply H.
  - apply ty_abs. apply IH.
    intros [x|]; [|constructor]. eapply typing_ren; [intros y; reflexivity|apply H].
  - apply ty_app with (T := T1); eauto.
Qed.

Lemma step_typing k (Gamma: ctx k) M T :
  Gamma |- M : T -> forall M', step M M' -> Gamma |- M' : T.
Proof.
  induction 1 as [k Gamma x | k Gamma T S M A IHA | k Gamma T S M N A IHA B IHB]; intros M' H; cbn.
  - inv H.
  - inv H. econstructor. now apply IHA.
  - inv H.
    + inv A. eapply typing_inst; try eassumption.
      intros [i|]; [econstructor | assumption].
    + eapply ty_app. now apply IHA. assumption.
    + eapply ty_app.
      * exact A.
      * now apply IHB.
Qed.
End Typing.
Import Typing.


(** ** The Reducibility Candidates/Logical Predicate*)
Definition cand n := tm n -> Prop.

Fixpoint L {k} (Gamma: ctx k) (T: ty) : cand k :=
  match T with
  |Base => fun M => Gamma |- M : T /\ sn M
  |arr T1 T2 => fun M => Gamma |- M : arr T1 T2 /\
                     (forall k' (N: tm k') (Delta: ctx k') rho, ltc Gamma Delta rho -> L Delta T1 N -> L Delta T2 (app (M.[rho]') N))
  end.

Lemma L_typing {k} (Gamma: ctx k) (T: ty) M :
  L Gamma T M -> Gamma |- M : T.
Proof. intros H. destruct T; simpl in *; intuition. Qed.

Module L.

Lemma preservation {k} (Gamma : ctx k) M M' T :
  step M M' -> L Gamma T M -> L Gamma T M'.
Proof.
  revert k Gamma M M'. induction T as [|T IHT S IHS]; intros k Gamma M M' M_M' [H1 H2].
  - split.
    + eapply step_typing; eassumption.
    + inv H2. now apply H.
  - split; [|].
    + eapply step_typing; eassumption.
    + intros k' N Delta rho H H0. apply IHS with (M := app (M.[rho]') N).
      * econstructor. asimpl. now apply Reduction.substitutivity.
      * now apply H2.
Qed.

Lemma preservation_red {k} (Gamma : ctx k) M M' T :
  red M M' -> L Gamma T M -> L Gamma T M'.
Proof. intros H. induction H; eauto using preservation. Qed.

Lemma ren k k' (Gamma: ctx k) (Delta: ctx k') rho M T (Gamma_Delta : ltc Gamma Delta rho):
  L Gamma T M -> L Delta T (M .[rho]').
Proof.
  induction T as [|T IHT S IHS]; intros [H1 H2]; split; try apply typing_ren with (Gamma := Gamma); eauto.
  - now apply SN.weak.
  - intros k'' N Delta' rho' A1 A2.
    assert ((M.[rho]').[rho']' = M.[rho >> rho']') as -> by (now asimpl).
    apply H2; [|assumption].
    + intros x. now rewrite <- Gamma_Delta, <- A1.
Qed.

Definition neutral k (M: tm k) :=
  match M with
  |lam _ _ => False
  |_ => True
  end.

(** Girard's theorem. *)
Lemma Girard k (Gamma: ctx k) (M : tm k) T :
  (L Gamma T M -> sn M) /\ (Gamma |- M : T -> neutral M -> (forall N, step M N -> L Gamma T N) -> L Gamma T M).
Proof.
  revert k M Gamma. induction T as [|T1 IHT1 T2 IHT2]; intros k M Gamma; simpl in *.
  - intuition. constructor. intros N H'. firstorder.
  - split.
    + intros [H1 H2].
      assert (A:  L (T1 .: Gamma) T2 (app (M .[shift]') (@var_tm (S k) None))).
      { apply H2. intros x; reflexivity. apply IHT1. constructor. constructor. intros N H. inv H. }
      erewrite rinst_inst_tm in A; [|reflexivity].
      now eapply IHT2, SN.closed_app, SN.substitutivity in A.
     + intros H0 H1 H2. split; [assumption |].
      intros k' N Delta rho H3 H4.
      assert ( SN_N : sn N) by firstorder.
      induction SN_N as [N sn_N IHN].
      apply IHT2; try constructor.
       * erewrite rinst_inst_tm; [|reflexivity]. eapply ty_app.
         -- eapply typing_inst; try eassumption.
            intros x. rewrite <- H3. constructor.
         -- auto using L_typing.
      * intros M' A. inv A.
        -- destruct M; simpl in *; try congruence. contradiction.
        -- destruct (Reduction.naturality H7) as [M'' [H' ->]]. now apply H2.
        -- apply IHN; [assumption|]. eapply preservation; eassumption.
Qed.

Lemma sn k (Gamma: ctx k) (M : tm k) T:
  L Gamma T M -> sn M.
Proof.
  intros H. eapply Girard. eassumption.
Qed.

Lemma var_tm k (Gamma: ctx k) x :
  L Gamma (Gamma x) (var_tm x).
Proof. apply Girard; try constructor. intros N H. inv H. Qed.

End L.

(** ** Closure under beta expansion and the fundamental theorem *)

Module StrongNormalisation.

Lemma beta_closure k Gamma (N: tm k) T (N_ty : Gamma |- N : T) :
  sn N -> forall S M, (T .: Gamma) |- M : S ->  L Gamma S (M.[N .: var_tm]) -> L Gamma S (app (lam T M) N).
Proof.
  induction 1 as [N H IH_N]. intros S M M_ty H'.
  assert (sn_M := SN.substitutivity (L.sn H')). induction sn_M as [M sn_M IH_M].
  apply L.Girard; try constructor.
  - now repeat econstructor.
  - intros M' H1. inv H1; try eauto.
    + inv H4. apply IH_M; eauto using step_typing, L.preservation, Reduction.substitutivity.
    + apply IH_N; eauto using step_typing, L.preservation_red, red_beta.
Qed.

Theorem fundamental_theorem k (Gamma: ctx k) M T :
  Gamma |- M : T -> forall k' (Gamma': ctx k') sigma,  (forall x,  L Gamma' (Gamma x) (sigma x)) -> L Gamma' T (M.[sigma]).
Proof.
  induction 1 as [| k Gamma T1 T2 M H IH | k Gamma T1 T2 M N A IHA B IHB]; intros k' Gamma' sigma adm; asimpl.
  - apply adm.
  - assert ( M_ty :  (T1 .: Gamma') |- (M.[@var_tm (S k') bound .: sigma >> ren_tm shift]) : T2).
    { assert (A: forall x, Gamma' |- sigma x : Gamma x) by auto using L_typing.
      apply typing_inst with (Gamma := T1 .: Gamma); [|assumption].
      intros [i|]; [|constructor].
      -  apply typing_ren with (Gamma := Gamma'); try constructor. apply A. }
    split.
    + apply ty_abs. revert M_ty. asimpl. auto.
    + intros k'0 N Delta rho A B.
      apply beta_closure; eauto using L_typing, L.sn.
      * apply typing_ren with (Gamma := T1 .: Gamma'); [intros [i|]; simpl; congruence | ]. revert M_ty. now asimpl.
      * asimpl. apply IH.
        intros [i|]; [|assumption].
        -- unfold up_ren. fsimpl. simpl. unfold funcomp. erewrite <- rinst_inst_tm; [|reflexivity].
           eapply L.ren. apply A. apply adm.
  - destruct (IHA _ _ _ adm) as [IHA1 IHA2]. specialize (IHB _ _ _ adm).
    assert ((M.[sigma]) = ((M.[sigma]).[idren]')) as -> by now asimpl.
    apply IHA2; unfold ltc; auto.
Qed.


Corollary strong_normalisation k (Gamma: ctx k) M T :
  Gamma |- M : T -> sn M.
Proof.
  intros A. apply L.sn with (Gamma := Gamma) (T := T).
  enough (H: L Gamma T  (M.[var_tm])) by now (revert H; asimpl).
  apply fundamental_theorem with (Gamma := Gamma); auto using L.var_tm.
Qed.
End StrongNormalisation.
