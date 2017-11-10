(** * Proof of Strong Normalisation *)

From mathcomp Require Import ssreflect.all_ssreflect.
Require Import axioms fintype graded stlc ARS.
Set Implicit Arguments.
Unset Strict Implicit.

(** This is a simple implementation of the rewriting technique of Autosubst. *)
Local Ltac asimpl :=
  repeat progress (cbn; fsimpl; gsimpl; tm_simpl).
Ltac inv H := inversion H; subst; clear H.

(** ** One-Step Reduction *)
Inductive step {n} : tm n -> tm n -> Prop :=
| step_beta (T : ty) (M : tm n.+1) (N : tm n) :
    step (Tm.app (Tm.lam T M) N) M.[N .: Tm.var]%tm
| step_appL M N M' :
    step M M' -> step (Tm.app M N) (Tm.app M' N)
| step_appR M N N' :
    step N N' -> step (Tm.app M N) (Tm.app M N')
| step_abs T M M' :
    @step n.+1 M M' -> step (Tm.lam T M) (Tm.lam T M').

Lemma step_ebeta {n} T M N (M' : tm n) :
  M' = M.[N .: Tm.var]%tm -> step (Tm.app (Tm.lam T M) N) M'.
Proof. move->. exact: step_beta. Qed.

Module Reduction.
Lemma substitutivity {n1 n2} (sigma : fin n1 -> tm n2) M M' :
  step M M' -> step M.[sigma]%tm M'.[sigma]%tm.
Proof.
  move=> H. elim: H n2 sigma => {n1 M M'}; asimpl; eauto using @step.
  - move=> n1 T M M' n2 sigma. apply: step_ebeta. by asimpl.
Qed.

Lemma naturality m n (M: tm m) (rho: fin m -> fin n) M' :
  step (M ◁ rho)%tm M' -> exists M'', step M M'' /\ M' = (M'' ◁ rho)%tm.
Proof.
  elim: M n rho M' => {m}.
  - move=>m x n rho M H. inv H.
  - move=>m M1 IHM1 M2 IHM2 n rho M H. inv H.
    + assert (exists s1', M1 = Tm.lam T s1' ) as [s1' B].
      { destruct M1; simpl in *; try congruence; eauto. inversion H1. subst. eauto. }
      subst.
      exists (s1'.[M2 .: Tm.var])%tm. split.
      * constructor.
      * revert H1. asimpl. intros H1. inv H1. asimpl. reflexivity.
    + destruct (IHM1 _ _ _ H3) as (M1'&IH11&IH12). subst.
      exists (Tm.app M1' M2). split. constructor. assumption.
      reflexivity.
    + destruct (IHM2 _ _ _ H3) as (M2'&IH21&IH22).
      subst. exists (Tm.app M1 M2').  split. now constructor. reflexivity.
  - move => m S M IHM n rho T H. inv H.
    destruct (IHM _ _ _ H3) as (N'&IH1&->).
    exists (Tm.lam S N'). split=>//. by apply: step_abs.
Qed.
End Reduction.

(** ** Many-Step Reduction *)
Definition red {n} := star (@step n).

Definition sred {n k} (sigma tau : fin n -> tm k) :=
  forall x, @red k (sigma x) (tau x).

Module ManyStepReduction.
Lemma red_app {n} (M M' N N' : tm n) :
  red M M' -> red N N' -> red (Tm.app M N) (Tm.app M' N').
Proof.
  move=> T B. apply: (star_trans (Tm.app M' N)).
  - apply: (star_hom (@Tm.app n^~ N)) T => x y. exact: step_appL.
  - apply: star_hom B => x y. exact: step_appR.
Qed.

Lemma red_abs {n} T (M M' : tm n.+1) :
  red M M' -> red (Tm.lam T M) (Tm.lam T M').
Proof. apply: star_hom => x y. exact: step_abs. Qed.

Lemma red_inst {n1 n2} (f : fin n1 -> tm n2) s t :
  red s t -> red s.[f]%tm t.[f]%tm.
Proof. apply: star_hom => x y. exact: Reduction.substitutivity. Qed.

Lemma red_compat {n1 n2} (f1 f2 : fin n1 -> tm n2) s :
  sred f1 f2 -> red s.[f1]%tm s.[f2]%tm.
Proof.
  elim: s n2 f1 f2; intros; asimpl; eauto using red_app,red_abs.
  - apply: red_abs. apply: H. hnf=>/= -[i|]//=. asimpl. rewrite Tm.embed [(_ ◁ (_))%tm]Tm.embed.
    apply: red_inst. exact: H0.
Qed.

Lemma red_beta {n} s (N N' : tm n) :
  step N N' -> red s.[N .: Tm.var]%tm s.[N' .: Tm.var]%tm.
Proof. move=> h. apply: red_compat => /=-[i|]/=; [exact: starR|exact: star1]. Qed.

End ManyStepReduction.
Import ManyStepReduction.

(** ** Strong Normalisation *)
Notation sn := (sn (@step _)).
Module SN.
Lemma closed_app {n} (t s : tm n) :
  sn (Tm.app s t) -> sn s.
Proof. apply: (sn_preimage (h := @Tm.app n^~t)) => x y. exact: step_appL. Qed.

Lemma substitutivity {n1 n2} (f : fin n1 -> tm n2) s :
  sn s.[f]%tm -> sn s.
Proof. apply: sn_preimage. exact: Reduction.substitutivity. Qed.

(** *** Lemma 2.4 - SN Closure under Weakening *)
Lemma weak k (M: tm k) k' (rho : fin k -> fin k'):
  sn M -> sn (M ◁ rho)%tm.
Proof.
  move=> H. move: k' rho. elim: H => x H IH k' rho.
  apply: SNI. move => x' A.
  destruct (Reduction.naturality A) as (x''&B1&B2); subst.
  by apply: IH.
Qed.
End SN.

(** ** Syntactic typing *)
Definition ctx n := fin n -> ty.
Inductive has_type {n} (Gamma : ctx n) : tm n -> ty -> Prop :=
| ty_var (x : fin n) :
    has_type Gamma (Tm.var x) (Gamma x)
| ty_abs (T S : ty) (M : tm n.+1) :
    @has_type n.+1 (T .: Gamma) M S ->
    has_type Gamma (Tm.lam T M) (arr T S)
| ty_app (T S : ty) (M N : tm n) :
    has_type Gamma M (arr T S) ->
    has_type Gamma N T ->
    has_type Gamma (Tm.app M N) S.
Notation "Gamma |- M :' T" := (has_type Gamma M T) (at level 20).
Definition ltc {k k'} (Gamma: ctx k) (Delta: ctx k') rho := forall x, Delta (rho x) = Gamma x.

Module Typing.
Lemma typing_ren n k (Gamma: ctx n) (Delta: ctx k) (rho: fin n -> fin k) (M: tm n) T :
  ltc Gamma Delta rho  -> Gamma |- M :' T ->  Delta |- (M ◁ rho)%tm :' T.
Proof.
  move => H B. elim: B k rho Delta H  => {n Gamma M T} n Gamma; [move => x|move => S T M A IH |move =>S T M N A IHA B IHB]; move => k rho Delta H.
  - rewrite -H. apply: ty_var.
  - asimpl. apply: ty_abs. apply: IH.
    move=> [x|] //. asimpl. apply: H.
  - apply: ty_app; [exact: IHA _ _ H| exact: IHB _ _ H].
Qed.

Lemma typing_inst n k (Gamma: ctx n) (Delta: ctx k) (sigma: fin n -> tm k) (M: tm n) T :
  (forall x, Delta |- sigma x :' Gamma x) -> Gamma |- M :' T ->  Delta |- (M.[sigma])%tm :' T.
Proof.
  move => A B. elim: B k sigma Delta A => {n Gamma M T} n Gamma; [move => x|move => S T M A IH |move =>S T M N A IHA B IHB]; move => k sigma Delta H.
  - apply: H.
  - asimpl. apply: ty_abs. apply: IH.
    move=> [x|]. asimpl. apply: typing_ren =>//. apply: ty_var.
  - apply: ty_app; [exact: IHA _ _ H| exact: IHB _ _ H].
Qed.

Lemma step_typing k (Gamma: ctx k) M T :
  Gamma |- M :' T -> forall M', step M M' -> Gamma |- M' :' T.
Proof.
  induction 1 as [k Gamma x | k Gamma T S M A IHA | k Gamma T S M N A IHA B IHB]; intros M' H; cbn.
  - inv H.
  - inv H. econstructor. now apply IHA.
  - inv H.
    + inv A. eapply typing_inst; try eassumption.
      intros [i|]; [econstructor | assumption].
    + apply: ty_app. by apply: IHA. by [].
    + apply: ty_app.
      * exact: A.
      * by apply: IHB.
Qed.
End Typing.
Import Typing.


(** ** The Reducibility Candidates/Logical Predicate*)
Definition cand n := tm n -> Prop.

Fixpoint L {k} (Gamma: ctx k) (T: ty) : cand k :=
  match T with
  |Base => fun M => Gamma |- M :' T /\ sn M
  |arr T1 T2 => fun M => Gamma |- M :' arr T1 T2 /\
                     (forall k' (N: tm k') (Delta: ctx k') rho, ltc Gamma Delta rho -> L Delta T1 N -> L Delta T2 (Tm.app (M ◁ rho)%tm N))
  end.

Lemma L_typing {k} (Gamma: ctx k) (T: ty) M :
  L Gamma T M -> Gamma |- M :' T.
Proof. move=> H. destruct T; simpl in *; intuition. Qed.

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
    + intros k' N Delta rho H H0. apply IHS with (M := Tm.app (M ◁ rho)%tm N).
      * econstructor. rewrite Tm.embed. rewrite (Tm.embed _ _ M'). now apply Reduction.substitutivity.
      * apply: H2 => //.
Qed.

Lemma preservation_red {k} (Gamma : ctx k) M M' T :
  red M M' -> L Gamma T M -> L Gamma T M'.
Proof. move=> H. elim: H; eauto using preservation. Qed.

Lemma ren k k' (Gamma: ctx k) (Delta: ctx k') rho M T (Gamma_Delta : ltc Gamma Delta rho):
  L Gamma T M -> L Delta T (M ◁ rho)%tm.
Proof.
  elim:T => [|T IHT S IHS] [H1 H2]; split; try apply typing_ren with (Gamma := Gamma) =>//.
  - now apply SN.weak.
  - move => k'' N Delta' rho' A1 A2. asimpl. apply H2 =>// i.
    rewrite <- Gamma_Delta. now rewrite A1.
Qed.

Definition neutral k (M: tm k) :=
  match M with
  |Tm.lam _ _ => False
  |_ => True
  end.

(** Girard's theorem. *)
Lemma Girard k (Gamma: ctx k) (M : tm k) T :
  (L Gamma T M -> sn M) /\ (Gamma |- M :' T -> neutral M -> (forall N, step M N -> L Gamma T N) -> L Gamma T M).
Proof.
  revert k M Gamma. induction T as [|T IHT S IHS]; intros k M Gamma; simpl in *.
  - intuition. constructor. intros N H'. firstorder.
  - split.
    + intros [H1 H2].
      have A:  L (T .: Gamma) S (Tm.app (M ◁ shift)%tm (Tm.var k.+1 None)).
      { apply H2 => //. apply IHT =>//. constructor. intros N H. inv H. }
      rewrite Tm.embed in A.
      now apply IHS, SN.closed_app, SN.substitutivity in A.
    + intros H0 H1 H2. split =>//.
      intros k' N Delta rho H3 H4.
      have SN_N : sn N by firstorder.
      induction SN_N as [N sn_N IHN].
      apply IHS =>//.
      * rewrite Tm.embed. eapply ty_app.
        -- eapply typing_inst; try eassumption.
           intros x =>/=. rewrite <- H3. constructor.
        -- auto using L_typing.
      * intros M' A. inv A.
        -- destruct M; simpl in *; try congruence. contradiction.
        -- destruct (Reduction.naturality H7) as [M'' [H' ->]]. now apply H2.
        -- apply IHN =>//. eapply preservation; eassumption.
Qed.

Lemma sn k (Gamma: ctx k) (M : tm k) T:
  L Gamma T M -> sn M.
Proof.
  intros H. eapply Girard. eassumption.
Qed.

Lemma var k (Gamma: ctx k) x :
  L Gamma (Gamma x) (Tm.var k x).
Proof. apply Girard =>//. apply: ty_var. move => N H. inv H. Qed.

End L.

(** ** Closure under beta expansion and the fundamental theorem *)

Module StrongNormalisation.

Lemma beta_closure k Gamma (N: tm k) T (N_ty : Gamma |- N :' T) :
  sn N -> forall S M, (T .: Gamma) |- M :' S ->  L Gamma S (M.[N .: Tm.var])%tm -> L Gamma S (Tm.app (Tm.lam T M) N).
Proof.
  induction 1 as [N H IH_N]. intros S M M_ty H'.
  have sn_M := SN.substitutivity (L.sn H'). induction sn_M as [M sn_M IH_M].
  apply L.Girard =>//.
  - by repeat econstructor.
  - intros M' H1. inv H1 =>//.
    + inv H4. apply IH_M; eauto using step_typing, L.preservation, Reduction.substitutivity.
    + apply IH_N; eauto using step_typing, L.preservation_red, red_beta.
Qed.

Theorem fundamental_theorem k (Gamma: ctx k) M T :
  Gamma |- M :' T -> forall k' (Gamma': ctx k') sigma,  (forall x,  L Gamma' (Gamma x) (sigma x)) -> L Gamma' T (M.[sigma])%tm.
Proof.
  induction 1 as [| k Gamma T S M H IH | k Gamma T S M N A IHA B IHB]; intros k' Gamma' sigma adm; asimpl.
  - apply adm.
  - have M_ty :  (T .: Gamma') |- (M.[Tm.var k'.+1 bound .: sigma >> th1 shift])%tm :' S.
    { have A: forall x, Gamma' |- sigma x :' Gamma x by auto using L_typing.
      apply typing_inst with (Gamma := T .: Gamma) =>//.
      intros [i|]; [|apply: ty_var]. asimpl. apply typing_ren with (Gamma := Gamma') =>//.  }
    split.
    + now apply ty_abs.
    + intros k'0 N Delta rho A B.
      apply beta_closure; eauto using L_typing, L.sn.
      * apply typing_ren with (Gamma := T .: Gamma'); [intros [i|]; simpl; congruence | assumption] .
      * asimpl. apply IH.
        intros [i|] =>//=. rewrite <- Tm.embed. apply L.ren with (Gamma := Gamma') =>//.
  - destruct (IHA _ _ _ adm) as [IHA1 IHA2]. specialize (IHB _ _ _ adm).
    have -> : (M.[sigma])%tm = ((M.[sigma])%tm ◁ id)%tm by now asimpl.
    now apply IHA2.
Qed.

Corollary strong_normalisation k (Gamma: ctx k) M T :
  Gamma |- M :' T -> sn M.
Proof.
  intros A. apply L.sn with (Gamma := Gamma) (T := T).
  enough (H: L Gamma T  (M.[Tm.var])%tm) by now (revert H; asimpl).
  apply fundamental_theorem with (Gamma := Gamma); auto using L.var.
Qed.
End StrongNormalisation.
