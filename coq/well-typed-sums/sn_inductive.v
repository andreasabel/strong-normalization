Require Import base contexts stlc reduction.

Inductive SN : forall g A, tm g A -> Prop :=
| SNeu g A (M: tm g A): SNe M -> SN M
| SAbs g A B (M: tm (A ::g) B) : SN M -> SN (lam M)
| SInl g A B (M: tm g A) : SN M -> SN (inl (B := B) M)                                                 | SInr g A B (M: tm g B) : SN M -> SN (inr (A := A) M)
| SRed g A (M M': tm g A): SNRed M M' -> SN M' -> SN M
with SNe : forall g A, tm g A -> Prop :=
| SVar g A (x: at_ty g A) : SNe (var x)
| SNeuOr g A B C (M: tm g (Plus A B)) (N1: tm (A::g) C) N2:
   SNe M -> SN N1 -> SN N2 -> SNe (orelim M N1 N2)
| SApp g A B (R: tm g (Fun A B)) M : SNe R -> SN M -> SNe (app R M)
with SNRed : forall g A, tm g A -> tm g A -> Prop :=
| SBeta g A B (M : tm (A :: g) B) N M': SN N -> M' = inst (N .: ids) M -> SNRed (app (lam M) N) M'
| SAppl g A B (R R': tm g (Fun A B)) M : SNRed R R' -> SNRed (app R M) (app R' M)
| SOr g A B C (M M' : tm g (Plus A B)) (N1 : tm (A ::g) C) N2: SNRed M M' -> SNRed (orelim M N1 N2) (orelim M' N1 N2)
| SCaseL G A B C (s: tm G A) t t' (u: tm (B :: G) C) : SN s -> SN t -> SN u -> t' = (inst (s.:ids) t) -> SNRed (orelim (inl s) t u) t'
| SCaseR G A B C (s: tm G B) (t: tm (A :: G) C) u u': SN s -> SN t -> SN u -> u' = (inst (s.:ids) u) ->  SNRed (orelim (inr s) t u) u'
.

Scheme SN_ind_2 := Minimality for SN Sort Prop
                   with SNe_ind_2  := Minimality for SNe Sort Prop
                    with redSN_ind_2 := Minimality for SNRed Sort Prop.
Combined Scheme SN_multind from SN_ind_2, SNe_ind_2, redSN_ind_2.

Ltac invTm :=
match goal with
|[_ : var _ = rinst ?R ?M' |- _] => inv M'; simpl in *; try congruence
|[_ : lam _ = rinst ?R ?M' |- _] => inv M'; simpl in *; try congruence
|[_ : app _ _ = rinst ?R ?M' |- _] => inv M'; simpl in *; try congruence
|[_ : inl _ = rinst ?R ?M' |- _] => inv M'; simpl in *; try congruence
|[_ : inr _ = rinst ?R ?M' |- _] => inv M'; simpl in *; try congruence
|[_ : orelim _ _ _  = rinst ?R ?M' |- _] => inv M'; simpl in *; try congruence
|[H: lam _ = lam _ |- _] => inv H
|[H: app _ _ = app _ _|- _] => inv H
|[H: var _ = var _|- _] => inv H
|[H: inl _ = inl _ |- _] => inv H
|[H: inr _ = inr _ |- _] => inv H
|[H: orelim _ _  _ = orelim _ _ _ |- _] => inv H
end.

Lemma anti_rename:
  (forall g A (M: tm g A), SN M -> forall g' M' (R: ren g' g), M = rinst R M' -> SN M')
 /\ (forall g A (M: tm g A), SNe M -> forall g' M' (R: ren g' g), M = rinst R M' -> SNe M')
 /\ (forall g  A (M N: tm g A), SNRed M N -> forall g' (R: ren g' g) M', M = rinst R M' -> exists N', N = rinst R N' /\ SNRed M' N').
Proof.
  apply SN_multind; intros; repeat invTm; eauto using SN, SNe, SNRed.
  - destruct (H0 _ _ _ H3) as (N'&->&A2).
    eauto using SRed.
  - exists (inst (M'0_2 .: ids) M'0_1).
    split. now asimpl. eauto using SNRed.
  - destruct (H0 _ _ _ (erefl (rinst R0 M'1))) as (N'&->&A2).
    exists (app N' M'2). split; [reflexivity| now constructor].
  - destruct (H0 _ _ _ (erefl (rinst R M'0_1))) as (N'&->&A2).
    exists (orelim N' M'0_2 M'0_3). split; [reflexivity|now constructor].
  - exists (inst (M'1 .: ids) M'2). split.
    + now asimpl.
    + constructor; [| | | reflexivity].
      * now eapply H0.
      * now eapply H2.
      * now eapply H4.
  - exists (inst (M'1 .: ids) M'3). split.
    + now asimpl.
    + constructor; [| | |reflexivity].
      * now eapply H0.
      * now eapply H2.
      * now eapply H4.
Qed.

Lemma rename :
  (forall g A (M: tm g A), SN M -> forall g' (R: ren g g'), SN (rinst R M))
  /\   (forall g A (M: tm g A),  SNe M -> forall g' (R: ren g g'), SNe (rinst R M))
  /\ (forall g  A (M N: tm g A), SNRed M N -> forall g' (R: ren g g'), SNRed (rinst R M) (rinst R N)).
Proof.
  apply SN_multind; eauto using SN, SNe, SNRed.
  - intros. subst. constructor. auto. now asimpl.
  - intros. subst. constructor. auto. auto. auto. now asimpl.
  - intros. subst. constructor. auto. auto. auto. now asimpl.
Qed.

Lemma ext_SN g A B (M: tm g (Fun A B)) (p: at_ty g A) :
  SN (app M (var p)) -> SN M.
Proof.
  intros H. remember (app M (var p)) as Mp. revert A M p HeqMp.
  induction H; intros; subst.
  - inv H. now constructor.
  - inv HeqMp.
  - inv HeqMp.
  - inv HeqMp.
  - inv H.
    + apply SAbs. eapply anti_rename. exact H0.
      instantiate (1 := p .: idren). rewrite rinst_inst. asimpl. reflexivity.
    + eapply SRed. exact H. eapply IHSN. reflexivity.
Qed.

(** ** Logical Relation *)

Inductive closure g A (R:  tm g A -> Prop) : tm g A -> Prop :=
|CRefl (M: tm g A) : R M -> closure R M
|CNeutral (M: tm g A) : SNe M -> closure R M
|CStep (M M': tm g A) : closure R M' -> SNRed M M' -> closure R M
.

Fixpoint Red (g : ctx) (A : ty) : tm g A -> Prop :=
  match A with
  | Base => fun s => SN s
  | Fun A B => fun s =>
                forall g' (S : ren g g') (t : tm g' A), Red t -> Red (app (rinst S s) t)
  | Plus A B => closure (fun M => (exists M', M = inl M' /\ Red M') \/ (exists M', M = inr M' /\ Red M'))
  end.

Definition RedS g g' (S: subst g g') :=
  forall B i, Red (S B i).

Lemma rename_red G1 A (s : tm G1 A) :
  Red s -> forall G2 (f: ren G1 G2), Red (rinst f s).
Proof.
  revert G1 s. induction A as [|A IHA B IHB|A IHA B IHB]; intros g s H G2 f; simpl in *.
  - now apply rename.
  - intros. rewrite rinst_comp. exact: H.
  - induction H.
    + apply CRefl. destruct H as [(M'&->&H2)|(M'&->&H2)]; [left|right].
      * exists (rinst f M'). split; [reflexivity|now apply IHA].
      * exists (rinst f M'). split; [reflexivity|now apply IHB].
    + eapply CNeutral. now apply rename.
    + apply CStep with (M' := rinst f M').
      * assumption.
      * apply rename. assumption.
Qed.

Lemma rename_redS g g' h  (R: ren g' h) (S: subst g g'):
  RedS S  -> RedS (S >> @rinst _ _ R).
Proof. intros H A s. now apply rename_red. Qed.

Lemma cr A:
  (forall g (M: tm g A), Red M -> SN M) /\ (forall g (M: tm g A), SNe M -> Red M) /\ (forall g (M M': tm g A), SNRed M M' -> Red M' -> Red M).
Proof.
  induction A as [|A IHA B IHB|A IHA B IHB].
  - repeat split; intros.
    + assumption.
    + now apply SNeu.
    + now apply SRed with (M' := M').
  - repeat split; intros.
    + eapply anti_rename with (R := shift) (M := rinst shift M); [|reflexivity].
      eapply ext_SN, IHB, H. apply IHA, (SVar _ A var0).
    + intros g' R N H'. apply IHB.
      * apply SApp. now apply rename.
      * intuition.
    + intros g' R N rn. apply IHB with (M' := app (rinst R M') N).
     * constructor. now apply rename.
     * apply H0, rn.
  - repeat split; intros.
    + induction H.
      * destruct H as [(M'&->&H2)|(M'&->&H2)].
        -- apply SInl. now apply IHA.
        -- apply SInr. now apply IHB.
      * now constructor.
      * now apply SRed with (M' := M').
    + now apply CNeutral.
    + simpl in H0.
      eapply CStep with (M' := M'); assumption.
Qed.

Lemma red_var g A (p: at_ty g A):
  Red (var p).
Proof. apply cr, SVar. Qed.

Lemma up_redS g g' A (S : subst g g'):
  RedS S -> RedS (up (A := A) S).
Proof.
  intros H B i. destruct i; subst.
  - simpl. apply red_var.
  - simpl. apply rename_red, H.
Qed.

Lemma main_lemma g g' A (M: tm g A) (S: subst g g'):
  RedS S -> Red (inst S M).
Proof.
  revert g' S. induction M as [p | g A B M IHM N IHN |g A B M IHM|g A B M IHM| g A B M IHM|g A B C M IHM N1 IHN1 N2 IHN2]; intros g' S rs.
  - apply rs.
  - specialize (IHM _ _ rs g' idren _ (IHN _ _ rs)). revert IHM. now asimpl.
  - intros g'' R N rn. eapply cr.
    + econstructor; [now apply cr| reflexivity].
    + asimpl. eapply IHM.  intros C [->|].
      * apply rn.
      * simpl. rewrite <- rinst_inst. now apply rename_redS.
  - specialize (IHM _ _ rs).
    constructor. left. exists (inst S M). split; [reflexivity|auto].
  - specialize (IHM _ _ rs).
    constructor. right. exists (inst S M). split; [reflexivity|auto].
  - specialize (IHM _ _ rs). simpl. remember (inst S M) as M'. clear M HeqM'.
    induction IHM.
    + destruct H as [(M'&->&H)|(M'&->&H)].
      * eapply cr.
        -- apply SCaseL; [| | |reflexivity].
           ++ now apply cr.
           ++ now apply cr, IHN1, up_redS.
           ++ now apply cr, IHN2, up_redS.
        -- asimpl. apply IHN1. intros D [|].
           ++ subst. assumption.
           ++ simpl. unfold scomp. asimpl. apply rs.
      * eapply cr.
        -- apply SCaseR; [| | |reflexivity].
           ++ now apply cr.
           ++ now apply cr, IHN1, up_redS.
           ++ now apply cr, IHN2, up_redS.
        -- asimpl. apply IHN2. intros D [|].
           ++ subst. assumption.
           ++ simpl. unfold scomp. asimpl. apply rs.
    + apply cr.
      constructor.
      * assumption.
      * now apply cr, IHN1, up_redS.
      * now apply cr, IHN2, up_redS.
    + intros. subst.
      assert (Red M') as Red_M' by apply IHM.
      simpl. apply cr with ( M' :=  (orelim M' (inst (up S) N1) (inst (up S) N2))).
      now constructor. assumption.
Qed.

Lemma id_red g : @RedS g g ids.
Proof. intros A p. now apply red_var. Qed.

Lemma norm g A (M: tm g A) : SN M.
Proof. rewrite <- inst_ids. apply cr, main_lemma, id_red. Qed.
