Require Import base contexts stlc reduction sn_defs.

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
