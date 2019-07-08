Require Import stlc reduction sn_defs.

Ltac invTm :=
match goal with
|[_ : var_tm _ = ren_tm ?R ?M' |- _] => inv M'; simpl in *; try congruence
|[_ : lam _ _ = ren_tm ?R ?M' |- _] => inv M'; simpl in *; try congruence
|[_ : app _ _ = ren_tm ?R ?M' |- _] => inv M'; simpl in *; try congruence
|[H: lam _ _ = lam _ _ |- _] => inv H
|[H: app _ _ = app _ _|- _] => inv H
|[H: ids _ = ids _|- _] => inv H
|[_ : inl _ = ren_tm ?R ?M' |- _] => inv M'; simpl in *; try congruence
|[_ : inr _ = ren_tm ?R ?M' |- _] => inv M'; simpl in *; try congruence
|[_ : orelim _ _ _  = ren_tm ?R ?M' |- _] => inv M'; simpl in *; try congruence
|[H: inl _ = inl _ |- _] => inv H
|[H: inr _ = inr _ |- _] => inv H
|[H: orelim _ _  _ = orelim _ _ _ |- _] => inv H
end.

Hint Constructors SN SNe SNRed.

Lemma anti_rename:
  (forall n (M: tm n), SN M -> forall n' M' (R: fin n' -> fin n), M = ren_tm R M' -> SN M')
 /\ (forall n (M: tm n), SNe M -> forall n' M' (R: fin n' -> fin n), M = ren_tm R M' -> SNe M')
 /\ (forall n (M N: tm n), SNRed M N -> forall n' (R: fin n' -> fin n) M', M = ren_tm R M' -> exists N', N = ren_tm R N' /\ SNRed M' N').
Proof.
  apply SN_multind; intros; repeat invTm; asimpl in *; subst; eauto.
  - destruct (H0 _ _ _ (eq_refl _)) as (M''&->&?).
    eapply SRed; eauto.
  - destruct M'; simpl in *; try congruence.
    inv H; now constructor.
  - exists (M'0_1 [M'0_2..]).
    split. now asimpl. constructor; eauto.
  - destruct (H0 _ _ _ (eq_refl (ren_tm R0 M'1))) as (N'&->&A2).
    exists (app N' M'2). split; [reflexivity| now constructor].
  - destruct (H0 _ _ _ (eq_refl (ren_tm R M'0_1))) as (N'&->&A2).
    exists (orelim N' M'0_2 M'0_3). split; [reflexivity|now constructor].
  - exists (M'2 [M'1..]). split.
    + now asimpl.
    + constructor; [| | | reflexivity].
      * now eapply H0.
      * now eapply H2.
      * now eapply H4.
  - exists (M'3 [M'1..]). split.
    + now asimpl.
    + constructor; [| | |reflexivity].
      * now eapply H0.
      * now eapply H2.
      * now eapply H4.
Qed.

Lemma rename :
  (forall n (M: tm n), SN M -> forall n' (R: fin n -> fin n'), SN (ren_tm R M))
  /\   (forall n (M: tm n),  SNe M -> forall n' (R: fin n -> fin n'), SNe (ren_tm R M))
  /\ (forall n (M N: tm n), SNRed M N -> forall n' (R: fin n -> fin n'), SNRed (ren_tm R M) (ren_tm R N)).
Proof.
  apply SN_multind; intros; asimpl in *; eauto.
  - constructor.
  - intros. subst. constructor. auto. now asimpl.
  - intros. subst. constructor. auto. auto. auto. now asimpl.
  - intros. subst. constructor. auto. auto. auto. now asimpl.
Qed.

Lemma ext_SN n (M: tm n) (p: fin n) :
  SN (app M (var_tm p)) -> SN M.
Proof.
  intros H. remember (app M (var_tm p)) as Mp. revert M p HeqMp.
  induction H; intros; subst.
  - inv H. now constructor.
  - inv HeqMp.
  - inv HeqMp.
  - inv HeqMp.
  - inv H.
    + apply SAbs. eapply anti_rename. exact H0.
      instantiate (1 := p..). substify. now asimpl.
    + eapply SRed. exact H. eapply IHSN. reflexivity.
Qed.
