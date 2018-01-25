Require Import base contexts stlc reduction.

Inductive SN : forall g A, tm g A -> Prop :=
| SNeu g A (M: tm g A): SNe M -> SN M
| SAbs g A B (M: tm (A ::g) B) : SN M -> SN (lam M)
| SRed g A (M M': tm g A): SNRed M M' -> SN M' -> SN M
with SNe : forall g A, tm g A -> Prop :=
| SVar g A (x: at_ty g A) : SNe (var x)
| SApp g A B (R: tm g (Fun A B)) M : SNe R -> SN M -> SNe (app R M)
with SNRed : forall g A, tm g A -> tm g A -> Prop :=
| SBeta g A B (M : tm (A :: g) B) N M': SN N -> M' = inst (N .: ids) M -> SNRed (app (lam M) N) M'
| SAppl g A B (R R': tm g (Fun A B)) M : SNRed R R' -> SNRed (app R M) (app R' M).

Scheme SN_ind_2 := Minimality for SN Sort Prop
                   with SNe_ind_2  := Minimality for SNe Sort Prop
                    with redSN_ind_2 := Minimality for SNRed Sort Prop.
Combined Scheme SN_multind from SN_ind_2, SNe_ind_2, redSN_ind_2.

Ltac invTm :=
match goal with
|[_ : var _ = rinst ?R ?M' |- _] => inv M'; simpl in *; try congruence
|[_ : lam _ = rinst ?R ?M' |- _] => inv M'; simpl in *; try congruence
|[_ : app _ _ = rinst ?R ?M' |- _] => inv M'; simpl in *; try congruence
|[H: lam _ = lam _ |- _] => inv H
|[H: app _ _ = app _ _|- _] => inv H
|[H: var _ = var _|- _] => inv H
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
Qed.

Lemma rename :
  (forall g A (M: tm g A), SN M -> forall g' (R: ren g g'), SN (rinst R M)) 
  /\   (forall g A (M: tm g A),  SNe M -> forall g' (R: ren g g'), SNe (rinst R M))
  /\ (forall g  A (M N: tm g A), SNRed M N -> forall g' (R: ren g g'), SNRed (rinst R M) (rinst R N)). 
Proof.
  apply SN_multind; eauto using SN, SNe, SNRed.  
  - intros. subst. constructor. auto. now asimpl. 
Qed.

Lemma ext_SN g A B (M: tm g (Fun A B)) (p: at_ty g A) :
  SN (app M (var p)) -> SN M.
Proof.
  intros H. remember (app M (var p)) as Mp. revert A M p HeqMp.
  induction H; intros; subst.
  - inv H. now constructor.
  - inv HeqMp.
  - inv H.
    + apply SAbs. eapply anti_rename. exact H0.
      instantiate (1 := p .: idren). rewrite rinst_inst. asimpl. reflexivity.  
    + eapply SRed. exact H. eapply IHSN. reflexivity.
Qed.

(** ** Logical Relation *)

Fixpoint Red (g : ctx) (A : ty) : tm g A -> Prop :=
  match A with
  | Base => fun s => SN s
  | Fun A B => fun s =>
      forall g' (S : ren g g') (t : tm g' A), Red t -> Red (app (rinst S s) t)
  end.

Definition RedS g g' (S: subst g g') :=
  forall B i, Red (S B i).

Lemma rename_red G1 G2 A (f : ren G1 G2) (s : tm G1 A) :
  Red s -> Red (rinst f s).
Proof.
  case: A s => [|A B] s /=. { intros H. now apply rename. }
  move=> H G3 g t lt. rewrite rinst_comp. exact: H.
Qed.

Lemma rename_redS g g' h  (R: ren g' h) (S: subst g g'):
  RedS S  -> RedS (S >> @rinst _ _ R).
Proof. intros H A s. now apply rename_red. Qed.

Lemma cr A:
  (forall g (M: tm g A), Red M -> SN M) /\ (forall g (M: tm g A), SNe M -> Red M) /\ (forall g (M M': tm g A), SNRed M M' -> Red M' -> Red M).
Proof.
  induction A as [|A IHA B IHB].
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
Qed.

Lemma red_var g A (p: at_ty g A):
  Red (var p).
Proof. apply cr, SVar. Qed.

Lemma main_lemma g g' A (M: tm g A) (S: subst g g'):
  RedS S -> Red (inst S M).
Proof.
  revert g' S. induction M as [p | g A B M IHM N IHN |g A B M IHM]; intros g' S rs.
  - apply rs.
  - specialize (IHM _ _ rs g' idren _ (IHN _ _ rs)). revert IHM. now asimpl.
  - intros g'' R N rn. eapply cr.
    + econstructor; [now apply cr| reflexivity].
    + asimpl. eapply IHM. intros C [->|].
      * apply rn.
      * simpl. rewrite <- rinst_inst. now apply rename_redS.
Qed.

Lemma id_red g : @RedS g g ids.
Proof. intros A p. now apply red_var. Qed.

Lemma norm g A (M: tm g A) : SN M.
Proof. rewrite <- inst_ids. apply cr, main_lemma, id_red. Qed.