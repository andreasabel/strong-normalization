Require Import base contexts stlc reduction sn_defs sn_inductive_2a.

(** ** Logical Relation *)
Inductive closure g A (R:  tm g A -> Prop) : tm g A -> Prop :=
|CRefl (M: tm g A) : R M -> closure R M
|CNeutral (M: tm g A) : SNe M -> closure R M
|CStep (M M': tm g A) : closure R M' -> SNRed M M' -> closure R M.

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

Lemma cr A: (forall g (M: tm g A), Red M -> SN M) /\ (forall g (M: tm g A), SNe M -> Red M) /\ (forall g (M M': tm g A), SNRed M M' -> Red M' -> Red M).
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

Lemma red_var g A (p: at_ty g A): Red (var p).
Proof. apply cr, SVar. Qed.

Lemma up_redS g g' A (S : subst g g'):
  RedS S -> RedS (up (A := A) S).
Proof.
  intros H B i. destruct i; subst.
  - simpl. apply red_var.
  - simpl. apply rename_red, H.
Qed.

Lemma main_lemma g g' A (M: tm g A) (S: subst g g'): RedS S -> Red (inst S M).
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
