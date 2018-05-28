Require Import base contexts stlc reduction sn_defs sn_inductive_2a.

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
  revert s. destruct A as [| A B]; intros s; cbn.
  - intros H. now apply rename.
  - intros H G3 g t lt. rewrite rinst_comp. now apply H.
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
      apply SApp. now apply rename. now intuition.
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
