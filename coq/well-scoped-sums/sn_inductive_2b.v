Require Import stlc reduction sn_defs sn_inductive_2a.

(** ** Logical Relation *)
Inductive closure {n} (R:  tm n -> Prop) : tm n -> Prop :=
|CRefl (M: tm n) : R M -> closure R M
|CNeutral (M: tm n) : SNe M -> closure R M
|CStep (M M': tm n) : closure R M' -> SNRed M M' -> closure R M.

Fixpoint Red {n} (A : ty) : tm n -> Prop :=
  match A with
  | Base => fun s => SN s
  | Fun A B => fun s =>
      forall n' (S : fin n -> fin n') (t : tm n'), Red A t -> Red B (app (ren_tm S s) t)
  | Plus A B => closure (fun M => (exists M', M = inl M' /\ Red A M') \/ (exists M', M = inr M' /\ Red B M'))
  end.

Definition RedS {n n'} (S: fin n -> tm n') (Gamma: fin n -> ty) :=
  forall i, Red (Gamma i) (S i).

Lemma rename_red m n (f : fin m -> fin n) (s : tm m) A :
  Red A s -> Red A (ren_tm f s).
Proof.
  revert s. induction A as [| A B|A IHA B IHB]; intros s; cbn.
  - intros H. now apply rename.
  - intros H n' g t lt. asimpl.  now apply H.
  - intros H. induction H.
    + apply CRefl. destruct H as [(M'&->&H2)|(M'&->&H2)]; [left|right].
      * exists (ren_tm f M'). split; [reflexivity|now apply IHA].
      * exists (ren_tm f M'). split; [reflexivity|now apply IHB].
    + eapply CNeutral. now apply rename.
    + asimpl. eapply CStep with (M'0 := ren_tm f M').
      * assumption.
      * apply rename. assumption.
Qed.

Lemma cr A:
  (forall n (M: tm n), Red A M -> SN M) /\ (forall n (M: tm n), SNe M -> Red A M) /\ (forall n (M M': tm n), SNRed M M' -> Red A M' -> Red A M).
Proof.
  induction A as [|A IHA B IHB| A IHA B IHB].
  - repeat split; intros.
    + assumption.
    + now apply SNeu.
    + now apply SRed with (M' := M').
  - repeat split; intros.
    + eapply anti_rename with (R := shift) (M := ren_tm shift M); [|reflexivity].
      eapply ext_SN, IHB. cbn in H. apply H, IHA. apply SVar with (x:= var_zero).
    + intros g' R N H'. apply IHB.
      apply SApp. now apply rename. now intuition.
    + intros g' R N rn. apply IHB with (M' := app (ren_tm R M') N).
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
      eapply CStep with (M'0 := M'); assumption.
Qed.


Lemma red_var n (p: fin n) A:
  Red A (var_tm p).
Proof. apply cr, SVar. Qed.

Hint Resolve red_var.

Definition ctx n := fin n -> ty.
Inductive has_type {n} (Gamma : ctx n) : tm n -> ty -> Prop :=
| ty_var_tm (x : fin n) :
    has_type Gamma (var_tm x) (Gamma x)
| ty_abs (S1 S2 : ty) (M : tm (S n)) :
    @has_type (S n) (S1 .: Gamma) M S2 ->
    has_type Gamma (lam S1 M) (Fun S1 S2)
| ty_app (T S : ty) (M N : tm n) :
    has_type Gamma M (Fun T S) ->
    has_type Gamma N T ->
    has_type Gamma (app M N) S
| ty_inl M A B: has_type Gamma M A -> has_type Gamma (inl M) (Plus A B)
| ty_inr M A B: has_type Gamma M B -> has_type Gamma (inr M) (Plus A B)
| ty_or M A B C N1 N2 : has_type Gamma M (Plus A B) -> @has_type (S n) (A .: Gamma) N1 C -> @has_type (S n) (B .: Gamma) N2 C -> has_type Gamma (orelim M N1 N2) C
.

Notation "Gamma |- M : T" := (has_type Gamma M T) (at level 20, M at level 99).

Lemma RedUp n n' (xi : fin n -> tm n') Gamma A:
  RedS xi Gamma -> RedS (up_tm_tm xi) (A .: Gamma).
Proof.
  intros H [|]; cbn; eauto.
  - apply rename_red, H.
Qed.

Lemma main_lemma n (M: tm n)  A Gamma:
  Gamma |- M : A ->  forall n' (S: fin n -> tm n'), RedS S Gamma  -> Red A (subst_tm S M).
Proof.
  induction 1; intros.
  - cbn. apply H.
  - intros m R N rn.
    eapply cr.
    + cbn. econstructor.
      * eapply cr; eauto.
      * reflexivity.
    + asimpl. eapply IHhas_type. intros [|]; eauto.
      * cbn. unfold funcomp. renamify. apply rename_red. eauto.
  - cbn.  specialize (IHhas_type2 _ _ H1).
    specialize (IHhas_type1  _ _ H1 n' id _ IHhas_type2).
    asimpl in IHhas_type1. eauto.
  - specialize (IHhas_type _ _ H0).
    constructor. left. exists (subst_tm S M). split; [reflexivity|auto].
  - specialize (IHhas_type _ _ H0).
    constructor. right. exists (subst_tm S M). split; [reflexivity|auto].
  - specialize (IHhas_type1 _ _ H2). simpl. remember (subst_tm S M) as M'. clear M H HeqM'.
    induction IHhas_type1.
    + destruct H as [(M'&->&H)|(M'&->&H)].
      * eapply cr.
        -- apply SCaseL; [| | |reflexivity].
           ++ eapply cr; eauto.
           ++ eapply cr; eauto using RedUp.
           ++ eapply cr; eauto using RedUp.
        -- asimpl. apply IHhas_type2. intros [|]; eauto.
      * eapply cr.
        -- apply SCaseR; [| | |reflexivity].
           ++ eapply cr; eauto.
           ++ eapply cr; eauto using RedUp.
           ++ eapply cr; eauto using RedUp.
        -- asimpl. apply IHhas_type3. intros [|]; eauto.
    + apply cr.
      constructor.
      * assumption.
      * eapply cr; eauto using RedUp.
      * eapply cr; eauto using RedUp.
    + intros. subst.
      assert (Red (Plus A B) M') as Red_M' by apply IHhas_type1.
      simpl.
      eapply cr.
      instantiate (1 := (orelim M' (subst_tm (up_tm_tm S) N1) (subst_tm (up_tm_tm S) N2))).
      now constructor. assumption.
Qed.

Lemma id_red g Gamma: @RedS g g ids Gamma.
Proof. intros i. now apply red_var. Qed.

Lemma norm n (M: tm n) (A: ty) Gamma: Gamma |- M : A -> SN M.
Proof.
  intros C.
  assert (H := main_lemma _ _ _ _ C _ _ (@id_red n Gamma)).
  asimpl in H. now apply cr in H.
Qed.
