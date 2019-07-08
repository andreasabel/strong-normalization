Require Import stlc reduction sn_defs sn_inductive_2a.

(** ** Logical Relation *)
Fixpoint Red {n} (A : ty) : tm n -> Prop :=
  match A with
  | Base => fun s => SN s
  | Fun A B => fun s =>
      forall n' (S : fin n -> fin n') (t : tm n'), Red A t -> Red B (app (ren_tm S s) t)
  end.

Definition RedS {n n'} (S: fin n -> tm n') (Gamma: fin n -> ty) :=
  forall i, Red (Gamma i) (S i).

Lemma rename_red m n (f : fin m -> fin n) (s : tm m) A :
  Red A s -> Red A (ren_tm f s).
Proof.
  revert s. destruct A as [| A B]; intros s; cbn.
  - intros H. now apply rename.
  - intros H n' g t lt. asimpl.  now apply H.
Qed.

Lemma cr A:
  (forall n (M: tm n), Red A M -> SN M) /\ (forall n (M: tm n), SNe M -> Red A M) /\ (forall n (M M': tm n), SNRed M M' -> Red A M' -> Red A M).
Proof.
  induction A as [|A IHA B IHB].
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
Qed.

Lemma red_var n (p: fin n) A:
  Red A (var_tm p).
Proof. apply cr, SVar. Qed.

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
    has_type Gamma (app M N) S.
Notation "Gamma |- M : T" := (has_type Gamma M T) (at level 20, M at level 99).

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
Qed.

Lemma id_red g Gamma: @RedS g g ids Gamma.
Proof. intros i. now apply red_var. Qed.

Lemma norm n (M: tm n) (A: ty) Gamma: Gamma |- M : A -> SN M.
Proof.
  intros C.
  assert (H := main_lemma _ _ _ _ C _ _ (@id_red n Gamma)).
  asimpl in H. now apply cr in H.
Qed.
