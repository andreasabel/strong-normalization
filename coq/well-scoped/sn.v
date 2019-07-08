Require Import base contexts stlc reduction.

(** ** Logical Relation *)

Fixpoint L (G : ctx) (A : ty) : tm G A -> Prop :=
  match A with
  | Base => sn
  | Fun A B => fun s =>
      forall G' (f : ren G G') (t : tm G' A), L t -> L (app (rinst f s) t)
  end.

(** Lemma 10 *)

Lemma L_step G A (s t : tm G A) :
  step s t -> L s -> L t.
Proof.
  elim: A G s t => /=[G s t st [H]|A ih1 B ih2 G1 s t st ls G2 f u lu]. exact: H.
  apply: ih2; last by exact: ls lu. apply: step_appL. rewrite !rinst_inst. exact: step_inst.
Qed.

Lemma L_mstep G A (s t : tm G A) :
  mstep s t -> L s -> L t.
Proof.
  elim=>//{t}t u _ ih /L_step; tauto.
Qed.

(** Lemma 11 *)

Lemma L_rinst G1 G2 A (f : ren G1 G2) (s : tm G1 A) :
  L s -> L (rinst f s).
Proof.
  case: A s => [|A B] s /=. exact: sn_rinst.
  move=> H G3 g t lt. rewrite rinst_comp. exact: H.
Qed.

(** Lemma 12 *)

Definition neutral {G A} (s : tm G A) : bool :=
  if s is lam _ _ _ then false else true.

Definition neutral_expansion_closed {G A} (P : tm G A -> Prop) :=
  forall s, neutral s -> (forall t, step s t -> P t) -> P s.

Lemma neutral_expansion_closed_var {G A} P (i : at_ty G A) :
  neutral_expansion_closed P -> P (var i).
Proof. apply=> //t st. by inv st. Qed.

Lemma L_sn_nec G A :
  (forall s : tm G A, L s -> sn s) /\ neutral_expansion_closed (@L G A).
Proof.
  elim: A G => [|A ihA B ihB] G. by split. split.
  - move=> s /=/(_ (A :: G) shift (var var0)). case/(_ _)/Wrap.
    apply: neutral_expansion_closed_var. by case: (ihA (A::G)).
    case: (ihB (A::G)) => h _ /h/sn_appL. by rewrite rinst_inst => /sn_inst.
  - move=> s ns /=ihs G' f t lt. have snt: sn t. case: (ihA G') => h _. exact: h.
    elim: snt lt => /={t} t _ iht lt.
    case: (ihB G') => _ h; apply: h => // u st. inv st.
    + by inv s.
    + move: st => /step_weak[s' st <-{s2}]. exact: (ihs s' st).
    + apply: iht => //. exact: L_step st lt.
Qed.

Corollary L_sn G A (s : tm G A) : L s -> sn s.
Proof. case: (L_sn_nec G A) => H _. exact: H. Qed.

Corollary L_nec G A : neutral_expansion_closed (@L G A).
Proof. by case: (L_sn_nec G A). Qed.

Corollary L_var G A (i : at_ty G A) : L (var i).
Proof. apply: neutral_expansion_closed_var. exact: L_nec. Qed.

(** Lemma 13 *)

Lemma beta_expansion G A B (s : tm (A :: G) B) t :
  sn t -> L (inst (t .: ids) s) -> L (app (lam s) t).
Proof.
  move=> snt ls. have sns: sn s. by move: ls => /L_sn/sn_inst.
  elim: sns t snt ls => {s}s _ ihs t. elim=>{t}t snt iht ls.
  apply: L_nec => // u st. inv st.
  - exact: ls.
  - inv st. apply: ihs. exact: st. constructor. exact: snt.
    apply: L_step ls. exact: step_inst.
  - apply: iht. exact: st. apply: L_mstep ls.
    apply: mstep_beta; eauto using @mstep.
Qed.

Theorem fundamental G1 A (s : tm G1 A) :
  forall G2 (f : subst G1 G2), (forall B i, L (f B i)) -> L (inst f s).
Proof.
  elim: s => {G1 A}[G1 A i|G1 A B s ihs t iht|G1 A B b ih] G2 f fP /=.
  - exact: fP.
  - move: (ihs G2 f fP) => /=/(_ G2 idren (inst f t)). rewrite rinst_idren. apply.
    exact: iht.
  - move=> G3 g t lt. apply: beta_expansion. exact: L_sn.
    rewrite rinst_inst_comp inst_comp. apply: ih => C/=[E|i].
    destruct E => //. cbn. rewrite inst_rinst_comp. fsimpl.
    rewrite inst_rinst_comp. fsimpl. rewrite -rinst_inst.
    apply: L_rinst. exact: fP.
Qed.

Corollary strong_normalization G A (s : tm G A) : sn s.
Proof.
  apply: L_sn. move: (@fundamental G A s G ids).
  case/(_ _)/Wrap. move=> B i. exact: L_var.
    by rewrite inst_ids.
Qed.
