Require Import base contexts stlc.

(** ** Single-step reduction *)
Inductive step : forall {G A}, tm G A -> tm G A -> Prop :=
| step_beta G A B (b : tm (A :: G) B) (t : tm G A) :
    step (app (lam b) t) (inst (t .: ids) b)
| step_abs G A B (b1 b2 : tm (A :: G) B) :
    @step _ _ b1 b2 -> @step G (Fun A B) (lam b1) (lam b2)
| step_appL G A B (s1 s2 : tm G (Fun A B)) (t : tm G A) :
    step s1 s2 -> step (app s1 t) (app s2 t)
| step_appR G A B (s : tm G (Fun A B)) (t1 t2 : tm G A) :
    step t1 t2 -> step (app s t1) (app s t2)
| step_inl G A B (s1 s2: tm G A) :
    step s1 s2 -> step (inl (B := B) s1) (inl s2)
| step_inr G A B (s1 s2: tm G B) :
    step s1 s2 -> step (inr (A := A) s1) (inr s2)
| step_orelim G A B C (s1 s2: tm G (Plus A B)) (t: tm (A :: G) C) u : step s1 s2 -> step (orelim s1 t u) (orelim s2 t u)
| step_orelimL G A B C (s: tm G (Plus A B)) (t1 t2: tm (A :: G) C) u : step t1 t2 -> step (orelim s t1 u) (orelim s t2 u)
| step_orelimR G A B C (s: tm G (Plus A B)) (t: tm (A :: G) C) u1 u2 : step u1 u2 -> step (orelim s t u1) (orelim s t u2)
| step_caseL G A B C (s: tm G A) t (u: tm (B :: G) C) : step (orelim (inl s) t u) (inst (s.:ids) t)
| step_caseR G A B C (s: tm G B) (t: tm (A :: G) C) u: step (orelim (inr s) t u) (inst (s.:ids) u)
.

Definition ImPred {T1 T2} (P : T1 -> Prop) (f : T1 -> T2) (y : T2) :=  exists2 x : T1, P x & f x = y.

Notation "[ 'Pred' s | x 'in' P ]" :=
  (ImPred (fun x => P) (fun x => s)) : form_scope.
Notation "x ∈ P" := (P x) (at level 30, only parsing).

Ltac inv H := dependent destruction H.

Lemma im_predI {T1 T2} (P : T1 -> Prop) (f : T1 -> T2) (x : T1) :
  P x -> f x ∈ [Pred f x' | x' in P x'].
Proof. move=> px. by exists x. Qed.

Lemma step_weak {G1 G2 A} (f : ren G1 G2) (s : tm G1 A) (t : tm G2 A) :
  step (rinst f s) t -> t ∈ [Pred rinst f s' | s' in step s s'].
Proof.
  move=> st. dependent induction st.
  - inv s => //. inv x. inv s1 => //. inv x.
    rewrite !rinst_inst. fsimpl. rewrite inst_up_beta. rewrite -rinst_inst.
    apply: im_predI. exact: step_beta.
  - inv s => //. inv x. case: (IHst _ _ _ erefl) => {IHst} s' ih e.
    exists (lam s'). by constructor. by rewrite -e.
  - inv s => //. inv x. case: (IHst _ _ _ erefl) => {IHst} s' ih e.
    exists (app s' s4). by constructor. by rewrite -e.
  - inv s => //. inv x. case: (IHst _ _ _ erefl) => {IHst} s' ih e.
    exists (app s1 s'). by constructor. by rewrite -e.
  - inv s => //. inv x. case: (IHst _ _ _ erefl) => {IHst} s' ih e.
    exists (inl s'). by constructor. by rewrite -e.
  - inv s => //. inv x. case: (IHst _ _ _ erefl) => {IHst} s' ih e.
    exists (inr s'). by constructor. by rewrite -e.
  - inv s => //. inv x. case: (IHst _ _ _ erefl) => {IHst} s' ih e.
    exists (orelim s' s4 s5). by constructor. by rewrite -e.
  - inv s => //. inv x. case: (IHst _ _ _ erefl) => {IHst} s' ih e.
    exists (orelim s1 s' s3). by constructor. by rewrite -e.
  - inv s => //. inv x. case: (IHst _ _ _ erefl) => {IHst} s' ih e.
    exists (orelim s1 s2 s'). by constructor. by rewrite -e.
  - inv s => //. inv x. inv s1 => //. inv x.
    rewrite !rinst_inst. fsimpl. rewrite inst_up_beta. rewrite -rinst_inst.
    apply: im_predI. exact: step_caseL.
  - inv s => //. inv x. inv s1 => //. inv x.
    rewrite !rinst_inst. fsimpl. rewrite inst_up_beta. rewrite -rinst_inst.
    apply: im_predI. exact: step_caseR.
Qed.

Lemma step_inst {G1 G2 A} (f : subst G1 G2) (s t : tm G1 A) :
  step s t -> step (inst f s) (inst f t).
Proof.
  move=> st. elim: st G2 f => {G1 A s t}
    [G1 A B b t|G1 A B b1 b2 _ ih|G1 A B s1 s2 t _ ih|G1 A B s t1 t2 _ ih|G1 A B s1 s2 _ ih|G1 A B s1 s2 _ ih|G1 A B C s1 s2 t u _ ih|G1 A B C s t1 t2 u _ ih|G1 A B C s t u1 u2 _ ih|G1 A B C s t u|G1 A B C s t u] G2 f/=; try (constructor; exact:ih).
  - rewrite -inst_up_beta. exact: step_beta.
  - rewrite -inst_up_beta. exact: step_caseL.
  - rewrite -inst_up_beta. exact: step_caseR.
Qed.

(** ** Multi-step reduction *)
Inductive mstep {G A} (s : tm G A) : tm G A -> Prop :=
| mstep_refl : mstep s s
| mstep_step t u : mstep s t -> step t u -> mstep s u.
Hint Resolve mstep_refl.

Lemma mstep_trans G A (s t u : tm G A) :
  mstep s t -> mstep t u -> mstep s u.
Proof.  move=> st. elim=> //{u} u v _. exact: mstep_step. Qed.

Lemma mstep_lam G A B (s t : tm (A :: G) B) :
  mstep s t -> mstep (lam s) (lam t).
Proof.
  elim=>//{t}t u _ ih st. apply: mstep_step ih _. exact: step_abs.
Qed.

Lemma mstep_app G1 A B (s1 s2 : tm G1 (Fun A B)) (t1 t2 : tm G1 A) :
  mstep s1 s2 -> mstep t1 t2 -> mstep (app s1 t1) (app s2 t2).
Proof with eauto using @mstep, @step.
  move=> ms. elim. elim: ms... move=> {t2} t2 t3 _ ih st...
Qed.

Lemma mstep_inl G1 A B (s1 s2: tm G1 A):
  mstep s1 s2 -> mstep (inl (B:=B) s1) (inl s2).
Proof.
  induction 1; [apply mstep_refl|].
  eapply mstep_step; eauto using mstep_refl, mstep_trans, step_inl.
Qed.

Lemma mstep_inr G1 A B (s1 s2: tm G1 B):
  mstep s1 s2 -> mstep (inr (A:=A) s1) (inr s2).
Proof.
  induction 1; [apply mstep_refl|].
  eapply mstep_step; eauto using mstep_refl, mstep_trans, step_inr.
Qed.

Lemma mstep_orelim G1 A B C (s1 s2 : tm G1 (Plus A B)) (t1 t2: tm (A::G1) C) u1 u2:
  mstep s1 s2 -> mstep t1 t2 -> mstep u1 u2 -> mstep (orelim s1 t1 u1) (orelim s2 t2 u2).
Proof.
  intros H1 H2 H3.
  apply mstep_trans with (t := orelim s2 t1 u1).
  - induction H1; [eapply mstep_refl|].
    eapply mstep_step; eauto using mstep_refl, mstep_trans, step_orelim.
  - apply mstep_trans with (t := orelim s2 t2 u1).
    + induction H2; [eapply mstep_refl|].
      eapply mstep_step; eauto using mstep_refl, mstep_trans, step_orelimL.
    + induction H3; [eapply mstep_refl|].
    eapply mstep_step; eauto using mstep_refl, mstep_trans, step_orelimR.
Qed.


Lemma mstep_inst G1 G2 A (f : subst G1 G2) (s t : tm G1 A) :
  mstep s t -> mstep (inst f s) (inst f t).
Proof.
  elim=>//{t} t u _ ih st. apply: mstep_step ih _. exact: step_inst.
Qed.

Lemma mstep_subst G1 G2 A (f g : subst G1 G2) (s t : tm G1 A) :
  mstep s t -> (forall B i, mstep (f B i) (g B i)) ->
  mstep (inst f s) (inst g t).
Proof with eauto using @mstep, @step.
  move=> st1 st2. apply: mstep_trans (mstep_inst f st1) _ => {st1 s}.
  elim: t G2 f g st2; eauto using mstep_inl, mstep_inr, mstep_app, mstep_orelim.
  - move=> {G1 A} G1 A B s ih G2 f g st2 /=. apply: mstep_lam.
    apply: ih => {B s} B /=[E|i]; first by destruct E.
    rewrite/=/scomp !rinst_inst. apply: mstep_inst. exact: st2.
  - intros. simpl. apply: mstep_orelim.
    + now apply H.
    + eapply H0. intros D [|]. subst. auto.
      rewrite/=/scomp !rinst_inst. apply: mstep_inst. apply st2.
    + eapply H1. intros D [|]. subst. auto.
      rewrite/=/scomp !rinst_inst. apply: mstep_inst. apply st2.
Qed.

Lemma mstep_beta G A B (s1 s2 : tm (A :: G) B) (t1 t2 : tm G A) :
  mstep s1 s2 -> mstep t1 t2 ->
  mstep (inst (t1 .: ids) s1) (inst (t2 .: ids) s2).
Proof.
  move=> st1 st2. apply: mstep_subst st1 _ => {B s1 s2} B /=[E|i]//.
  by destruct E.
Qed.
