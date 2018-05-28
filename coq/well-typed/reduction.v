Require Import base contexts stlc.

(** ** Single-step reduction *)
Inductive step {G} : forall {A}, tm G A -> tm G A -> Prop :=
| step_beta A B (b : tm (A :: G) B) (t : tm G A) :
    step (app (lam b) t) (inst (t .: ids) b)
| step_abs A B (b1 b2 : tm (A :: G) B) :
    @step _ _ b1 b2 -> @step G (Fun A B) (lam b1) (lam b2)
| step_appL A B (s1 s2 : tm G (Fun A B)) (t : tm G A) :
    step s1 s2 -> step (app s1 t) (app s2 t)
| step_appR A B (s : tm G (Fun A B)) (t1 t2 : tm G A) :
    step t1 t2 -> step (app s t1) (app s t2).

Definition ImPred {T1 T2} (P : T1 -> Prop) (f : T1 -> T2) (y : T2) :=
  exists2 x : T1, P x & f x = y.

Notation "[ 'Pred' s | x 'in' P ]" :=
  (ImPred (fun x => P) (fun x => s)) .
Notation "x ∈ P" := (P x) (at level 30, only parsing).

Ltac inv H := dependent destruction H.

Lemma im_predI {T1 T2} (P : T1 -> Prop) (f : T1 -> T2) (x : T1) :
  P x -> f x ∈ [Pred f x' | x' in P x'].
Proof. intros px. now exists x. Qed.

Lemma step_weak {G1 G2 A} (f : ren G1 G2) (s : tm G1 A) (t : tm G2 A) :
  step (rinst f s) t -> t ∈ [Pred rinst f s' | s' in step s s'].
Proof with simpl in *; try congruence.
  intros st. dependent induction st.
  - inv s... inv s1; try inv x... asimpl.
    eexists. constructor. now asimpl.
  - inv s... inv x. destruct (IHst _ _ _ eq_refl) as [s' ih <-].
    exists (lam s'). now constructor. now fsimpl.
  - inv s... inv x. destruct (IHst _ _ _ eq_refl) as [s' ih <-].
    exists (app s' s4). now constructor. now fsimpl.
  - inv s... inv x. destruct (IHst _ _ _ eq_refl) as [s' ih <-].
    exists (app s1 s'). now constructor. now fsimpl.
Qed.

Lemma step_inst {G1 G2 A} (f : subst G1 G2) (s t : tm G1 A) :
  step s t -> step (inst f s) (inst f t).
Proof.
  intros st. revert G2 f. induction st as  [G1 A B b t|G1 A B b1 b2 _ ih|G1 A B s1 s2 t _ ih|G1 A B s t1 t2 _ ih]; intros G2 f; cbn.
  - rewrite <- inst_up_beta. apply step_beta.
  - apply step_abs, ih.
  - apply step_appL, ih.
  - apply step_appR, ih.
Qed.

(** ** Multi-step reduction *)
Inductive mstep {G A} (s : tm G A) : tm G A -> Prop :=
| mstep_refl : mstep s s
| mstep_step t u : mstep s t -> step t u -> mstep s u.
Hint Resolve mstep_refl.

Lemma mstep_trans G A (s t u : tm G A) : mstep s t -> mstep t u -> mstep s u.
Proof. intros st tu. revert s st. induction tu; eauto using mstep_step. Qed.

Lemma mstep_lam G A B (s t : tm (A :: G) B) :
  mstep s t -> mstep (lam s) (lam t).
Proof. induction 1; eauto using mstep_step, step_abs. Qed.

Lemma mstep_app G1 A B (s1 s2 : tm G1 (Fun A B)) (t1 t2 : tm G1 A) :
  mstep s1 s2 -> mstep t1 t2 -> mstep (app s1 t1) (app s2 t2).
Proof with eauto using @mstep, @step.
  intros ms. induction 1. induction ms... auto...
Qed.

Lemma mstep_inst G1 G2 A (f : subst G1 G2) (s t : tm G1 A) :
  mstep s t -> mstep (inst f s) (inst f t).
Proof. induction 1; eauto using mstep_step, step_inst. Qed.

Lemma mstep_subst G1 G2 A (f g : subst G1 G2) (s t : tm G1 A) :
  mstep s t -> (forall B i, mstep (f B i) (g B i)) ->
  mstep (inst f s) (inst g t).
Proof with eauto using @mstep, @step.
  intros st fg. apply mstep_trans with (t := inst f t); [eauto using mstep_inst|].
  clear s st. revert G2 f g fg.
  induction t; eauto using mstep_app; intros; simpl.
  - apply mstep_lam. apply IHt. intros C [->|i]; [constructor|].
    unfold up, scomp. rewrite !rinst_inst. apply mstep_inst, fg.
Qed.

Lemma mstep_beta G A B (s1 s2 : tm (A :: G) B) (t1 t2 : tm G A) :
  mstep s1 s2 -> mstep t1 t2 ->
  mstep (inst (t1 .: ids) s1) (inst (t2 .: ids) s2).
Proof.
  intros st1 st2. apply mstep_subst; [assumption|].
  now intros C [->|i].
Qed.
