Require Import stlc Coq.Program.Equality.

(** ** Single-step reduction *)
Inductive step {n} : tm n -> tm n -> Prop :=
| step_beta A b t : step (app (lam A b) t) (b[t..])
| step_abs A b1 b2 : @step (S n) b1 b2 -> step (lam A b1) (lam A b2)
| step_appL s1 s2 t : step s1 s2 -> step (app s1 t) (app s2 t)
| step_appR s t1 t2 : step t1 t2 -> step (app s t1) (app s t2).

Lemma step_beta' n A b (t t': tm n):
  t' = b[t..] -> step (app (lam A b) t) t'.
Proof. intros ->. now constructor. Qed.

Definition ImPred {T1 T2} (P : T1 -> Prop) (f : T1 -> T2) (y : T2) :=
  exists2 x : T1, P x & f x = y.

Notation "[ 'Pred' s | x 'in' P ]" :=
  (ImPred (fun x => P) (fun x => s)) .
Notation "x ∈ P" := (P x) (at level 30, only parsing).

Ltac inv H := dependent destruction H.

Lemma im_predI {T1 T2} (P : T1 -> Prop) (f : T1 -> T2) (x : T1) :
  P x -> f x ∈ [Pred f x' | x' in P x'].
Proof. intros px. now exists x. Qed.

Lemma step_weak {m n} (f : fin m -> fin n) (s : tm m) (t : tm n) :
  step (s⟨f⟩) t -> t ∈ [Pred ren_tm f s' | s' in step s s'].
Proof with cbn in *; try congruence.
  intros st. dependent induction st.
  - inv s... inv s1; try inv x... asimpl.
    eexists. constructor. now asimpl.
  - inv s... inv x. destruct (IHst _ _ _ eq_refl) as [s' ih <-].
    exists (lam t s'). now constructor. now asimpl.
  - inv s... inv x. destruct (IHst _ _ _ eq_refl) as [s' ih <-].
    exists (app s' s4). now constructor. now asimpl.
  - inv s... inv x. destruct (IHst _ _ _ eq_refl) as [s' ih <-].
    exists (app s1 s'). now constructor. now asimpl.
Qed.

Lemma step_inst {m n} (f : fin m -> tm n) (s t : tm m) :
  step s t -> step (subst_tm f s) (subst_tm f t).
Proof.
   intros st. revert n f.  induction st as  [m b s t |m A b1 b2 _ ih|m s1 s2 t _ ih|m s t1 t2 _ ih]; intros n f; cbn.
  - apply step_beta'. now asimpl.
  - apply step_abs. eapply ih.
  - apply step_appL, ih.
  - apply step_appR, ih.
Qed.

(** ** Multi-step reduction *)
Inductive mstep {n} (s : tm n) : tm n -> Prop :=
| mstep_refl : mstep s s
| mstep_step t u : mstep s t -> step t u -> mstep s u.
Hint Resolve mstep_refl.

Lemma mstep_trans {n} (s t u : tm n) : mstep s t -> mstep t u -> mstep s u.
Proof. intros st tu. revert s st. induction tu; eauto using mstep_step. Qed.

Lemma mstep_lam n A (s t : tm (S n)) :
  mstep s t -> mstep (lam A s) (lam A t).
Proof. induction 1; eauto using mstep_step, step_abs. Qed.

Lemma mstep_app n (s1 s2 : tm n) (t1 t2 : tm n) :
  mstep s1 s2 -> mstep t1 t2 -> mstep (app s1 t1) (app s2 t2).
Proof with eauto using @mstep, @step.
  intros ms. induction 1. induction ms... auto...
Qed.

Lemma mstep_inst m n (f : fin m -> tm n) (s t : tm m) :
  mstep s t -> mstep (s[f]) (t[f]).
Proof. induction 1; eauto using mstep_step, step_inst. Qed.

Lemma mstep_subst m n (f g : fin m -> tm n) (s t : tm m) :
  mstep s t -> (forall i, mstep (f i) (g i)) ->
  mstep (s[f]) (t[g]).
Proof with eauto using @mstep, @step.
  intros st fg. apply mstep_trans with (t0 := t[f]); [eauto using mstep_inst|].
  clear s st. revert n f g fg.
  induction t; eauto using mstep_app; intros; simpl.
  - apply mstep_lam. apply IHt. intros [i|]; [|constructor].
    + asimpl. cbn. unfold funcomp. substify. now apply mstep_inst.
Qed.

Lemma mstep_beta n (s1 s2 : tm (S n)) (t1 t2 : tm n) :
  mstep s1 s2 -> mstep t1 t2 ->
  mstep (s1 [t1..]) (s2 [t2..]).
Proof.
  intros st1 st2. apply mstep_subst; [assumption|].
  now intros [|].
Qed.
