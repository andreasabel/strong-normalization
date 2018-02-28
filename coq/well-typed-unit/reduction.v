Require Import base contexts stlc.

(** ** Single-step reduction *)

Inductive step {G} : forall {A}, tm G A -> tm G A -> Prop :=
| step_unit (M : tm G Base) :
    M <> unit -> step M unit
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
  (ImPred (fun x => P) (fun x => s)) : form_scope.
Notation "x ∈ P" := (P x) (at level 30, only parsing).

Ltac inv H := dependent destruction H.

Lemma im_predI {T1 T2} (P : T1 -> Prop) (f : T1 -> T2) (x : T1) :
  P x -> f x ∈ [Pred f x' | x' in P x'].
Proof. move=> px. by exists x. Qed.

Lemma inst_up_beta {G1 G2 A B} (f : subst G1 G2) (s : tm (B :: G1) A) t :
  inst (inst f t .: ids) (inst (up f) s) =
  inst f (inst (t .: ids) s).
Proof.
  rewrite !inst_comp. f_equal. fext=> C /=-[E|i]; first by destruct E.
  fsimpl. cbn. by rewrite/scomp inst_rinst_comp inst_ids.
Qed.

Lemma step_weak {G1 G2 A} (f : ren G1 G2) (s : tm G1 A) (t : tm G2 A) :
  step (rinst f s) t -> t ∈ [Pred rinst f s' | s' in step s s'].
Proof.
  move=> st. dependent induction st.
  - exists unit => //=. apply: step_unit. inv s => //=.
  - inv s => //. inv x. inv s1 => //. inv x.
    rewrite !rinst_inst. fsimpl. rewrite inst_up_beta. rewrite -rinst_inst.
    apply: im_predI. exact: step_beta.
  - inv s => //. inv x. case: (IHst _ _ _ erefl) => {IHst} s' ih e.
    exists (lam s'). by constructor. by rewrite -e.
  - inv s => //. inv x. case: (IHst _ _ _ erefl) => {IHst} s' ih e.
    exists (app s' s4). by constructor. by rewrite -e.
  - inv s => //. inv x. case: (IHst _ _ _ erefl) => {IHst} s' ih e.
    exists (app s1 s'). by constructor. by rewrite -e.
Qed.

(** ** Multi-step reduction *)

Inductive mstep {G A} (s : tm G A) : tm G A -> Prop :=
| mstep_refl : mstep s s
| mstep_step t u : mstep s t -> step t u -> mstep s u.
Hint Resolve mstep_refl.

Lemma mstep_trans G A (s t u : tm G A) :
  mstep s t -> mstep t u -> mstep s u.
Proof.
  move=> st. elim=> //{u} u v _. exact: mstep_step.
Qed.

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

Lemma unit_dec G (s: tm G Base):
  {s = unit} + {s <> unit}.
Proof. inv s; eauto. now right. now right. Qed.

Lemma step_inst {G1 G2 A} (f : subst G1 G2) (s t : tm G1 A) :
  step s t -> step (inst f s) (inst f t) \/ (inst f s = inst f t).
Proof.
  move=> st. elim: st G2 f => {G1 A s t}
                               [G M H|G1 A B b t|G1 A B b1 b2 _ ih|G1 A B s1 s2 t _ ih|G1 A B s t1 t2 _ ih] G2 f/=.
  - destruct (unit_dec (inst f M)) as [->|E].
    + now right.
    + left. now constructor.
  - left.  rewrite -inst_up_beta. exact: step_beta.
  - destruct (ih _ (up f)) as [ih'|ih']; [left; now constructor|right; congruence].
  - destruct (ih G2 f) as [ih'|ih']; [left; now constructor|right; congruence].
  - destruct (ih G2 f) as [ih'|ih']; [left; now constructor|right; congruence].
Qed.

(* Lemma step_inst {G1 G2 A} (f : subst G1 G2) (s t : tm G1 A) :
  step s t -> mstep (inst f s) (inst f t).
Proof.
  move=> st. elim: st G2 f => {G1 A s t}
                               [G M H|G1 A B b t|G1 A B b1 b2 _ ih|G1 A B s1 s2 t _ ih|G1 A B s t1 t2 _ ih] G2 f/=.
  - destruct (unit_dec (inst f M)) as [->|E].
    + constructor.
    + eapply mstep_step; constructor. assumption.
  - eapply mstep_step; [constructor|]. rewrite -inst_up_beta. exact: step_beta.
  - now apply mstep_lam.
  - now apply mstep_app.
  - now apply mstep_app.
Qed. *)

Lemma mstep_inst G1 G2 A (f : subst G1 G2) (s t : tm G1 A) :
  mstep s t -> mstep (inst f s) (inst f t).
Proof.
  elim=>//{t} t u _ ih st. apply: mstep_trans ih _. destruct (step_inst f st) as [| ->]; eauto using mstep_step.
Qed.

Lemma mstep_subst G1 G2 A (f g : subst G1 G2) (s t : tm G1 A) :
  mstep s t -> (forall B i, mstep (f B i) (g B i)) ->
  mstep (inst f s) (inst g t).
Proof with eauto using @mstep, @step.
  move=> st1 st2. apply: mstep_trans (mstep_inst f st1) _ => {st1 s}.
  elim: t G2 f g st2...
  - move=> {G1 A} G1 A B s ihs t iht G2 f g st2 /=. apply: mstep_app.
    exact: ihs. exact: iht.
  - move=> {G1 A} G1 A B s ih G2 f g st2 /=. apply: mstep_lam.
    apply: ih => {B s} B /=[E|i]; first by destruct E.
    rewrite/=/scomp !rinst_inst. apply: mstep_inst. exact: st2.
Qed.

Lemma mstep_beta G A B (s1 s2 : tm (A :: G) B) (t1 t2 : tm G A) :
  mstep s1 s2 -> mstep t1 t2 ->
  mstep (inst (t1 .: ids) s1) (inst (t2 .: ids) s2).
Proof.
  move=> st1 st2. apply: mstep_subst st1 _ => {B s1 s2} B /=[E|i]//.
  by destruct E.
Qed.

(** ** Strong normalization *)

Inductive sn {G A} (s : tm G A) : Prop :=
| snI : (forall t, step s t -> sn t) -> sn s.

Lemma sn_unit {G: ctx} :
  @sn G _ unit.
Proof. constructor. intros s H. now inv H. Qed.

Lemma sn_preimage {G1 G2 A1 A2} (f : tm G1 A1 -> tm G2 A2) (s : tm G1 A1) :
  (forall t u, step t u -> step (f t) (f u)) ->
  sn (f s) -> sn s.
Proof.
  move=> H sns. dependent induction sns. apply: snI => t st.
  apply: H0; last by reflexivity. apply: H. eassumption. exact: H.
Qed.

Lemma sn_appL {G A B} (s : tm G (Fun A B)) (t : tm G A) :
  sn (app s t) -> sn s.
Proof.
  apply: (@sn_preimage _ _ _ _ (app^~ t)); eauto using @step.
Qed.

Lemma sn_mstep g A (M M' : tm g A):
  sn M -> mstep M M' -> sn M'.
Proof. intros H. induction 1; auto. inv IHmstep; auto.  Qed.

Lemma sn_rinst {G1 G2 A} (f : ren G1 G2) (s : tm G1 A) :
  sn s -> sn (rinst f s).
Proof.
  elim=> {s} s _ ih. apply: snI => t /step_weak[t' st <-]. exact: ih.
Qed.

Lemma sn_inst {G1 G2 A} (f: subst G1 G2) (s: tm G1 A) :
  sn (inst f s) -> sn s.
Proof.
  remember (inst f s) as s'. intros H. revert s Heqs'. induction H as [s' H IH]; intros s ->.
  constructor. intros s' C. inv C.
Admitted.
