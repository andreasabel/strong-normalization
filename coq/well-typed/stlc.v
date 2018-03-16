Require Import base contexts.

Inductive tm (G : ctx) : ty -> Type :=
| var A : at_ty G A -> tm G A
| app A B : tm G (Fun A B) -> tm G A -> tm G B
| lam A B : tm (A :: G) B -> tm G (Fun A B).
Arguments var {G A} i.
Arguments app {G A B} s t.
Arguments lam {G A B} b.

Definition subst (G1 G2 : ctx) := env G1 (tm G2).

(** ** Instantiation *)

Fixpoint rinst {G1 G2} (f : ren G1 G2) {A} (s : tm G1 A) : tm G2 A :=
  match s with
  | var _ i => var (f _ i)
  | app _ _ s t => app (rinst f s) (rinst f t)
  | lam _ _ b => lam (rinst (var0 .: (f >> shift)) b)
  end.

Definition up {G1 G2 A} (f : subst G1 G2) : subst (A :: G1) (A :: G2) :=
  var var0 .: (f >> @rinst _ _ shift).

Fixpoint inst {G1 G2} (f : subst G1 G2) {A} (s : tm G1 A) : tm G2 A :=
  match s with
  | var _ i => f _ i
  | app _ _ s t => app (inst f s) (inst f t)
  | lam _ _ b => lam (inst (up f) b)
  end.

(** ** Identity instantiation *)

Definition ids {G} : subst G G := @var G.

Lemma rinst_idren {G A} (s : tm G A) :
  rinst idren s = s.
Proof.
  elim: s => {G A}[//|G A B s ihs t iht|G A B s ihs] /=;
                 intros; simpl; subst; try congruence.
  - fsimpl. by rewrite ihs.
Qed.

Lemma rinst_inst {G1 G2} (f : ren G1 G2) :
  @rinst G1 G2 f = @inst G1 G2 (f >> ids).
Proof.
  fext. intros A s.
  elim: s G2 f => {G1 A}[//|G1 A B s ihs t iht|G1 A B s ihs]/= G2 f; intros; simpl; subst; try congruence.
  - rewrite ihs /up. by fsimpl.
Qed.

Lemma inst_ids {G A} (s : tm G A) :
  inst ids s = s.
Proof.
  by rewrite -{2}[s]rinst_idren rinst_inst.
Qed.

(** ** Composition of instantiations *)

Lemma inst_rinst_comp {G1 G2 G3 A} (f : ren G1 G2) (g : subst G2 G3) (s : tm G1 A) :
  inst g (rinst f s) = inst (f >> g) s.
Proof.
  elim: s G2 G3 f g => {G1 A} [G1 A i|G1 A B s ihs t iht|G1 A B s ihs] G2 G3 f g //=.
  - by rewrite ihs iht.
  - rewrite ihs /up. by fsimpl.
Qed.

Lemma rinst_comp {G1 G2 G3 A} (f : ren G1 G2) (g : ren G2 G3) (s : tm G1 A) :
  rinst g (rinst f s) = rinst (f >> g) s.
Proof.
  by rewrite rinst_inst inst_rinst_comp rinst_inst.
Qed.

Lemma rinst_inst_comp {G1 G2 G3 A} (f : subst G1 G2) (g : ren G2 G3) (s : tm G1 A) :
  rinst g (inst f s) = inst (f >> @rinst _ _ g) s.
Proof.
  elim: s G2 G3 f g => {G1 A} [G1 A i|G1 A B s ihs t iht|G1 A B s ihs] G2 G3 f g //=; intros; simpl; subst; try congruence.
  - rewrite ihs. do 2 f_equal. fext=> {B s ihs} B /=-[E|i]; first by destruct E.
    rewrite/up/scomp/=. by rewrite !rinst_comp.
Qed.

Lemma up_comp {G1 G2 G3 A} (f : subst G1 G2) (g : subst G2 G3) :
  @up G1 G2 A f >> @inst _ _ (up g) = up (f >> @inst _ _ g).
Proof.
  fext=> B /=-[E|i]; first by destruct E. rewrite/up/scomp/=.
  by rewrite rinst_inst_comp inst_rinst_comp.
Qed.

Lemma inst_comp {G1 G2 G3 A} (f : subst G1 G2) (g : subst G2 G3) (s : tm G1 A) :
  inst g (inst f s) = inst (f >> @inst _ _ g) s.
Proof.
  elim: s G2 G3 f g => {G1 A} [G1 A i|G1 A B s ihs t iht|G1 A B s ihs] G2 G3 f g //=;  intros; simpl; subst; try congruence.
  - by rewrite ihs up_comp.
Qed.

(* Automation comp *)
Lemma comp_rinst_inst g g' g'' (xi: ren g g') (sigma : subst g' g'') :
  @rinst g g' xi >> @inst g' g'' sigma = @inst g g'' ((xi >> ids) >> @inst _ _ sigma).
Proof. fext. intros A s. unfold scomp. now rewrite inst_rinst_comp. Qed.

Lemma comp_idl g g' (xi: subst g g') :
  ids >> @inst _ _ xi = xi.
Proof. fext. intros A x. reflexivity. Qed.

Lemma sconsS G P A hd tl : shift >> @scons G P A hd tl = tl.
Proof. by []. Qed.

(** ** Automation *)
Lemma rinst_idrenE G : @rinst G G idren = (fun A x => x).
Proof. fext=> A s. exact: rinst_idren. Qed.

Lemma inst_idsE G : @inst G G ids = (fun A x => x).
Proof. fext=> A s. exact: inst_ids. Qed.

Lemma inst_up_beta {G1 G2 A B} (f : subst G1 G2) (s : tm (B :: G1) A) t :
  inst (inst f t .: ids) (inst (up f) s) =
  inst f (inst (t .: ids) s).
Proof.
  rewrite !inst_comp. f_equal. fext=> C /=-[E|i]; first by destruct E.
  fsimpl. cbn. by rewrite/scomp inst_rinst_comp inst_ids.
Qed.

Ltac asimpl :=
  repeat first [progress rewrite ?comp_rinst_inst ?sconsS ?comp_idl ?rinst_idrenE ?inst_ids ?rinst_inst_comp ?inst_rinst_comp ?inst_comp /up|fsimpl].
