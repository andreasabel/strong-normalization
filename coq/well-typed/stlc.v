Require Import base contexts.
Opaque at_ty.

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
  | var i => var (f _ i)
  | app s t => app (rinst f s) (rinst f t)
  | lam b => lam (rinst (var0 .: (f >> shift)) b)
  end.

Definition up {G1 G2 A} (f : subst G1 G2) : subst (A :: G1) (A :: G2) :=
  var var0 .: (f >> @rinst _ _ shift).

Fixpoint inst {G1 G2} (f : subst G1 G2) {A} (s : tm G1 A) : tm G2 A :=
  match s with
  | var i => f _ i
  | app s t => app (inst f s) (inst f t)
  | lam b => lam (inst (up f) b)
  end.

(** ** Identity instantiation *)

Definition ids {G} : subst G G := @var G.

Lemma rinst_idren {G A} (s : tm G A) :
  rinst idren s = s.
Proof.
  induction s; intros; try reflexivity; try (simpl; subst; congruence); simpl.
  - fsimpl. congruence.
Qed.

Lemma rinst_inst {G1 G2} (f : ren G1 G2) :
  @rinst G1 G2 f = @inst G1 G2 (f >> ids).
Proof.
  fext. intros A s. revert G2 f.
  induction s; intros; simpl; subst; try reflexivity; try congruence.
  - unfold up. rewrite IHs. now fsimpl.
Qed.

Lemma inst_ids {G A} (s : tm G A) :
  inst ids s = s.
Proof. now rewrite <- rinst_idren, rinst_inst. Qed.

(** ** Composition of instantiations *)

Lemma inst_rinst_comp {G1 G2 G3 A} (f : ren G1 G2) (g : subst G2 G3) (s : tm G1 A) :
  inst g (rinst f s) = inst (f >> g) s.
Proof.
  revert G2 G3 f g.
  induction s; intros; cbn; try reflexivity; try congruence.
  - unfold up. rewrite IHs. now fsimpl.
Qed.

Lemma rinst_comp {G1 G2 G3 A} (f : ren G1 G2) (g : ren G2 G3) (s : tm G1 A) :
  rinst g (rinst f s) = rinst (f >> g) s.
Proof.
  now rewrite rinst_inst, inst_rinst_comp, rinst_inst.
Qed.

Lemma rinst_inst_comp {G1 G2 G3 A} (f : subst G1 G2) (g : ren G2 G3) (s : tm G1 A) :
  rinst g (inst f s) = inst (f >> @rinst _ _ g) s.
Proof.
  revert G2 G3 f g.
  induction s; intros; simpl; subst; try congruence; try reflexivity.
  - unfold up, scomp. rewrite IHs. do 2 f_equal. fext. intros C [-> |i]; [reflexivity|].
    unfold scomp. simpl. now rewrite !rinst_comp.
Qed.

Lemma up_comp {G1 G2 G3 A} (f : subst G1 G2) (g : subst G2 G3) :
  @up G1 G2 A f >> @inst _ _ (up g) = up (f >> @inst _ _ g).
Proof.
  fext. intros B [->|i]; [reflexivity|]. unfold up, scomp.
  cbn. now rewrite rinst_inst_comp, inst_rinst_comp.
Qed.

Lemma inst_comp {G1 G2 G3 A} (f : subst G1 G2) (g : subst G2 G3) (s : tm G1 A) :
  inst g (inst f s) = inst (f >> @inst _ _ g) s.
Proof.
  revert G2 G3 f g. induction s as [G1 A i|G1 A B s ihs t iht|G1 A B s ihs]; intros; simpl; subst; try congruence; try reflexivity.
  - now rewrite ihs, up_comp.
Qed.

(* Automation comp *)
Lemma comp_rinst_inst g g' g'' (xi: ren g g') (sigma : subst g' g'') :
  @rinst g g' xi >> @inst g' g'' sigma = @inst g g'' ((xi >> ids) >> @inst _ _ sigma).
Proof. fext. intros A s. unfold scomp. now rewrite inst_rinst_comp. Qed.

Lemma comp_idl g g' (xi: subst g g') :
  ids >> @inst _ _ xi = xi.
Proof. fext. intros A x. reflexivity. Qed.

Lemma sconsS G P A hd tl : shift >> @scons G P A hd tl = tl.
Proof. reflexivity. Qed.

(** ** Automation *)
Lemma rinst_idrenE G : @rinst G G idren = (fun A x => x).
Proof. fext. intros A s. apply rinst_idren. Qed.

Lemma inst_idsE G : @inst G G ids = (fun A x => x).
Proof. fext. intros A s. apply inst_ids. Qed.

Lemma inst_up_beta {G1 G2 A B} (f : subst G1 G2) (s : tm (B :: G1) A) t :
  inst (inst f t .: ids) (inst (up f) s) =
  inst f (inst (t .: ids) s).
Proof.
  rewrite !inst_comp. f_equal. fext. intros C [->|i]; [reflexivity|].
  fsimpl. cbn. unfold scomp. rewrite inst_rinst_comp. fsimpl. now rewrite inst_ids.
Qed.

Ltac asimpl :=
  repeat first [unfold up; progress rewrite ?comp_rinst_inst, ?sconsS,?comp_idl,?rinst_idrenE,?inst_ids,?rinst_inst_comp,?inst_rinst_comp,?inst_comp|fsimpl].
