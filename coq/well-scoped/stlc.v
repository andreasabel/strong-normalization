(** * STLC Infrastructure *)
(* This file contains the infrastructure which will be generated automatically by Autosubst 2.
 *)

From mathcomp Require Import ssreflect.all_ssreflect.
Require Import axioms fintype graded.
Set Implicit Arguments.
Unset Strict Implicit.

Local Ltac asimpl := repeat progress (cbn; fsimpl; gsimpl).

Inductive ty :=
  | Base  : ty
  | arr (A B : ty) : ty.

Module TmTerms.
  Section Defs.
  (** *** Types *)

  Inductive tm (n : nat) :=
  | var (i : fin n) : tm n
  | app (A B : tm n) : tm n
  | lam (T: ty) (A : tm n.+1) : tm n.

  (** *** Traversals *)

  Structure traversal (V D : nat -> Type) := Traversal
    { tvar : forall n, V n -> D n
    ; tapp : forall n, D n -> D n -> D n
    ; tlam : forall m, ty -> ☐ (fun m' => V m' -> D m') m -> D m
    }.
  Arguments tvar {V D} t {n} i.
  Arguments tapp {V D} t {n} A B.
  Arguments tlam {V D} t {m} T F.

  Fixpoint eval {V : graded1} {D : nat -> Type} (t : traversal V D)
           {m n : nat} (rho : fin m -> V n) (A : tm m) : D n :=
    match A with
    | var i => tvar t (rho i)
    | app A B => tapp t (eval t rho A) (eval t rho B)
    | lam T A => tlam t T (fun _ xi v => eval t (v .: rho >> th1 xi) A)
    end.

  (** *** Models *)

  Structure is_natural {V D : graded1} (t : traversal V D) := IsNatural
    { nvar : forall m n (f : iren m n) (i : V m),
      (tvar t i) ⋅ f = tvar t (i ⋅ f)
    ; napp : forall m n (f : iren m n) (A B : D m),
      (tapp t A B) ⋅ f = tapp t (A ⋅ f) (B ⋅ f)
    ; nlam : forall m T (F : ☐ (fun m' => V m' -> D m') m),
      (forall n k (f : iren m n) (g : iren n k) (i : V n),
         (F n f i) ⋅ g = F k (f >>> g) (i ⋅ g)) ->
       forall n (f : iren m n),
        (tlam t T F) ⋅ f = tlam t T (F ⋅ f)
    }.

  Structure model (V D : graded1) := Model
    { base : traversal V D
    ; _ : is_natural base
    }.
  Local Coercion base : model >-> traversal.

  Definition model_of {V D : graded1} (V' D' : nat -> Type)
    of phant_id (V : nat -> Type) V' of phant_id (D : nat -> Type) D' := model V D.

  Local Notation "'{' 'model'  V ','  D  '}'" := (@model_of _ _ V D id id) : type_scope.

  Definition model_is_natural {V D : graded1} (t : model V D) : is_natural t :=
    let: Model _ c := t in c.
  Local Coercion model_is_natural : model >-> is_natural.

  (** ** Renaming *)

  Definition ren_traversal : traversal fin tm :=
    Traversal (@var) (@app) (fun m T F => lam T (F m.+1 shift bound)).
  Local Notation tm_ren := (eval ren_traversal).
  Local Notation "s ◁ f" := (tm_ren f s) (at level 50).
  Canonical tm_graded1 := Eval hnf in Graded1 tm (@eval _ _ ren_traversal).

  Lemma th1_tmE {m n} (f : iren m n) (A : tm m) : A ⋅ f = A ◁ f.
  Proof. by []. Qed.

  Local Ltac gsimpl' := rewrite ?th1_tmE; gsimpl.

  Lemma ren_is_natural : is_natural ren_traversal.
  Proof.
    apply: IsNatural => //= m T F H n f.
      gsimpl' => /=. by rewrite -shift_up -(H m.+1 n.+1 shift (up f) bound).
  Qed.
  Canonical ren_model : {model fin, tm} := Eval hnf in Model ren_is_natural.

  Section EvalRen.
    Context {V : graded1} {D : nat -> Type} (t : traversal V D).

    Lemma eval_ren {m n k : nat} (A : tm m) (f : ren m n) (rho : fin n -> V k) :
      eval t rho (A ◁ f) = eval t (f >> rho) A.
    Proof.
      elim: A n k f rho => {m}//=[m A ih1 B ih2|m T A ih] n k f rho.
        by rewrite ih1 ih2. congr tlam; fext=> l g i. rewrite ih. by fsimpl.
    Qed.
  End EvalRen.

  Lemma ren_comp {m n k : nat} (f : ren m n) (g : ren n k) (A : tm m) :
    A ◁ f ◁ g = A ◁ (f >> g).
  Proof. exact: eval_ren. Qed.

  Lemma ren_inj {m n : nat} (f : ren m n) : injective f -> injective (tm_ren f).
  Proof.
    move=> H A B. (* elim: A B n f H => {m}[m i|m A1 ih1 A2 ih2|m A ih] [|B1 B2|B].   n f H //=[].
    - by move=>/H->.
    - move=>/ih1 e1 /ih2 e2. by rewrite e1 // e2.
    - move=>/ih e. rewrite e //. by hnf=> /= -[i|] [j|] //=[/H->].
  Qed. *)
  Admitted.


  Lemma ren_id {n : nat} (A : tm n) : A ◁ id = A.
  Proof. apply: (ren_inj (f := id)) => //. exact: ren_comp. Qed.

  Canonical tm_cgraded1 := Eval hnf in CGraded1 tm (@ren_comp).
  Canonical tm_igraded1 := Eval hnf in IGraded1 tm (@ren_id).
  Canonical tm_pgraded1 := Eval hnf in PGraded1 tm (fun m n f => ren_inj (@iren_inj m n f)).

  (** *** Lifting *)

  Definition lift {V D : graded1} (t : traversal V D) : traversal D D :=
    Traversal (fun n => id) (@tapp _ _ t)
              (fun m T F => tlam t T (fun n f v => F n f (tvar t v))).

  Definition lift_is_natural {V D : graded1} (t : model V D) :
    is_natural (lift t).
  Proof.
    apply: IsNatural => //[m n f A B/=|m T F FP n f]. exact: (napp t).
    apply: (nlam t) => {n f} n k f g v. by rewrite FP (nvar t).
  Qed.

  Canonical lift_model {V D : graded1} (t : model V D) : model D D :=
    Eval hnf in Model (lift_is_natural t).

  Definition lift_embed {V D : graded1} (t : model V D)
      {m n : nat} (rho : fin m -> V n) (A : tm m) :
    eval t rho A = eval (lift t) (rho >> tvar t) A.
  Proof.
    elim: A n rho => {m} //=[m A ihA B ihB|m T A ih] n rho.
    - by rewrite ihA ihB.
    - congr tlam; fext => k xi v. rewrite ih. congr eval.
      fsimpl=>/=. congr scons. fext=> i /=. symmetry. exact: (nvar t).
  Qed.

  (** *** Instantiation *)

  Notation inst_traversal := (lift ren_traversal).
  Notation inst := (eval inst_traversal).
  Notation "A .[ f ]" := (inst f A) : tm_inst_scope.
  Delimit Scope tm_inst_scope with tm.

  Definition inst_id {n : nat} (A : tm n) :
    A.[@var n]%tm = A.
  Proof.
    rewrite -{2}[A]th_id1/=. symmetry. exact: lift_embed.
  Qed.

  Definition tm_ren_inst {m n k : nat} (A : tm m) (f : ren m n) (g : fin n -> tm k) :
    (A ◁ f).[g]%tm = A.[f >> g]%tm.
  Proof. exact: eval_ren. Qed.

  (** *** Naturality *)

  Definition naturality {V : cgraded1} {D : graded1} (t : model V D)
           {m n k : nat} (rho : fin m -> V n) (f : iren n k) (A : tm m) :
    (eval t rho A) ⋅ f = eval t (rho >> th1 f) A.
  Proof.
    elim: A n k rho f => {m}[m i|m A ihA B ihB|m T A ih] n k rho f.
    - exact: (nvar t).
    - cbn. rewrite (napp t). congr tapp. exact: ihA. exact: ihB.
    - cbn. rewrite (nlam t).
      + congr tlam; fext=> l g v. by asimpl.
      + move=> {k f} k l f g v. rewrite ih. by asimpl.
  Qed.

  (*Definition ty_inst_ren {m n k : nat} (A : ty m) (f : fin m -> ty n) (g : iren n k) :
    A.[f]%ty ⋅ g = A.[f >> th1 g]%ty.
  Proof. exact: naturality. Qed.*)

  (** *** Compatibility with instantiation *)

  Definition eval_inst {V : cgraded1} {D : graded1} (t : model V D)
           {m n k : nat} (sigma : fin m -> tm n) (rho : fin n -> V k) (A : tm m) :
    eval t rho A.[sigma]%tm =
    eval (lift t) (sigma >> eval t rho) A.
  Proof.
    elim: A n k sigma rho => {m}//=[m A ihA B ihB|m T A ih] n k sigma rho.
    - by rewrite ihA ihB.
    - congr tlam; fext=> l f v. rewrite ih. asimpl. congr eval.
      fext=>/=;case=>//=i. rewrite eval_ren /=. symmetry. exact: naturality.
  Qed.

  Definition inst_comp {m n k : nat} (A : tm m) (f : fin m -> tm n) (g : fin n -> tm k) :
    A.[f]%tm.[g]%tm = A.[f >> inst g]%tm.
  Proof. exact: eval_inst. Qed.

  Lemma tm_inst_ren {m n k : nat} (A : tm m) (f : fin m -> tm n) (g : ren n k) :
    A.[f]%tm ◁ g = A.[f >> tm_ren g]%tm.
  Proof.
    rewrite lift_embed inst_comp. do 2 f_equal. symmetry. fext. exact: lift_embed.
  Qed.

  End Defs.

  Module Exports.
    Notation tm := tm.
    Canonical tm_graded1.
    Canonical tm_cgraded1.
    Canonical tm_igraded1.
    Canonical tm_pgraded1.

    Canonical ren_model.
    Canonical lift_model.

    Coercion base : model >-> traversal.
    Coercion model_is_natural : model >-> is_natural.

    Arguments tvar {V D} t {n} i.
    Arguments tapp {V D} t {n} A B.
    Arguments tlam {V D} t {m} F.

    Arguments var {n}, n.

    Module Tm.
      (* Types *)
      Notation var := var.
      Notation app := app.
      Notation lam := lam.

      (* Traversal *)
      Notation traversal := traversal.
      Notation Traversal := Traversal.
      Notation tvar := tvar.
      Notation tapp := tapp.
      Notation tlam := tlam.

      Notation ren_traversal := ren_traversal.
      Notation inst_traversal := (lift ren_traversal).
      Notation lift := lift.

      (* Models *)
      Notation is_natural := is_natural.
      Notation IsNatural := IsNatural.
      Notation nvar := nvar.
      Notation napp := napp.
      Notation nlam := nlam.

      Notation model := model.
      Notation Model := Model.

      (* Evaluation *)
      Notation eval := eval.

      Notation eval_ren := eval_ren.
      Notation eval_inst := eval_inst.
      Notation naturality := naturality.

      Notation embed := lift_embed.

      (* Renaming *)
      Notation ren  := (eval ren_traversal).

      Notation ren_id := ren_id.
      Notation ren_comp := ren_comp.
      Notation ren_inj := ren_inj.

      (* Instantiation *)
      Notation inst := (eval inst_traversal).

      Notation ren_inst := tm_ren_inst.
      Notation inst_ren := tm_inst_ren.

      Notation inst_id := inst_id.
      Notation inst_comp := inst_comp.

    End Tm.
    Notation "A ◁ f" := (Tm.ren f A) (at level 50) : tm_inst_scope.
    Notation "A .[ f ]" := (Tm.inst f A) : tm_inst_scope.
    Delimit Scope tm_inst_scope with tm.
  End Exports.
End TmTerms.
Export TmTerms.Exports.

Canonical TmTerms.tm_graded1.
Canonical TmTerms.tm_cgraded1.
Canonical TmTerms.tm_igraded1.
Canonical TmTerms.tm_pgraded1.

Canonical TmTerms.ren_model.
    Canonical TmTerms.lift_model.

(* Automation *)
Lemma tm_ren_idX {n} : Tm.ren (id : fin n -> fin n) = id.
Proof. fext=> A. exact: Tm.ren_id. Qed.

Lemma tm_ren_compX {m n k} (f : ren m n) (g : ren n k) :
  Tm.ren f >> Tm.ren g = Tm.ren (f >> g).
Proof. fext=> A /=. exact: Tm.ren_comp. Qed.

Lemma tm_ren_compR {T m n k} (f : ren m n) (g : ren n k) (h : _ -> T) :
  Tm.ren f >> (Tm.ren g >> h) = Tm.ren (f >> g) >> h.
Proof. fext=> A /=. by rewrite Tm.ren_comp. Qed.

Lemma tm_ren_instX {m n k} (f : ren m n) (g : fin n -> tm k) :
  Tm.ren f >> Tm.inst g = Tm.inst (f >> g).
Proof. fext=> A /=. exact: Tm.ren_inst. Qed.

Lemma tm_ren_instR {T m n k} (f : ren m n) (g : fin n -> tm k) (h : _ -> T) :
  Tm.ren f >> (Tm.inst g >> h) = Tm.inst (f >> g) >> h.
Proof. fext=> A /=. by rewrite Tm.ren_inst. Qed.

Lemma tm_inst_renX {m n k} (f : fin m -> tm n) (g : ren n k) :
  Tm.inst f >> Tm.ren g = Tm.inst (f >> Tm.ren g).
Proof. fext=> A /=. exact: Tm.inst_ren. Qed.

Lemma tm_inst_renR {T m n k} (f : fin m -> tm n) (g : ren n k) (h : _ -> T) :
  Tm.inst f >> (Tm.ren g >> h) = Tm.inst (f >> Tm.ren g) >> h.
Proof. fext=> A /=. by rewrite Tm.inst_ren. Qed.

Lemma tm_id_instX {m n} (f : fin m -> tm n) : Tm.var >> Tm.inst f = f.
Proof. by []. Qed.

Lemma tm_inst_idX {n} : Tm.inst (@Tm.var n) = id.
Proof. fext=> A. exact: Tm.inst_id. Qed.

Lemma tm_inst_idR {T m n} (f : fin m -> tm n) (g : _ -> T) : Tm.var >> (Tm.inst f >> g) = (f >> g).
Proof. by []. Qed.

Lemma tm_inst_compX {m n k} (f : fin m -> tm n) (g : fin n -> tm k) :
  Tm.inst f >> Tm.inst g = Tm.inst (f >> Tm.inst g).
Proof. fext=> A /=. exact: Tm.inst_comp. Qed.

Lemma tm_inst_compR {T m n k} (f : fin m -> tm n) (g : fin n -> tm k) (h : _ -> T) :
  Tm.inst f >> (Tm.inst g >> h) = Tm.inst (f >> Tm.inst g) >> h.
Proof. fext=> A /=. by rewrite Tm.inst_comp. Qed.

Ltac tm_simpl :=
  rewrite ?tm_ren_idX ?tm_ren_compX ?tm_ren_compR
          ?tm_ren_instX ?tm_ren_instR
          ?tm_inst_renX ?tm_inst_renR
          ?tm_id_instX ?tm_inst_idX ?tm_inst_idR
          ?tm_inst_compX ?tm_inst_compR
          ?Tm.ren_id ?Tm.ren_comp ?Tm.ren_inst ?Tm.inst_ren ?Tm.inst_id ?Tm.inst_comp
          ?Tm.eval_ren ?Tm.eval_inst  ?Tm.naturality
          ?TmTerms.th1_tmE.
