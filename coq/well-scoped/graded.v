(** * Graded Types *)
From mathcomp Require Import ssreflect.all_ssreflect.
Require Import axioms fintype.
Set Implicit Arguments.
Unset Strict Implicit.

(* 1 *)

Module Graded1.
  Definition mixin_of (p : nat -> Type) :=
    forall m n, iren m n -> p m -> p n.
  Notation class_of := mixin_of (only parsing).

  Section Defs.
    Structure type := Pack
      { sort : nat -> Type
      ; _ : class_of sort
      ; _ : nat -> Type
      }.
    Local Coercion sort : type >-> Funclass.

    Variable (p : nat -> Type) (cT : type).
    Definition class :=
      let: Pack _ c _ := cT return class_of cT in c.

    Definition pack th := @Pack p th p.
    Definition clone c of phant_id class c := @Pack p c p.
  End Defs.

  Module Exports.
    Coercion sort : type >-> Funclass.
    Notation graded1 := type.
    Notation Graded1 p th := (@pack p th).

    Notation "[ 'graded1' 'of' p 'for' C ]" := (@clone p C _ idfun)
      (at level 0, format "[ 'graded1'  'of'  p  'for'  C ]") : form_scope.
    Notation "[ 'graded1' 'of' p ]" := (@clone p _ _ id)
      (at level 0, format "[ 'graded1'  'of'  p ]") : form_scope.
  End Exports.
End Graded1.
Export Graded1.Exports.

Definition th1 {T : graded1} {m n : nat} : iren m n -> T m -> T n := @Graded1.class T m n.
Arguments th1 {T m n} f x : simpl never.

Notation "x ⋅ f" := (@th1 _ _ _ f x)
  (at level 2, left associativity, format "x  ⋅  f") : graded_scope.
Notation "x ⋅ ( f )" := (@th1 _ _ _ f x)
  (at level 2, left associativity, only parsing) : graded_scope.
Open Scope graded_scope.

Module CGraded1.
  Definition mixin_of (T : graded1) :=
    forall m n k (f : iren m n) (g : iren n k) (x : T m), x ⋅ f ⋅ g = x ⋅ (f >>> g).

  Section ClassDef.
    Record class_of (p : nat -> Type) := Class {
      base : Graded1.class_of p;
      mixin : mixin_of (Graded1.Pack base p)
    }.
    Local Coercion base : class_of >-> Graded1.class_of.

    Structure type := Pack {sort; _ : class_of sort; _ : nat -> Type }.
    Local Coercion sort : type >-> Funclass.

    Variable (T : nat -> Type) (cT : type).
    Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
    Definition clone c of phant_id class c := @Pack T c T.
    Let xT := let: Pack T _ _ := cT in T.
    Notation xclass := (class : class_of xT).

    Definition pack b0 (m0 : mixin_of (@Graded1.Pack T b0 T)) :=
      fun bT b & phant_id (@Graded1.class bT) b =>
      fun m & phant_id m0 m => Pack (@Class T b m) T.

    Definition graded1 := @Graded1.Pack cT xclass xT.
  End ClassDef.

  Module Exports.
    Coercion base : class_of >-> Graded1.class_of.
    Coercion mixin : class_of >-> mixin_of.
    Coercion sort : type >-> Funclass.

    Coercion graded1 : type >-> Graded1.type.
    Canonical graded1.

    Notation cgraded1 := type.
    Notation CGraded1 T m := (@pack T _ m _ _ id _ id).

    Notation "[ 'cgraded1' 'of' T 'for' C ]" := (@clone T C _ idfun)
      (at level 0, format "[ 'cgraded1'  'of'  T  'for'  C ]") : form_scope.
    Notation "[ 'cgraded1' 'of' T ]" := (@clone T _ _ id)
      (at level 0, format "[ 'cgraded1'  'of'  T ]") : form_scope.
  End Exports.
End CGraded1.
Export CGraded1.Exports.

Module IGraded1.
  Definition mixin_of (T : graded1) :=
    forall n (x : T n), x ⋅ idren = x.

  Section ClassDef.
    Record class_of (p : nat -> Type) := Class {
      base : Graded1.class_of p;
      mixin : mixin_of (Graded1.Pack base p)
    }.
    Local Coercion base : class_of >-> Graded1.class_of.

    Structure type := Pack {sort; _ : class_of sort; _ : nat -> Type }.
    Local Coercion sort : type >-> Funclass.

    Variable (T : nat -> Type) (cT : type).
    Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
    Definition clone c of phant_id class c := @Pack T c T.
    Let xT := let: Pack T _ _ := cT in T.
    Notation xclass := (class : class_of xT).

    Definition pack b0 (m0 : mixin_of (@Graded1.Pack T b0 T)) :=
      fun bT b & phant_id (@Graded1.class bT) b =>
      fun m & phant_id m0 m => Pack (@Class T b m) T.

    Definition graded1 := @Graded1.Pack cT xclass xT.
  End ClassDef.

  Module Exports.
    Coercion base : class_of >-> Graded1.class_of.
    Coercion mixin : class_of >-> mixin_of.
    Coercion sort : type >-> Funclass.

    Coercion graded1 : type >-> Graded1.type.
    Canonical graded1.

    Notation igraded1 := type.
    Notation IGraded1 T m := (@pack T _ m _ _ id _ id).

    Notation "[ 'igraded1' 'of' T 'for' C ]" := (@clone T C _ idfun)
      (at level 0, format "[ 'igraded1'  'of'  T  'for'  C ]") : form_scope.
    Notation "[ 'igraded1' 'of' T ]" := (@clone T _ _ id)
      (at level 0, format "[ 'igraded1'  'of'  T ]") : form_scope.
  End Exports.
End IGraded1.
Export IGraded1.Exports.

Module PGraded1.
  Definition mixin_of (T : graded1) :=
    forall m n (f : iren m n), injective (@th1 T m n f).

  Section ClassDef.
    Record class_of (p : nat -> Type) := Class {
      base : Graded1.class_of p;
      mixin : mixin_of (Graded1.Pack base p)
    }.
    Local Coercion base : class_of >-> Graded1.class_of.

    Structure type := Pack {sort; _ : class_of sort; _ : nat -> Type }.
    Local Coercion sort : type >-> Funclass.

    Variable (T : nat -> Type) (cT : type).
    Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
    Definition clone c of phant_id class c := @Pack T c T.
    Let xT := let: Pack T _ _ := cT in T.
    Notation xclass := (class : class_of xT).

    Definition pack b0 (m0 : mixin_of (@Graded1.Pack T b0 T)) :=
      fun bT b & phant_id (@Graded1.class bT) b =>
      fun m & phant_id m0 m => Pack (@Class T b m) T.

    Definition graded1 := @Graded1.Pack cT xclass xT.
  End ClassDef.

  Module Exports.
    Coercion base : class_of >-> Graded1.class_of.
    Coercion mixin : class_of >-> mixin_of.
    Coercion sort : type >-> Funclass.

    Coercion graded1 : type >-> Graded1.type.
    Canonical graded1.

    Notation pgraded1 := type.
    Notation PGraded1 T m := (@pack T _ m _ _ id _ id).

    Notation "[ 'pgraded1' 'of' T 'for' C ]" := (@clone T C _ idfun)
      (at level 0, format "[ 'pgraded1'  'of'  T  'for'  C ]") : form_scope.
    Notation "[ 'pgraded1' 'of' T ]" := (@clone T _ _ id)
      (at level 0, format "[ 'pgraded1'  'of'  T ]") : form_scope.
  End Exports.
End PGraded1.
Export PGraded1.Exports.

(** *** Lemmas *)

Lemma th_comp1 {T : cgraded1} {m n k : nat} (f : iren m n) (g : iren n k) (x : T m) :
  x ⋅ f ⋅ g = x ⋅ (f >>> g).
Proof. exact: CGraded1.mixin. Qed.

Lemma th_id1 {T : igraded1} {n : nat} (x : T n) :
  x ⋅ idren = x.
Proof. exact: IGraded1.mixin. Qed.

Lemma th_inj1 {T : pgraded1} {m n : nat} (f : iren m n) (x y : T m) :
  x ⋅ f = y ⋅ f -> x = y.
Proof. exact: PGraded1.mixin. Qed.

(** *** Trivial grading *)

Section TrivialGraded1.
  Definition fin_th1 {m n : nat} (xi : ren m n) (x : fin m) : fin n := xi x.

  Canonical fin_graded1 := Eval hnf in Graded1 fin (@fin_th1).

  Lemma fin_cgraded1_mixin : CGraded1.mixin_of fin_graded1.
  Proof. by []. Qed.

  Canonical fin_cgraded1 := Eval hnf in CGraded1 fin fin_cgraded1_mixin.

  Lemma fin_igraded1_mixin : IGraded1.mixin_of fin_graded1.
  Proof. by []. Qed.

  Canonical fin_igraded1 := Eval hnf in IGraded1 fin fin_igraded1_mixin.

  Lemma fin_pgraded1_mixin : PGraded1.mixin_of fin_graded1.
  Proof. move=> m n f x y. exact: iren_inj. Qed.

  Canonical fin_pgraded1 := Eval hnf in PGraded1 fin fin_pgraded1_mixin.

  Lemma th1_finE {m n} (f : iren m n) : @th1 fin_graded1 m n f = f.
  Proof. by []. Qed.
End TrivialGraded1.

(** *** Constant grading *)

Definition const1 (V : Type) : nat -> Type := fun=> V.

Section ConstGraded1.
  Variable (T : Type).

  Canonical const_graded1 : graded1 :=
    Eval hnf in Graded1 (const1 T) (fun _ _ _ => id).

  Lemma const_cgraded1_mixin : CGraded1.mixin_of const_graded1.
  Proof. by []. Qed.

  Canonical const_cgraded1 :=
    Eval hnf in CGraded1 (const1 T) const_cgraded1_mixin.

  Lemma const_igraded1_mixin : IGraded1.mixin_of const_graded1.
  Proof. by []. Qed.

  Canonical const_igraded1 := Eval hnf in IGraded1 (const1 T) const_igraded1_mixin.

  Lemma const_pgraded1_mixin : PGraded1.mixin_of const_graded1.
  Proof. move=> m n f x y. exact. Qed.

  Canonical const_pgraded1 := Eval hnf in PGraded1 (const1 T) const_pgraded1_mixin.

  Lemma th1_constE {m n} (f : iren m n) : @th1 const_graded1 m n f = id.
  Proof. by []. Qed.
End ConstGraded1.

(** *** Monotone grading *)

Definition box (V : nat -> Type) (m : nat) : Type :=
  forall n, iren m n -> V n.

Section BoxGraded1.
  Variable (V : nat -> Type).

  Canonical box_graded1 : graded1 :=
    Eval hnf in Graded1 (box V) (fun m n f bv k g  => bv k (f >>> g)).

  Lemma box_cgraded1_mixin : CGraded1.mixin_of box_graded1.
  Proof. by []. Qed.

  Canonical box_cgraded1 :=
    Eval hnf in CGraded1 (box V) box_cgraded1_mixin.

  Lemma box_igraded1_mixin : IGraded1.mixin_of box_graded1.
  Proof. by []. Qed.

  Canonical box_igraded1 :=
    Eval hnf in IGraded1 (box V) box_igraded1_mixin.

  Lemma th1_boxE {m n k} (f : iren m n) (g : iren n k) (b : box V m) : (b ⋅ f) k g = b k (f >>> g).
  Proof. by []. Qed.
End BoxGraded1.

Notation "☐ V" := (box V) (at level 2).

(* set grading *)

Definition pred1 (A : nat -> Type) (n : nat) := A n -> Prop.

Definition im {X Y} (f : X -> Y) (P : X -> Prop) (y : Y) : Prop :=
  exists2 x, P x & f x = y.

Lemma im_inj {X Y} (f : X -> Y) (P : X -> Prop) (x : X) :
  injective f -> im f P (f x) = P x.
Proof.
  move=> fP. apply: pext; split=> [[x' px' /fP <-//]|px]. by exists x.
Qed.

Lemma im_injective {X Y} (f : X -> Y) :
  injective f -> injective (im f).
Proof.
  move=> fP P Q E. fext=> x. by rewrite -(im_inj P x fP) E im_inj.
Qed.

Lemma im_id {X} (P : X -> Prop) : im id P = P.
Proof. fext=> x. apply: pext; split=> [[y py <-//]|px]. by exists x. Qed.

Lemma im_comp {X Y Z} (f : X -> Y) (g : Y -> Z) (P : X -> Prop) :
  im g (im f P) = im (f >> g) P.
Proof.
  fext=> x. apply: pext; split=>[[y[z pz <-]<-]|[z pz <-]].
    by exists z. exists (f z) => //. by exists z.
Qed.

Section PredGrading.
  Variable (A : graded1).

  Definition pred_th1 {m n} (f : iren m n) (P : pred1 A m) : pred1 A n := im (th1 f) P.

  Canonical pred_graded1 := Eval hnf in Graded1 (pred1 A) (@pred_th1).

  Lemma th1_predE {m n} (f : iren m n) (P : pred1 A m) : P ⋅ f = im (th1 f) P.
  Proof. by []. Qed.
End PredGrading.

Section PredCGrading.
  Variable (A : cgraded1).

  Lemma pred_cgraded1_mixin : CGraded1.mixin_of (pred_graded1 A).
  Proof.
    move=>/=m n k f g P. rewrite !th1_predE im_comp. f_equal.
    fext=> x /=. by rewrite th_comp1.
  Qed.

  Canonical pred_cgraded1 := Eval hnf in CGraded1 (pred1 A) pred_cgraded1_mixin.
End PredCGrading.

Section PredIGrading.
  Variable (A : igraded1).

  Lemma pred_igraded1_mixin : IGraded1.mixin_of (pred_graded1 A).
  Proof.
    hnf; intros. fext=> H. apply: pext; split. move=> [H' P]. by rewrite th_id1 => <-.
    move=> H'. hnf. exists H => //. by rewrite th_id1.
  Qed.

  Canonical pred_igraded1 := Eval hnf in IGraded1 (pred1 A) pred_igraded1_mixin.
End PredIGrading.

Section PredPGrading.
  Variable (A : pgraded1).

  Lemma pred_pgraded1_mixin : PGraded1.mixin_of (pred_graded1 A).
  Proof.
    move=> m n f /=. apply: im_injective. exact: th_inj1.
  Qed.

  Canonical pred_pgraded1 := Eval hnf in PGraded1 (pred1 A) pred_pgraded1_mixin.

  (*Lemma th1_predE {m n} (f : iren m n) (P : pred1 A m) (i : A m) :
    (P ⋅ f) (i ⋅ f) = P i.
  Proof.
    apply: pext; split. by case=> j pj /th_inj1<-. move=> pi. by exists i.
  Qed.*)
End PredPGrading.

(* 2 *)

Module Graded2.
  Definition mixin_of (p : nat -> nat -> Type) :=
    forall m1 n1 m2 n2, iren m1 m2 -> iren n1 n2 -> p m1 n1 -> p m2 n2.
  Notation class_of := mixin_of (only parsing).

  Section Defs.
    Structure type := Pack
      { sort : nat -> nat ->Type
      ; _ : class_of sort
      ; _ : nat -> nat -> Type
      }.
    Local Coercion sort : type >-> Funclass.

    Variable (p : nat -> nat -> Type) (cT : type).
    Definition class :=
      let: Pack _ c _ := cT return class_of cT in c.

    Definition pack th := @Pack p th p.
    Definition clone c of phant_id class c := @Pack p c p.
  End Defs.

  Module Exports.
    Coercion sort : type >-> Funclass.
    Notation graded2 := type.
    Notation Graded2 p th := (@pack p th).

    Notation "[ 'graded2' 'of' p 'for' C ]" := (@clone p C _ idfun)
      (at level 0, format "[ 'graded2'  'of'  p  'for'  C ]") : form_scope.
    Notation "[ 'graded2' 'of' p ]" := (@clone p _ _ id)
      (at level 0, format "[ 'graded2'  'of'  p ]") : form_scope.
  End Exports.
End Graded2.
Export Graded2.Exports.

Definition th2 {T : graded2} {m1 n1 m2 n2 : nat} : iren m1 m2 -> iren n1 n2 -> T m1 n1 -> T m2 n2 := @Graded2.class T m1 n1 m2 n2.
Arguments th2 {T m1 n1 m2 n2} f g x : simpl never.
Notation "x ⋅ ( f , g )" := (@th2 _ _ _ _ _ f g x) (at level 2, left associativity, format "x  ⋅  ( f ,  g )") : graded_scope.

Module CGraded2.
  Definition mixin_of (T : graded2) :=
    forall m1 m2 m3 n1 n2 n3 (f1 : iren m1 m2) (f2 : iren m2 m3) (g1 : iren n1 n2) (g2 : iren n2 n3) (x : T m1 n1), x ⋅ (f1,g1) ⋅ (f2,g2) = x ⋅ (f1 >>> f2, g1 >>> g2).

  Section ClassDef.
    Record class_of (p : nat -> nat -> Type) := Class {
      base : Graded2.class_of p;
      mixin : mixin_of (Graded2.Pack base p)
    }.
    Local Coercion base : class_of >-> Graded2.class_of.

    Structure type := Pack {sort; _ : class_of sort; _ : nat -> nat -> Type }.
    Local Coercion sort : type >-> Funclass.

    Variable (T : nat -> nat -> Type) (cT : type).
    Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
    Definition clone c of phant_id class c := @Pack T c T.
    Let xT := let: Pack T _ _ := cT in T.
    Notation xclass := (class : class_of xT).

    Definition pack b0 (m0 : mixin_of (@Graded2.Pack T b0 T)) :=
      fun bT b & phant_id (@Graded2.class bT) b =>
      fun m & phant_id m0 m => Pack (@Class T b m) T.

    Definition graded2 := @Graded2.Pack cT xclass xT.
  End ClassDef.

  Module Exports.
    Coercion base : class_of >-> Graded2.class_of.
    Coercion mixin : class_of >-> mixin_of.
    Coercion sort : type >-> Funclass.

    Coercion graded2 : type >-> Graded2.type.
    Canonical graded2.

    Notation cgraded2 := type.
    Notation CGraded2 T m := (@pack T _ m _ _ id _ id).

    Notation "[ 'cgraded2' 'of' T 'for' C ]" := (@clone T C _ idfun)
      (at level 0, format "[ 'cgraded2'  'of'  T  'for'  C ]") : form_scope.
    Notation "[ 'cgraded2' 'of' T ]" := (@clone T _ _ id)
      (at level 0, format "[ 'cgraded2'  'of'  T ]") : form_scope.
  End Exports.
End CGraded2.
Export CGraded2.Exports.

Module IGraded2.
  Definition mixin_of (T : graded2) :=
    forall m n (x : T m n), x ⋅ (idren,idren) = x.

  Section ClassDef.
    Record class_of (p : nat -> nat -> Type) := Class {
      base : Graded2.class_of p;
      mixin : mixin_of (Graded2.Pack base p)
    }.
    Local Coercion base : class_of >-> Graded2.class_of.

    Structure type := Pack {sort; _ : class_of sort; _ : nat -> nat -> Type }.
    Local Coercion sort : type >-> Funclass.

    Variable (T : nat -> nat -> Type) (cT : type).
    Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
    Definition clone c of phant_id class c := @Pack T c T.
    Let xT := let: Pack T _ _ := cT in T.
    Notation xclass := (class : class_of xT).

    Definition pack b0 (m0 : mixin_of (@Graded2.Pack T b0 T)) :=
      fun bT b & phant_id (@Graded2.class bT) b =>
      fun m & phant_id m0 m => Pack (@Class T b m) T.

    Definition graded2 := @Graded2.Pack cT xclass xT.
  End ClassDef.

  Module Exports.
    Coercion base : class_of >-> Graded2.class_of.
    Coercion mixin : class_of >-> mixin_of.
    Coercion sort : type >-> Funclass.

    Coercion graded2 : type >-> Graded2.type.
    Canonical graded2.

    Notation igraded2 := type.
    Notation IGraded2 T m := (@pack T _ m _ _ id _ id).

    Notation "[ 'igraded2' 'of' T 'for' C ]" := (@clone T C _ idfun)
      (at level 0, format "[ 'igraded2'  'of'  T  'for'  C ]") : form_scope.
    Notation "[ 'igraded2' 'of' T ]" := (@clone T _ _ id)
      (at level 0, format "[ 'igraded2'  'of'  T ]") : form_scope.
  End Exports.
End IGraded2.
Export IGraded2.Exports.

Module PGraded2.
  Definition mixin_of (T : graded2) :=
    forall m1 m2 n1 n2 (f : iren m1 m2) (g : iren n1 n2), injective (@th2 T _ _ _ _ f g).

  Section ClassDef.
    Record class_of (p : nat -> nat -> Type) := Class {
      base : Graded2.class_of p;
      mixin : mixin_of (Graded2.Pack base p)
    }.
    Local Coercion base : class_of >-> Graded2.class_of.

    Structure type := Pack {sort; _ : class_of sort; _ : nat -> nat -> Type }.
    Local Coercion sort : type >-> Funclass.

    Variable (T : nat -> nat -> Type) (cT : type).
    Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
    Definition clone c of phant_id class c := @Pack T c T.
    Let xT := let: Pack T _ _ := cT in T.
    Notation xclass := (class : class_of xT).

    Definition pack b0 (m0 : mixin_of (@Graded2.Pack T b0 T)) :=
      fun bT b & phant_id (@Graded2.class bT) b =>
      fun m & phant_id m0 m => Pack (@Class T b m) T.

    Definition graded2 := @Graded2.Pack cT xclass xT.
  End ClassDef.

  Module Exports.
    Coercion base : class_of >-> Graded2.class_of.
    Coercion mixin : class_of >-> mixin_of.
    Coercion sort : type >-> Funclass.

    Coercion graded2 : type >-> Graded2.type.
    Canonical graded2.

    Notation pgraded2 := type.
    Notation PGraded2 T m := (@pack T _ m _ _ id _ id).

    Notation "[ 'pgraded2' 'of' T 'for' C ]" := (@clone T C _ idfun)
      (at level 0, format "[ 'pgraded2'  'of'  T  'for'  C ]") : form_scope.
    Notation "[ 'pgraded2' 'of' T ]" := (@clone T _ _ id)
      (at level 0, format "[ 'pgraded2'  'of'  T ]") : form_scope.
  End Exports.
End PGraded2.
Export PGraded2.Exports.

(** *** Lemmas *)

Lemma th_comp2 {T : cgraded2} {m1 m2 m3 n1 n2 n3 : nat} (f1 : iren m1 m2) (f2 : iren m2 m3) (g1 : iren n1 n2) (g2 : iren n2 n3) (x : T m1 n1) :
  x ⋅ (f1,g1) ⋅ (f2,g2) = x ⋅ (f1 >>> f2, g1 >>> g2).
Proof. exact: CGraded2.mixin. Qed.

Lemma th_id2 {T : igraded2} {m n : nat} (x : T m n) :
  x ⋅ (idren, idren) = x.
Proof. exact: IGraded2.mixin. Qed.

Lemma th_inj2 {T : pgraded2} {m1 m2 n1 n2} (f : iren m1 m2) (g : iren n1 n2) (x y : T m1 n1) :
  x ⋅ (f,g) = y ⋅ (f,g) -> x = y.
Proof. exact: PGraded2.mixin. Qed.

(** *** Left/Right grading *)

Definition constl (F : nat -> Type) (m n : nat) : Type := F m.
Definition constr (F : nat -> Type) (m n : nat) : Type := F n.

Section LiftGrading.
  Variable (F : graded1).

  Definition constl_th2 {m1 n1 m2 n2 : nat} (f : iren m1 m2) (g : iren n1 n2)
    (x : constl F m1 n1) : constl F m2 n2 := x ⋅ f.
  Definition constr_th2 {m1 n1 m2 n2 : nat} (f : iren m1 m2) (g : iren n1 n2)
    (x : constr F m1 n1) : constr F m2 n2 := x ⋅ g.

  Canonical constl_graded2 := Eval hnf in Graded2 (constl F) (@constl_th2).
  Canonical constr_graded2 := Eval hnf in Graded2 (constr F) (@constr_th2).

  Lemma th2_constlE {m1 n1 m2 n2} (f : iren m1 m2) (g : iren n1 n2) :
    @th2 constl_graded2 m1 n1 m2 n2 f g = @th1 F m1 m2 f.
  Proof. by []. Qed.

  Lemma th2_constrE {m1 n1 m2 n2} (f : iren m1 m2) (g : iren n1 n2) :
    @th2 constr_graded2 m1 n1 m2 n2 f g = @th1 F n1 n2 g.
  Proof. by []. Qed.
End LiftGrading.

Section LiftCGrading.
  Variable (F : cgraded1).

  Lemma constl_cgraded2_mixin : CGraded2.mixin_of (constl_graded2 F).
  Proof. hnf;intros. exact: th_comp1. Qed.

  Lemma constr_cgraded2_mixin : CGraded2.mixin_of (constr_graded2 F).
  Proof. hnf;intros. exact: th_comp1. Qed.

  Canonical contl_cgraded2 := Eval hnf in CGraded2 (constl F) constl_cgraded2_mixin.
  Canonical contr_cgraded2 := Eval hnf in CGraded2 (constr F) constr_cgraded2_mixin.
End LiftCGrading.

Section LiftIGrading.
  Variable (F : igraded1).

  Lemma constl_igraded2_mixin : IGraded2.mixin_of (constl_graded2 F).
  Proof. hnf;intros. exact: th_id1. Qed.

  Lemma constr_igraded2_mixin : IGraded2.mixin_of (constr_graded2 F).
  Proof. hnf;intros. exact: th_id1. Qed.

  Canonical constl_igraded2 := Eval hnf in IGraded2 (constl F) constl_igraded2_mixin.
  Canonical constr_igraded2 := Eval hnf in IGraded2 (constr F) constr_igraded2_mixin.
End LiftIGrading.

Section LiftPGrading.
  Variable (F : pgraded1).

  Lemma constl_pgraded2_mixin : PGraded2.mixin_of (constl_graded2 F).
  Proof. hnf;intros. exact: th_inj1. Qed.

  Lemma constr_pgraded2_mixin : PGraded2.mixin_of (constr_graded2 F).
  Proof. hnf;intros. exact: th_inj1. Qed.

  Canonical constl_pgraded2 := Eval hnf in PGraded2 (constl F) constl_pgraded2_mixin.
  Canonical constr_pgraded2 := Eval hnf in PGraded2 (constr F) constr_pgraded2_mixin.
End LiftPGrading.

(** *** Trivial grading *)

Definition fin2 : nat -> nat -> Type := constr fin.

(** *** Constant grading *)

Definition const2 (V : Type) : nat -> nat -> Type := fun _ _ => V.

Section ConstGraded2.
  Variable (T : Type).

  Canonical const_graded2 : graded2 :=
    Eval hnf in Graded2 (const2 T) (fun _ _ _ _ _ _ => id).

  Lemma const_cgraded2_mixin : CGraded2.mixin_of const_graded2.
  Proof. by []. Qed.

  Canonical const_cgraded2 :=
    Eval hnf in CGraded2 (const2 T) const_cgraded2_mixin.

  Lemma const_igraded2_mixin : IGraded2.mixin_of const_graded2.
  Proof. by []. Qed.

  Canonical const_igraded2 := Eval hnf in IGraded2 (const2 T) const_igraded2_mixin.

  Lemma const_pgraded2_mixin : PGraded2.mixin_of const_graded2.
  Proof. move=> m1 m2 n1 n2 f g x y. exact. Qed.

  Canonical const_pgraded2 := Eval hnf in PGraded2 (const2 T) const_pgraded2_mixin.

  Lemma th2_constE {m1 n1 m2 n2} (f : iren m1 m2) (g : iren n1 n2) :
    @th2 const_graded2 m1 n1 m2 n2 f g = id.
  Proof. by []. Qed.
End ConstGraded2.

(* Pred2 grading *)

Definition pred2 (A : nat -> nat -> Type) (m n : nat) := A m n -> Prop.

Section Pred2Grading.
  Variable (A : graded2).

  Definition pred_th2 {m1 n1 m2 n2} (f : iren m1 m2) (g : iren n1 n2) (P : pred2 A m1 n1) : pred2 A m2 n2 :=
    im (th2 f g) P.

  Canonical pred_graded2 := Eval hnf in Graded2 (pred2 A) (@pred_th2).

  Lemma th2_predE {m1 n1 m2 n2} (f : iren m1 m2) (g : iren n1 n2) (P : pred2 A m1 n1) :
    P ⋅ (f,g) = im (th2 f g) P.
  Proof. by []. Qed.
End Pred2Grading.

Section Pred2CGrading.
  Variable (A : cgraded2).

  Lemma pred_cgraded2_mixin : CGraded2.mixin_of (pred_graded2 A).
  Proof.
    move=>/=m1 m2 m3 n1 n2 n3 f1 f2 g1 g2 P. rewrite !th2_predE im_comp. f_equal.
    fext=> x /=. by rewrite th_comp2.
  Qed.

  Canonical pred_cgraded2 := Eval hnf in CGraded2 (pred2 A) pred_cgraded2_mixin.
End Pred2CGrading.

Section Pred2IGrading.
  Variable (A : igraded2).

  Lemma pred_igraded2_mixin : IGraded2.mixin_of (pred_graded2 A).
  Proof.
    hnf; intros. fext=> H. apply: pext; split. move=> [H' P]. by rewrite th_id2 => <-.
    move=> H'. hnf. exists H => //. by rewrite th_id2.
  Qed.

  Canonical pred_igraded2 := Eval hnf in IGraded2 (pred2 A) pred_igraded2_mixin.
End Pred2IGrading.

Section Pred2PGrading.
  Variable (A : pgraded2).

  Lemma pred_pgraded2_mixin : PGraded2.mixin_of (pred_graded2 A).
  Proof.
    move=> m1 m2 n1 n2 f g /=. apply: im_injective. exact: th_inj2.
  Qed.

  Canonical pred_pgraded2 := Eval hnf in PGraded2 (pred2 A) pred_pgraded2_mixin.
End Pred2PGrading.

(** *** Monotone grading *)

Definition box2 (V : nat -> nat -> Type) (m1 n1 : nat) : Type :=
  forall m2 n2, iren m1 m2 -> iren n1 n2 -> V m2 n2.

Section BoxGraded2.
  Variable (V : nat -> nat -> Type).

  Canonical box_graded2 : graded2 :=
    Eval hnf in Graded2 (box2 V)
      (fun m1 n1 m2 n2 f1 g1 bv m3 n3 f2 g2 => bv m3 n3 (f1 >>> f2) (g1 >>> g2)).

  Lemma box_cgraded2_mixin : CGraded2.mixin_of box_graded2.
  Proof. by []. Qed.

  Canonical box_cgraded2 :=
    Eval hnf in CGraded2 (box2 V) box_cgraded2_mixin.

  Lemma box_igraded2_mixin : IGraded2.mixin_of box_graded2.
  Proof. by []. Qed.

  Canonical box_igraded2 :=
    Eval hnf in IGraded2 (box2 V) box_igraded2_mixin.

  Lemma th2_boxE {m1 n1 m2 n2 m3 n3} (f1 : iren m1 m2) (f2 : iren m2 m3) (g1 : iren n1 n2) (g2 : iren n2 n3) (b : box2 V m1 n1) :
    @th2 box_graded2 m1 n1 m2 n2 f1 g1 b m3 n3 f2 g2 = b m3 n3 (f1 >>> f2) (g1 >>> g2).
  Proof. by []. Qed.
End BoxGraded2.

Notation "☐₂ V" := (box2 V) (at level 2).

(** Left1 *)

Definition left1 (n : nat) (F : nat -> nat -> Type) (m : nat) := F m n.

Section LeftGraded1.
  Variable (F : graded2) (n : nat).

  Definition left_th1 {m1 m2} (f : iren m1 m2) (x : left1 n F m1) : left1 n F m2 :=
    x ⋅ (f,idren).

  Canonical left_graded1 := Eval hnf in Graded1 (left1 n F) (@left_th1).

  Lemma th1_leftE {m1 m2} (f : iren m1 m2) (x : left1 n F m1) :
    x ⋅ f = x ⋅ (f,idren).
  Proof. by []. Qed.
End LeftGraded1.

Section LeftCGraded1.
  Variable (F : cgraded2) (n : nat).

  Lemma left_cgraded1_mixin : CGraded1.mixin_of (left_graded1 F n).
  Proof.
    move=> /= m1 m2 m3 f1 f2 x. by rewrite !th1_leftE th_comp2.
  Qed.

  Canonical left_cgraded1 := Eval hnf in CGraded1 (left1 n F) left_cgraded1_mixin.
End LeftCGraded1.

Section LeftIGraded1.
  Variable (F : igraded2) (n : nat).

  Lemma left_igraded1_mixin : IGraded1.mixin_of (left_graded1 F n).
  Proof.
    move=> /= m x. by rewrite th1_leftE th_id2.
  Qed.

  Canonical left_igraded1 := Eval hnf in IGraded1 (left1 n F) left_igraded1_mixin.
End LeftIGraded1.

Section LeftPGraded1.
  Variable (F : pgraded2) (n : nat).

  Lemma left_pgraded1_mixin : PGraded1.mixin_of (left_graded1 F n).
  Proof.
    move=> /= m1 m2 f x y. rewrite !th1_leftE. exact: th_inj2.
  Qed.

  Canonical left_pgraded1 := Eval hnf in PGraded1 (left1 n F) left_pgraded1_mixin.
End LeftPGraded1.

(** Automation *)

Lemma th1_idX {T : igraded1} {n : nat} : @th1 T n n idren = id.
Proof. fext=> i. exact: th_id1. Qed.

Lemma th1_compX {T : cgraded1} {m n k : nat} (f : iren m n) (g : iren n k) :
  @th1 T m n f >> @th1 T n k g = @th1 T m k (f >>> g).
Proof. fext=> i /=. exact: th_comp1. Qed.

Lemma th1_compR {I : Type} {T : cgraded1} {m n k} (f : iren m n) (g : iren n k) (h : _ -> I) :
  @th1 T m n f >> (@th1 T n k g >> h) = @th1 T m k (f >>> g) >> h.
Proof. fext=> i /=. by rewrite th_comp1. Qed.

Lemma th2_idX {T : igraded2} {m n : nat} : @th2 T m n m n idren idren = id.
Proof. fext=> i. exact: th_id2. Qed.

Lemma th2_compX {T : cgraded2} {m1 m2 m3 n1 n2 n3} (f1 : iren m1 m2) (f2 : iren m2 m3) (g1 : iren n1 n2) (g2 : iren n2 n3) :
  @th2 T m1 n1 m2 n2 f1 g1 >> @th2 T m2 n2 m3 n3 f2 g2 = @th2 T m1 n1 m3 n3 (f1 >>> f2) (g1 >>> g2).
Proof. fext=> i /=. exact: th_comp2. Qed.

Lemma th2_compR {I : Type} {T : cgraded2} {m1 m2 m3 n1 n2 n3} (f1 : iren m1 m2) (f2 : iren m2 m3) (g1 : iren n1 n2) (g2 : iren n2 n3) (h : _ -> I) :
  @th2 T m1 n1 m2 n2 f1 g1 >> (@th2 T m2 n2 m3 n3 f2 g2 >> h) = @th2 T m1 n1 m3 n3 (f1 >>> f2) (g1 >>> g2) >> h.
Proof. fext=> i /=. by rewrite th_comp2. Qed.

Ltac gsimpl :=
  rewrite ?th1_idX ?th1_compX ?th1_compR
          ?th2_idX ?th2_compX ?th2_compR
          ?th_id1 ?th_comp1
          ?th_id2 ?th_comp2
          ?th1_finE
          ?th1_constE
          ?th1_boxE
          ?th1_predE
          ?th2_constlE
          ?th2_constrE
          ?th2_constE
          ?th2_boxE.
