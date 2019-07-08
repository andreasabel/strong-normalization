Require Export fintype.

Inductive ty  : Type :=
  | Base : ty 
  | Fun : ty  -> ty  -> ty 
  | Plus : ty  -> ty  -> ty .

Lemma congr_Base  : Base  = Base  .
Proof. congruence. Qed.

Lemma congr_Fun  { s0 : ty  } { s1 : ty  } { t0 : ty  } { t1 : ty  } : s0 = t0 -> s1 = t1 -> Fun s0 s1 = Fun t0 t1 .
Proof. congruence. Qed.

Lemma congr_Plus  { s0 : ty  } { s1 : ty  } { t0 : ty  } { t1 : ty  } : s0 = t0 -> s1 = t1 -> Plus s0 s1 = Plus t0 t1 .
Proof. congruence. Qed.

Inductive tm (ntm : nat) : Type :=
  | var_tm : fin (ntm) -> tm (ntm)
  | app : tm (ntm) -> tm (ntm) -> tm (ntm)
  | lam : ty  -> tm (S ntm) -> tm (ntm)
  | inl : tm (ntm) -> tm (ntm)
  | inr : tm (ntm) -> tm (ntm)
  | orelim : tm (ntm) -> tm (S ntm) -> tm (S ntm) -> tm (ntm).

Lemma congr_app { mtm : nat } { s0 : tm (mtm) } { s1 : tm (mtm) } { t0 : tm (mtm) } { t1 : tm (mtm) } : s0 = t0 -> s1 = t1 -> app (mtm) s0 s1 = app (mtm) t0 t1 .
Proof. congruence. Qed.

Lemma congr_lam { mtm : nat } { s0 : ty  } { s1 : tm (S mtm) } { t0 : ty  } { t1 : tm (S mtm) } : s0 = t0 -> s1 = t1 -> lam (mtm) s0 s1 = lam (mtm) t0 t1 .
Proof. congruence. Qed.

Lemma congr_inl { mtm : nat } { s0 : tm (mtm) } { t0 : tm (mtm) } : s0 = t0 -> inl (mtm) s0 = inl (mtm) t0 .
Proof. congruence. Qed.

Lemma congr_inr { mtm : nat } { s0 : tm (mtm) } { t0 : tm (mtm) } : s0 = t0 -> inr (mtm) s0 = inr (mtm) t0 .
Proof. congruence. Qed.

Lemma congr_orelim { mtm : nat } { s0 : tm (mtm) } { s1 : tm (S mtm) } { s2 : tm (S mtm) } { t0 : tm (mtm) } { t1 : tm (S mtm) } { t2 : tm (S mtm) } : s0 = t0 -> s1 = t1 -> s2 = t2 -> orelim (mtm) s0 s1 s2 = orelim (mtm) t0 t1 t2 .
Proof. congruence. Qed.

Definition upRen_tm_tm { m : nat } { n : nat } (xi : fin (m) -> fin (n)) : _ :=
  up_ren xi.

Fixpoint ren_tm { mtm : nat } { ntm : nat } (xitm : fin (mtm) -> fin (ntm)) (s : tm (mtm)) : _ :=
    match s with
    | var_tm (_) s => (var_tm (ntm)) (xitm s)
    | app (_) s0 s1 => app (ntm) (ren_tm xitm s0) (ren_tm xitm s1)
    | lam (_) s0 s1 => lam (ntm) s0 (ren_tm (upRen_tm_tm xitm) s1)
    | inl (_) s0 => inl (ntm) (ren_tm xitm s0)
    | inr (_) s0 => inr (ntm) (ren_tm xitm s0)
    | orelim (_) s0 s1 s2 => orelim (ntm) (ren_tm xitm s0) (ren_tm (upRen_tm_tm xitm) s1) (ren_tm (upRen_tm_tm xitm) s2)
    end.

Definition up_tm_tm { m : nat } { ntm : nat } (sigma : fin (m) -> tm (ntm)) : _ :=
  scons ((var_tm (S ntm)) var_zero) (funcomp (ren_tm shift) sigma).

Fixpoint subst_tm { mtm : nat } { ntm : nat } (sigmatm : fin (mtm) -> tm (ntm)) (s : tm (mtm)) : _ :=
    match s with
    | var_tm (_) s => sigmatm s
    | app (_) s0 s1 => app (ntm) (subst_tm sigmatm s0) (subst_tm sigmatm s1)
    | lam (_) s0 s1 => lam (ntm) s0 (subst_tm (up_tm_tm sigmatm) s1)
    | inl (_) s0 => inl (ntm) (subst_tm sigmatm s0)
    | inr (_) s0 => inr (ntm) (subst_tm sigmatm s0)
    | orelim (_) s0 s1 s2 => orelim (ntm) (subst_tm sigmatm s0) (subst_tm (up_tm_tm sigmatm) s1) (subst_tm (up_tm_tm sigmatm) s2)
    end.

Definition upId_tm_tm { mtm : nat } (sigma : fin (mtm) -> tm (mtm)) (Eq : forall x, sigma x = (var_tm (mtm)) x) : forall x, (up_tm_tm sigma) x = (var_tm (S mtm)) x :=
  fun n => match n with
  | Some n => ap (ren_tm shift) (Eq n)
  | None => eq_refl
  end.

Fixpoint idSubst_tm { mtm : nat } (sigmatm : fin (mtm) -> tm (mtm)) (Eqtm : forall x, sigmatm x = (var_tm (mtm)) x) (s : tm (mtm)) : subst_tm sigmatm s = s :=
    match s with
    | var_tm (_) s => Eqtm s
    | app (_) s0 s1 => congr_app (idSubst_tm sigmatm Eqtm s0) (idSubst_tm sigmatm Eqtm s1)
    | lam (_) s0 s1 => congr_lam (eq_refl s0) (idSubst_tm (up_tm_tm sigmatm) (upId_tm_tm (_) Eqtm) s1)
    | inl (_) s0 => congr_inl (idSubst_tm sigmatm Eqtm s0)
    | inr (_) s0 => congr_inr (idSubst_tm sigmatm Eqtm s0)
    | orelim (_) s0 s1 s2 => congr_orelim (idSubst_tm sigmatm Eqtm s0) (idSubst_tm (up_tm_tm sigmatm) (upId_tm_tm (_) Eqtm) s1) (idSubst_tm (up_tm_tm sigmatm) (upId_tm_tm (_) Eqtm) s2)
    end.

Definition upExtRen_tm_tm { m : nat } { n : nat } (xi : fin (m) -> fin (n)) (zeta : fin (m) -> fin (n)) (Eq : forall x, xi x = zeta x) : forall x, (upRen_tm_tm xi) x = (upRen_tm_tm zeta) x :=
  fun n => match n with
  | Some n => ap shift (Eq n)
  | None => eq_refl
  end.

Fixpoint extRen_tm { mtm : nat } { ntm : nat } (xitm : fin (mtm) -> fin (ntm)) (zetatm : fin (mtm) -> fin (ntm)) (Eqtm : forall x, xitm x = zetatm x) (s : tm (mtm)) : ren_tm xitm s = ren_tm zetatm s :=
    match s with
    | var_tm (_) s => ap (var_tm (ntm)) (Eqtm s)
    | app (_) s0 s1 => congr_app (extRen_tm xitm zetatm Eqtm s0) (extRen_tm xitm zetatm Eqtm s1)
    | lam (_) s0 s1 => congr_lam (eq_refl s0) (extRen_tm (upRen_tm_tm xitm) (upRen_tm_tm zetatm) (upExtRen_tm_tm (_) (_) Eqtm) s1)
    | inl (_) s0 => congr_inl (extRen_tm xitm zetatm Eqtm s0)
    | inr (_) s0 => congr_inr (extRen_tm xitm zetatm Eqtm s0)
    | orelim (_) s0 s1 s2 => congr_orelim (extRen_tm xitm zetatm Eqtm s0) (extRen_tm (upRen_tm_tm xitm) (upRen_tm_tm zetatm) (upExtRen_tm_tm (_) (_) Eqtm) s1) (extRen_tm (upRen_tm_tm xitm) (upRen_tm_tm zetatm) (upExtRen_tm_tm (_) (_) Eqtm) s2)
    end.

Definition upExt_tm_tm { m : nat } { ntm : nat } (sigma : fin (m) -> tm (ntm)) (tau : fin (m) -> tm (ntm)) (Eq : forall x, sigma x = tau x) : forall x, (up_tm_tm sigma) x = (up_tm_tm tau) x :=
  fun n => match n with
  | Some n => ap (ren_tm shift) (Eq n)
  | None => eq_refl
  end.

Fixpoint ext_tm { mtm : nat } { ntm : nat } (sigmatm : fin (mtm) -> tm (ntm)) (tautm : fin (mtm) -> tm (ntm)) (Eqtm : forall x, sigmatm x = tautm x) (s : tm (mtm)) : subst_tm sigmatm s = subst_tm tautm s :=
    match s with
    | var_tm (_) s => Eqtm s
    | app (_) s0 s1 => congr_app (ext_tm sigmatm tautm Eqtm s0) (ext_tm sigmatm tautm Eqtm s1)
    | lam (_) s0 s1 => congr_lam (eq_refl s0) (ext_tm (up_tm_tm sigmatm) (up_tm_tm tautm) (upExt_tm_tm (_) (_) Eqtm) s1)
    | inl (_) s0 => congr_inl (ext_tm sigmatm tautm Eqtm s0)
    | inr (_) s0 => congr_inr (ext_tm sigmatm tautm Eqtm s0)
    | orelim (_) s0 s1 s2 => congr_orelim (ext_tm sigmatm tautm Eqtm s0) (ext_tm (up_tm_tm sigmatm) (up_tm_tm tautm) (upExt_tm_tm (_) (_) Eqtm) s1) (ext_tm (up_tm_tm sigmatm) (up_tm_tm tautm) (upExt_tm_tm (_) (_) Eqtm) s2)
    end.

Fixpoint compRenRen_tm { ktm : nat } { ltm : nat } { mtm : nat } (xitm : fin (mtm) -> fin (ktm)) (zetatm : fin (ktm) -> fin (ltm)) (rhotm : fin (mtm) -> fin (ltm)) (Eqtm : forall x, (funcomp zetatm xitm) x = rhotm x) (s : tm (mtm)) : ren_tm zetatm (ren_tm xitm s) = ren_tm rhotm s :=
    match s with
    | var_tm (_) s => ap (var_tm (ltm)) (Eqtm s)
    | app (_) s0 s1 => congr_app (compRenRen_tm xitm zetatm rhotm Eqtm s0) (compRenRen_tm xitm zetatm rhotm Eqtm s1)
    | lam (_) s0 s1 => congr_lam (eq_refl s0) (compRenRen_tm (upRen_tm_tm xitm) (upRen_tm_tm zetatm) (upRen_tm_tm rhotm) (up_ren_ren (_) (_) (_) Eqtm) s1)
    | inl (_) s0 => congr_inl (compRenRen_tm xitm zetatm rhotm Eqtm s0)
    | inr (_) s0 => congr_inr (compRenRen_tm xitm zetatm rhotm Eqtm s0)
    | orelim (_) s0 s1 s2 => congr_orelim (compRenRen_tm xitm zetatm rhotm Eqtm s0) (compRenRen_tm (upRen_tm_tm xitm) (upRen_tm_tm zetatm) (upRen_tm_tm rhotm) (up_ren_ren (_) (_) (_) Eqtm) s1) (compRenRen_tm (upRen_tm_tm xitm) (upRen_tm_tm zetatm) (upRen_tm_tm rhotm) (up_ren_ren (_) (_) (_) Eqtm) s2)
    end.

Definition up_ren_subst_tm_tm { k : nat } { l : nat } { mtm : nat } (xi : fin (k) -> fin (l)) (tau : fin (l) -> tm (mtm)) (theta : fin (k) -> tm (mtm)) (Eq : forall x, (funcomp tau xi) x = theta x) : forall x, (funcomp (up_tm_tm tau) (upRen_tm_tm xi)) x = (up_tm_tm theta) x :=
  fun n => match n with
  | Some n => ap (ren_tm shift) (Eq n)
  | None => eq_refl
  end.

Fixpoint compRenSubst_tm { ktm : nat } { ltm : nat } { mtm : nat } (xitm : fin (mtm) -> fin (ktm)) (tautm : fin (ktm) -> tm (ltm)) (thetatm : fin (mtm) -> tm (ltm)) (Eqtm : forall x, (funcomp tautm xitm) x = thetatm x) (s : tm (mtm)) : subst_tm tautm (ren_tm xitm s) = subst_tm thetatm s :=
    match s with
    | var_tm (_) s => Eqtm s
    | app (_) s0 s1 => congr_app (compRenSubst_tm xitm tautm thetatm Eqtm s0) (compRenSubst_tm xitm tautm thetatm Eqtm s1)
    | lam (_) s0 s1 => congr_lam (eq_refl s0) (compRenSubst_tm (upRen_tm_tm xitm) (up_tm_tm tautm) (up_tm_tm thetatm) (up_ren_subst_tm_tm (_) (_) (_) Eqtm) s1)
    | inl (_) s0 => congr_inl (compRenSubst_tm xitm tautm thetatm Eqtm s0)
    | inr (_) s0 => congr_inr (compRenSubst_tm xitm tautm thetatm Eqtm s0)
    | orelim (_) s0 s1 s2 => congr_orelim (compRenSubst_tm xitm tautm thetatm Eqtm s0) (compRenSubst_tm (upRen_tm_tm xitm) (up_tm_tm tautm) (up_tm_tm thetatm) (up_ren_subst_tm_tm (_) (_) (_) Eqtm) s1) (compRenSubst_tm (upRen_tm_tm xitm) (up_tm_tm tautm) (up_tm_tm thetatm) (up_ren_subst_tm_tm (_) (_) (_) Eqtm) s2)
    end.

Definition up_subst_ren_tm_tm { k : nat } { ltm : nat } { mtm : nat } (sigma : fin (k) -> tm (ltm)) (zetatm : fin (ltm) -> fin (mtm)) (theta : fin (k) -> tm (mtm)) (Eq : forall x, (funcomp (ren_tm zetatm) sigma) x = theta x) : forall x, (funcomp (ren_tm (upRen_tm_tm zetatm)) (up_tm_tm sigma)) x = (up_tm_tm theta) x :=
  fun n => match n with
  | Some n => eq_trans (compRenRen_tm shift (upRen_tm_tm zetatm) (funcomp shift zetatm) (fun x => eq_refl) (sigma n)) (eq_trans (eq_sym (compRenRen_tm zetatm shift (funcomp shift zetatm) (fun x => eq_refl) (sigma n))) (ap (ren_tm shift) (Eq n)))
  | None => eq_refl
  end.

Fixpoint compSubstRen__tm { ktm : nat } { ltm : nat } { mtm : nat } (sigmatm : fin (mtm) -> tm (ktm)) (zetatm : fin (ktm) -> fin (ltm)) (thetatm : fin (mtm) -> tm (ltm)) (Eqtm : forall x, (funcomp (ren_tm zetatm) sigmatm) x = thetatm x) (s : tm (mtm)) : ren_tm zetatm (subst_tm sigmatm s) = subst_tm thetatm s :=
    match s with
    | var_tm (_) s => Eqtm s
    | app (_) s0 s1 => congr_app (compSubstRen__tm sigmatm zetatm thetatm Eqtm s0) (compSubstRen__tm sigmatm zetatm thetatm Eqtm s1)
    | lam (_) s0 s1 => congr_lam (eq_refl s0) (compSubstRen__tm (up_tm_tm sigmatm) (upRen_tm_tm zetatm) (up_tm_tm thetatm) (up_subst_ren_tm_tm (_) (_) (_) Eqtm) s1)
    | inl (_) s0 => congr_inl (compSubstRen__tm sigmatm zetatm thetatm Eqtm s0)
    | inr (_) s0 => congr_inr (compSubstRen__tm sigmatm zetatm thetatm Eqtm s0)
    | orelim (_) s0 s1 s2 => congr_orelim (compSubstRen__tm sigmatm zetatm thetatm Eqtm s0) (compSubstRen__tm (up_tm_tm sigmatm) (upRen_tm_tm zetatm) (up_tm_tm thetatm) (up_subst_ren_tm_tm (_) (_) (_) Eqtm) s1) (compSubstRen__tm (up_tm_tm sigmatm) (upRen_tm_tm zetatm) (up_tm_tm thetatm) (up_subst_ren_tm_tm (_) (_) (_) Eqtm) s2)
    end.

Definition up_subst_subst_tm_tm { k : nat } { ltm : nat } { mtm : nat } (sigma : fin (k) -> tm (ltm)) (tautm : fin (ltm) -> tm (mtm)) (theta : fin (k) -> tm (mtm)) (Eq : forall x, (funcomp (subst_tm tautm) sigma) x = theta x) : forall x, (funcomp (subst_tm (up_tm_tm tautm)) (up_tm_tm sigma)) x = (up_tm_tm theta) x :=
  fun n => match n with
  | Some n => eq_trans (compRenSubst_tm shift (up_tm_tm tautm) (funcomp (up_tm_tm tautm) shift) (fun x => eq_refl) (sigma n)) (eq_trans (eq_sym (compSubstRen__tm tautm shift (funcomp (ren_tm shift) tautm) (fun x => eq_refl) (sigma n))) (ap (ren_tm shift) (Eq n)))
  | None => eq_refl
  end.

Fixpoint compSubstSubst_tm { ktm : nat } { ltm : nat } { mtm : nat } (sigmatm : fin (mtm) -> tm (ktm)) (tautm : fin (ktm) -> tm (ltm)) (thetatm : fin (mtm) -> tm (ltm)) (Eqtm : forall x, (funcomp (subst_tm tautm) sigmatm) x = thetatm x) (s : tm (mtm)) : subst_tm tautm (subst_tm sigmatm s) = subst_tm thetatm s :=
    match s with
    | var_tm (_) s => Eqtm s
    | app (_) s0 s1 => congr_app (compSubstSubst_tm sigmatm tautm thetatm Eqtm s0) (compSubstSubst_tm sigmatm tautm thetatm Eqtm s1)
    | lam (_) s0 s1 => congr_lam (eq_refl s0) (compSubstSubst_tm (up_tm_tm sigmatm) (up_tm_tm tautm) (up_tm_tm thetatm) (up_subst_subst_tm_tm (_) (_) (_) Eqtm) s1)
    | inl (_) s0 => congr_inl (compSubstSubst_tm sigmatm tautm thetatm Eqtm s0)
    | inr (_) s0 => congr_inr (compSubstSubst_tm sigmatm tautm thetatm Eqtm s0)
    | orelim (_) s0 s1 s2 => congr_orelim (compSubstSubst_tm sigmatm tautm thetatm Eqtm s0) (compSubstSubst_tm (up_tm_tm sigmatm) (up_tm_tm tautm) (up_tm_tm thetatm) (up_subst_subst_tm_tm (_) (_) (_) Eqtm) s1) (compSubstSubst_tm (up_tm_tm sigmatm) (up_tm_tm tautm) (up_tm_tm thetatm) (up_subst_subst_tm_tm (_) (_) (_) Eqtm) s2)
    end.

Definition rinstInst_up_tm_tm { m : nat } { ntm : nat } (xi : fin (m) -> fin (ntm)) (sigma : fin (m) -> tm (ntm)) (Eq : forall x, (funcomp (var_tm (ntm)) xi) x = sigma x) : forall x, (funcomp (var_tm (S ntm)) (upRen_tm_tm xi)) x = (up_tm_tm sigma) x :=
  fun n => match n with
  | Some n => ap (ren_tm shift) (Eq n)
  | None => eq_refl
  end.

Fixpoint rinst_inst_tm { mtm : nat } { ntm : nat } (xitm : fin (mtm) -> fin (ntm)) (sigmatm : fin (mtm) -> tm (ntm)) (Eqtm : forall x, (funcomp (var_tm (ntm)) xitm) x = sigmatm x) (s : tm (mtm)) : ren_tm xitm s = subst_tm sigmatm s :=
    match s with
    | var_tm (_) s => Eqtm s
    | app (_) s0 s1 => congr_app (rinst_inst_tm xitm sigmatm Eqtm s0) (rinst_inst_tm xitm sigmatm Eqtm s1)
    | lam (_) s0 s1 => congr_lam (eq_refl s0) (rinst_inst_tm (upRen_tm_tm xitm) (up_tm_tm sigmatm) (rinstInst_up_tm_tm (_) (_) Eqtm) s1)
    | inl (_) s0 => congr_inl (rinst_inst_tm xitm sigmatm Eqtm s0)
    | inr (_) s0 => congr_inr (rinst_inst_tm xitm sigmatm Eqtm s0)
    | orelim (_) s0 s1 s2 => congr_orelim (rinst_inst_tm xitm sigmatm Eqtm s0) (rinst_inst_tm (upRen_tm_tm xitm) (up_tm_tm sigmatm) (rinstInst_up_tm_tm (_) (_) Eqtm) s1) (rinst_inst_tm (upRen_tm_tm xitm) (up_tm_tm sigmatm) (rinstInst_up_tm_tm (_) (_) Eqtm) s2)
    end.

Lemma rinstInst_tm { mtm : nat } { ntm : nat } (xitm : fin (mtm) -> fin (ntm)) : ren_tm xitm = subst_tm (funcomp (var_tm (ntm)) xitm) .
Proof. exact (FunctionalExtensionality.functional_extensionality _ _ (fun x => rinst_inst_tm xitm (_) (fun n => eq_refl) x)). Qed.

Lemma instId_tm { mtm : nat } : subst_tm (var_tm (mtm)) = id .
Proof. exact (FunctionalExtensionality.functional_extensionality _ _ (fun x => idSubst_tm (var_tm (mtm)) (fun n => eq_refl) (id x))). Qed.

Lemma rinstId_tm { mtm : nat } : @ren_tm (mtm) (mtm) id = id .
Proof. exact (eq_trans (rinstInst_tm id) instId_tm). Qed.

Lemma varL_tm { mtm : nat } { ntm : nat } (sigmatm : fin (mtm) -> tm (ntm)) : funcomp (subst_tm sigmatm) (var_tm (mtm)) = sigmatm .
Proof. exact (FunctionalExtensionality.functional_extensionality _ _ (fun x => eq_refl)). Qed.

Lemma varLRen_tm { mtm : nat } { ntm : nat } (xitm : fin (mtm) -> fin (ntm)) : funcomp (ren_tm xitm) (var_tm (mtm)) = funcomp (var_tm (ntm)) xitm .
Proof. exact (FunctionalExtensionality.functional_extensionality _ _ (fun x => eq_refl)). Qed.

Lemma compComp_tm { ktm : nat } { ltm : nat } { mtm : nat } (sigmatm : fin (mtm) -> tm (ktm)) (tautm : fin (ktm) -> tm (ltm)) (s : tm (mtm)) : subst_tm tautm (subst_tm sigmatm s) = subst_tm (funcomp (subst_tm tautm) sigmatm) s .
Proof. exact (compSubstSubst_tm sigmatm tautm (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_tm { ktm : nat } { ltm : nat } { mtm : nat } (sigmatm : fin (mtm) -> tm (ktm)) (tautm : fin (ktm) -> tm (ltm)) : funcomp (subst_tm tautm) (subst_tm sigmatm) = subst_tm (funcomp (subst_tm tautm) sigmatm) .
Proof. exact (FunctionalExtensionality.functional_extensionality _ _ (fun n => compComp_tm sigmatm tautm n)). Qed.

Lemma compRen_tm { ktm : nat } { ltm : nat } { mtm : nat } (sigmatm : fin (mtm) -> tm (ktm)) (zetatm : fin (ktm) -> fin (ltm)) (s : tm (mtm)) : ren_tm zetatm (subst_tm sigmatm s) = subst_tm (funcomp (ren_tm zetatm) sigmatm) s .
Proof. exact (compSubstRen__tm sigmatm zetatm (_) (fun n => eq_refl) s). Qed.

Lemma compRen'_tm { ktm : nat } { ltm : nat } { mtm : nat } (sigmatm : fin (mtm) -> tm (ktm)) (zetatm : fin (ktm) -> fin (ltm)) : funcomp (ren_tm zetatm) (subst_tm sigmatm) = subst_tm (funcomp (ren_tm zetatm) sigmatm) .
Proof. exact (FunctionalExtensionality.functional_extensionality _ _ (fun n => compRen_tm sigmatm zetatm n)). Qed.

Lemma renComp_tm { ktm : nat } { ltm : nat } { mtm : nat } (xitm : fin (mtm) -> fin (ktm)) (tautm : fin (ktm) -> tm (ltm)) (s : tm (mtm)) : subst_tm tautm (ren_tm xitm s) = subst_tm (funcomp tautm xitm) s .
Proof. exact (compRenSubst_tm xitm tautm (_) (fun n => eq_refl) s). Qed.

Lemma renComp'_tm { ktm : nat } { ltm : nat } { mtm : nat } (xitm : fin (mtm) -> fin (ktm)) (tautm : fin (ktm) -> tm (ltm)) : funcomp (subst_tm tautm) (ren_tm xitm) = subst_tm (funcomp tautm xitm) .
Proof. exact (FunctionalExtensionality.functional_extensionality _ _ (fun n => renComp_tm xitm tautm n)). Qed.

Lemma renRen_tm { ktm : nat } { ltm : nat } { mtm : nat } (xitm : fin (mtm) -> fin (ktm)) (zetatm : fin (ktm) -> fin (ltm)) (s : tm (mtm)) : ren_tm zetatm (ren_tm xitm s) = ren_tm (funcomp zetatm xitm) s .
Proof. exact (compRenRen_tm xitm zetatm (_) (fun n => eq_refl) s). Qed.

Lemma renRen'_tm { ktm : nat } { ltm : nat } { mtm : nat } (xitm : fin (mtm) -> fin (ktm)) (zetatm : fin (ktm) -> fin (ltm)) : funcomp (ren_tm zetatm) (ren_tm xitm) = ren_tm (funcomp zetatm xitm) .
Proof. exact (FunctionalExtensionality.functional_extensionality _ _ (fun n => renRen_tm xitm zetatm n)). Qed.

Arguments var_tm {ntm}.

Arguments app {ntm}.

Arguments lam {ntm}.

Arguments inl {ntm}.

Arguments inr {ntm}.

Arguments orelim {ntm}.

Instance Subst_tm { mtm : nat } { ntm : nat } : Subst1 (fin (mtm) -> tm (ntm)) (tm (mtm)) (tm (ntm)) := @subst_tm (mtm) (ntm) .

Instance Ren_tm { mtm : nat } { ntm : nat } : Ren1 (fin (mtm) -> fin (ntm)) (tm (mtm)) (tm (ntm)) := @ren_tm (mtm) (ntm) .

Instance VarInstance_tm { mtm : nat } : Var (fin (mtm)) (tm (mtm)) := @var_tm (mtm) .

Notation "x '__tm'" := (var_tm x) (at level 5, format "x __tm") : subst_scope.

Notation "x '__tm'" := (@ids (_) (_) VarInstance_tm x) (at level 5, only printing, format "x __tm") : subst_scope.

Notation "'var'" := (var_tm) (only printing, at level 1) : subst_scope.

Class Up_tm X Y := up_tm : X -> Y.

Notation "↑__tm" := (up_tm) (only printing) : subst_scope.

Notation "↑__tm" := (up_tm_tm) (only printing) : subst_scope.

Instance Up_tm_tm { m : nat } { ntm : nat } : Up_tm (_) (_) := @up_tm_tm (m) (ntm) .

Notation "s [ sigmatm ]" := (subst_tm sigmatm s) (at level 7, left associativity, only printing) : subst_scope.

Notation "s ⟨ xitm ⟩" := (ren_tm xitm s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmatm ]" := (subst_tm sigmatm) (at level 1, left associativity, only printing) : fscope.

Notation "⟨ xitm ⟩" := (ren_tm xitm) (at level 1, left associativity, only printing) : fscope.

Ltac auto_unfold := repeat unfold subst1,  ren1,  subst2,  ren2,  Subst1,  Ren1,  Subst2,  Ren2,  ids,  Subst_tm,  Ren_tm,  VarInstance_tm.

Tactic Notation "auto_unfold" "in" "*" := repeat unfold subst1,  ren1,  subst2,  ren2,  Subst1,  Ren1,  Subst2,  Ren2,  ids,  Subst_tm,  Ren_tm,  VarInstance_tm in *.

Ltac asimpl' := repeat first [progress rewrite ?instId_tm| progress rewrite ?rinstId_tm| progress rewrite ?compComp_tm| progress rewrite ?compComp'_tm| progress rewrite ?compRen_tm| progress rewrite ?compRen'_tm| progress rewrite ?renComp_tm| progress rewrite ?renComp'_tm| progress rewrite ?renRen_tm| progress rewrite ?renRen'_tm| progress rewrite ?varL_tm| progress rewrite ?varLRen_tm| progress (unfold up_ren, upRen_tm_tm, up_tm_tm)| progress (cbn [subst_tm ren_tm])| fsimpl].

Ltac asimpl := repeat try unfold_funcomp; auto_unfold in *; asimpl'; repeat try unfold_funcomp.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case (asimpl; cbn; eauto).

Tactic Notation "asimpl" "in" "*" := auto_unfold in *; repeat first [progress rewrite ?instId_tm in *| progress rewrite ?rinstId_tm in *| progress rewrite ?compComp_tm in *| progress rewrite ?compComp'_tm in *| progress rewrite ?compRen_tm in *| progress rewrite ?compRen'_tm in *| progress rewrite ?renComp_tm in *| progress rewrite ?renComp'_tm in *| progress rewrite ?renRen_tm in *| progress rewrite ?renRen'_tm in *| progress rewrite ?varL_tm in *| progress rewrite ?varLRen_tm in *| progress (unfold up_ren, upRen_tm_tm, up_tm_tm in *)| progress (cbn [subst_tm ren_tm] in *)| fsimpl in *].

Ltac substify := auto_unfold; try repeat (erewrite rinst_inst_tm; [|now intros]).

Ltac renamify := auto_unfold; try repeat (erewrite <- rinst_inst_tm; [|intros; now asimpl]).
