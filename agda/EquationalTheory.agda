module EquationalTheory where

open import Library
open import Syntax
open import RenamingAndSubstitution

-- Single collapsing substitution.

sub1 : ∀{Γ σ τ} → Tm Γ σ → Tm (Γ , σ) τ → Tm Γ τ
sub1 {Γ}{σ}{τ} u t = sub (subId , u) t

-- Typed β-η-equality.

data _≡βη_ {Γ : Cxt} : ∀{σ} → Tm Γ σ → Tm Γ σ → Set where

  -- Axioms.

  beta≡  : ∀{σ τ} {t : Tm (Γ , σ) τ} {u : Tm Γ σ} →

           --------------------------
           app (abs t) u ≡βη sub1 u t

  eta≡   : ∀{σ τ} (t : Tm Γ (σ ⇒ τ)) →

           -------------------------------------
           abs (app (weak _ t) (var zero)) ≡βη t

  -- Congruence rules.

  var≡   : ∀{σ} (x : Var Γ σ) →

           ---------------
           var x ≡βη var x

  abs≡   : ∀{σ τ}{t t' : Tm (Γ , σ) τ} →

           t ≡βη t' →
           ----------------
           abs t ≡βη abs t'

  app≡   : ∀{σ τ}{t t' : Tm Γ (σ ⇒ τ)}{u u' : Tm Γ σ} →

          t ≡βη t' → u ≡βη u' →
          ---------------------
          app t u ≡βη app t' u'

  -- Equivalence rules.

  refl≡  : ∀{a} (t {t'} : Tm Γ a) →

           t ≡ t' →
           -------
           t ≡βη t'

  sym≡   : ∀{a}{t t' : Tm Γ a}

           (t'≡t : t' ≡βη t) →
           -----------------
           t ≡βη t'

  trans≡ : ∀{a}{t₁ t₂ t₃ : Tm Γ a}

           (t₁≡t₂ : t₁ ≡βη t₂) (t₂≡t₃ : t₂ ≡βη t₃) →
           ----------------------------------
           t₁ ≡βη t₃

-- A calculation on renamings needed for renaming of eta≡.

ren-eta≡ : ∀ {Γ Δ a b} (t : Tm Γ (a ⇒ b)) (ρ : Ren Δ Γ) →
        ren (wkr ρ , zero) (ren (wkr renId) t) ≡ ren (wkr {σ = a} renId) (ren ρ t)
ren-eta≡ t ρ = begin
  ren (wkr ρ , zero) (ren (wkr renId) t)     ≡⟨ sym (rencomp _ _ _) ⟩
  ren (renComp (wkr ρ , zero) (wkr renId)) t ≡⟨ cong (λ ρ₁ → ren ρ₁ t) (lemrr _ _ _) ⟩
  ren (renComp (wkr ρ) renId) t              ≡⟨ cong (λ ρ₁ → ren ρ₁ t) (ridr _) ⟩
  ren (wkr ρ) t                              ≡⟨ cong (λ ρ₁ → ren ρ₁ t) (cong wkr (sym (lidr _))) ⟩
  ren (wkr (renComp renId ρ)) t              ≡⟨ cong (λ ρ₁ → ren ρ₁ t) (sym (wkrcomp _ _)) ⟩
  ren (renComp (wkr renId) ρ) t              ≡⟨ rencomp _ _ _ ⟩
  ren (wkr renId) (ren ρ t)                  ∎ where open ≡-Reasoning

-- Definitional equality is closed under renaming.

ren≡βη : ∀{Γ a} {t : Tm Γ a}{t' : Tm Γ a} → t ≡βη t' → ∀{Δ}(ρ : Ren Δ Γ) →
        ren ρ t ≡βη ren ρ t'

ren≡βη (beta≡ {t = t}{u = u}) ρ = trans≡ beta≡ $ refl≡ _ $
  trans (subren (subId , ren ρ u) (liftr ρ) t)
        (trans (cong (λ xs → sub xs t)
                     (cong₂ Sub._,_
                            (trans (lemsr subId (ren ρ u) ρ)
                            (trans (sidl (ren2sub ρ)) (sym $ sidr (ren2sub ρ))))
                            (ren2subren ρ u)))
               (sym $ rensub ρ (subId , u) t))
  -- TODO: factor out reasoning about renamings and substitutions

ren≡βη (eta≡ {a} t) ρ rewrite ren-eta≡ t ρ = eta≡ (ren ρ t)

-- OLD:
-- ren≡βη (eta≡ t) ρ = trans≡
--   (abs≡ (app≡ (refl≡ _
--     (trans (sym $ rencomp (liftr ρ) (wkr renId) t)
--            (trans (cong (λ xs → ren xs t)
--                         (trans (lemrr (wkr ρ) zero renId)
--                                (trans (ridr (wkr ρ))
--                                       (trans (cong wkr (sym (lidr ρ)))
--                                              (sym (wkrcomp renId ρ))))))
--                   (rencomp (wkr renId) ρ t))))
--     (refl≡ _)))
--   (eta≡ _)

ren≡βη (var≡ x)       ρ = var≡ (lookr ρ x)
ren≡βη (abs≡ p)       ρ = abs≡ (ren≡βη p (liftr ρ))
ren≡βη (app≡ p q)     ρ = app≡ (ren≡βη p ρ) (ren≡βη q ρ)

ren≡βη (refl≡ _ refl) ρ = refl≡ _ refl
ren≡βη (sym≡ p)       ρ = sym≡ (ren≡βη p ρ)
ren≡βη (trans≡ p q)   ρ = trans≡ (ren≡βη p ρ) (ren≡βη q ρ)
