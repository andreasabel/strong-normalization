{-# OPTIONS --copatterns --sized-types #-}

module SN.AntiRename where

open import Relation.Unary using (_∈_; _⊆_)

open import Library
open import Terms
open import Substitution
open import SN


mutual

  -- To formulate this, we need heterogeneous SNholes, going from Γ to Δ

  -- unRenameSNh : ∀{a b Γ Δ} (ρ : Δ ≤ Γ) {t : Tm Γ b} {E : ECxt Γ a b} {t' : Tm Γ a} →
  --   SNhole (subst ρ t) (λ t' → subst ρ (E t')) t' → SNhole t E t'
  -- unRenameSNh = TODO

  unRenameSNe : ∀{a Γ Δ} {ρ : Δ ≤ Γ} {t : Tm Γ a}{t'} → IndRen ρ t t' →
                SNe t' → SNe t
  unRenameSNe (var x x₁)     (var y)           = var x
  unRenameSNe (app is is₁)   (elim 𝒏 (appl 𝒖)) = elim (unRenameSNe is 𝒏) (appl (unRenameSN is₁ 𝒖))

  unRenameSN : ∀{a Γ Δ} {ρ : Δ ≤ Γ} {t : Tm Γ a} {t'} → IndRen ρ t t'
    → SN t' → SN t
  -- neutral cases:
  unRenameSN n           (ne 𝒏)       = ne (unRenameSNe n 𝒏)
  -- redex cases:
  unRenameSN is           (exp t⇒ 𝒕)   = exp (unRename⇒1 is t⇒) (unRenameSN (proj₂ (unRename⇒0 is t⇒)) 𝒕)
  -- constructor cases:
  unRenameSN (abs t)      (abs 𝒕)      = abs (unRenameSN t 𝒕)

  unRename⇒0 : ∀{a Γ Δ} {ρ : Δ ≤ Γ} {t : Tm Γ a} {t' : Tm Δ a}{tρ} → IndRen ρ t tρ
              → tρ ⟨ _ ⟩⇒ t' → Σ _ \ s → IndRen ρ s t'
  unRename⇒0 {ρ = ρ} (app {u = u} (abs {t = t} is) is₁)  (β 𝒖)  = _ , prop→Ind ρ (≡.trans (≡.sym (sgs-lifts-term {σ = ρ} {u = u} {t = t}))
                                                                      (≡.cong₂ (λ t₁ u₁ → subst (sgs u₁) t₁) (Ind→prop _ is) (Ind→prop _ is₁)))
  unRename⇒0 (app is is₁)        (cong (appl u) (appl .u) tρ→t') = let s , iss = unRename⇒0 is tρ→t' in app s _ , app iss is₁

  unRename⇒1 : ∀{a Γ Δ} {ρ : Δ ≤ Γ} {t : Tm Γ a} {t' : Tm Δ a}{tρ} → (is : IndRen ρ t tρ)
              → (t⇒ : tρ ⟨ _ ⟩⇒ t') → t ⟨ _  ⟩⇒ proj₁ (unRename⇒0 is t⇒)
  unRename⇒1 (app (abs is) is₁) (β 𝒖) = β (unRenameSN is₁ 𝒖)
  unRename⇒1 (app is is₁)        (cong (appl u) (appl .u) tρ→t') = cong (appl _) (appl _) (unRename⇒1 is tρ→t')


-- Extensionality of SN for function types:
-- If t x ∈ SN then t ∈ SN.

absVarSNe : ∀{Γ a b}{t : Tm (a ∷ Γ) (a →̂ b)} → app t (var (zero)) ∈ SNe → t ∈ SNe
absVarSNe (elim 𝒏 (appl 𝒖)) = 𝒏

absVarSN : ∀{Γ a b}{t : Tm (a ∷ Γ) (a →̂ b)} → app t (var (zero)) ∈ SN → t ∈ SN
absVarSN (ne 𝒖)                                                   = ne (absVarSNe 𝒖)
absVarSN (exp (β {t = t} 𝒖) 𝒕′)                                   = abs (unRenameSN (prop→Ind contract (subst-ext contract-sgs t)) 𝒕′)
absVarSN (exp (cong (appl ._) (appl ._) t⇒) 𝒕′) = exp t⇒ (absVarSN 𝒕′)
