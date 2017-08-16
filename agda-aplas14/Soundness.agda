{-# OPTIONS --allow-unsolved-metas #-}

-- Type interpretation and soundness of typing.

module Soundness where

open import Library
open import Terms
open import Substitution
open import SN
open import SN.AntiRename
open import SAT3

-- Type interpretation

⟦_⟧ : (a : Ty) → SAT a
⟦ base  ⟧  = {!!}
⟦ a →̂ b ⟧  = ⟦ a ⟧  ⟦→⟧ ⟦ b ⟧

-- Context interpretation (semantic substitutions)

⟦_⟧C : ∀ Γ → ∀ {Δ} (σ : Subst Γ Δ) → Set
⟦ Γ ⟧C σ = ∀ {a} (x : Var Γ a) → σ x ∈ ⟦ a ⟧

Ext : ∀ {a Δ Γ} {t : Tm Δ a} → (𝒕 : t ∈ (⟦ a ⟧)) →
      ∀ {σ : Subst Γ Δ} (θ : ⟦ Γ ⟧C σ) → ⟦ a ∷ Γ ⟧C (t ∷s σ)
Ext {a} 𝒕 θ (zero)  = 𝒕
Ext {a} 𝒕 θ (suc x) = θ x

Rename : ∀ {Δ Δ'} → (ρ : Ren Δ Δ') →
         ∀ {Γ}{σ : Subst Γ Δ} (θ : ⟦ Γ ⟧C σ) →
         ⟦ Γ ⟧C (ρ •s σ)
Rename ρ θ {a} x = ↿ SAT.satRename ⟦ a ⟧ ρ (⇃ θ x)


sound : ∀ {a Γ} (t : Tm Γ a) {Δ} {σ : Subst Γ Δ} → (θ : ⟦ Γ ⟧C σ) → subst σ t ∈ (⟦ a ⟧)
sound (var x) θ = θ x
sound (abs t) {σ = σ} θ = ⟦abs⟧ {𝓐 = ⟦ _ ⟧} {𝓑 = ⟦ _ ⟧} (λ ρ {u} 𝑢 →
  let open ≡-Reasoning
      eq : subst (u ∷s (ρ •s σ)) t ≡ subst0 u (subst (lifts ρ) (subst (lifts σ) t))
      eq = begin

             subst (u ∷s (ρ •s σ)) t

           ≡⟨ subst-ext (cons-to-sgs u _) t ⟩

              subst (sgs u •s lifts (ρ •s σ)) t

           ≡⟨ subst-∙ _ _ t ⟩

             subst0 u (subst (lifts (ρ •s σ)) t)

           ≡⟨ ≡.cong (subst0 u) (subst-ext (lifts-∙ ρ σ) t) ⟩

             subst0 u (subst (lifts ρ •s lifts σ) t)

           ≡⟨ ≡.cong (subst0 u) (subst-∙ (lifts ρ) (lifts σ) t) ⟩

             subst0 u (subst (lifts ρ) (subst (lifts σ) t))
           ∎
  in (≡.subst (_∈ ⟦ _ ⟧) eq (↿ (⇃ sound t (Ext (↿ (⇃ 𝑢)) ((Rename ρ θ)))))))

sound (app t u) θ = ↿ (⇃ ⟦app⟧ {𝓐 = ⟦ _ ⟧} {𝓑 = ⟦ _ ⟧} (sound t θ) (↿ (⇃ sound u θ)))
-- -}
