-- Saturated sets.

module SAT3 where

open import Library
open import Terms
open import Substitution
open import Reduction
open import SN
open import SN.AntiRename

-- Kripke predicates on well-typed terms.

TmSet : (a : Ty) → Set₁
TmSet a = {Γ : Cxt} (t : Tm Γ a) → Set

_⊆_ : ∀{a} (𝑨 𝑨′ : TmSet a) → Set
𝑨 ⊆ 𝑨′ = ∀{Γ}{t : Tm Γ _} → 𝑨 t → 𝑨′ t

-- Closure by strong head expansion

Closed : ∀ {a} (𝑨 : TmSet a) → Set
Closed 𝑨 = ∀{Γ}{t t' : Tm Γ _} → t ⟨ _ ⟩⇒ t' → 𝑨 t' → 𝑨 t

data Cl {a} (𝑨 : TmSet a) {Γ} (t : Tm Γ a) : Set where
  emb : 𝑨 t                             → Cl 𝑨 t
  exp : ∀{t'} → t ⟨ _ ⟩⇒ t' → Cl 𝑨 t' → Cl 𝑨 t

-- Function space.

_[→]_ : ∀{a b} → TmSet a → TmSet b → TmSet (a →̂ b)
(𝓐 [→] 𝓑) {Γ} t = ∀{Δ} (ρ : Δ ≤ Γ) → {u : Tm Δ _} → 𝓐 u → 𝓑 (app (rename ρ t) u)

-- Saturated term sets.

record IsSAT {a} (𝑨 : TmSet a) : Set where
  -- constructor isSat
  field
    satSNe  : SNe ⊆ 𝑨
    satSN   : 𝑨 ⊆ SN
    satExp  : Closed 𝑨
    satRename : ∀ {Γ Δ} → (ρ : Ren Γ Δ) → ∀ {t} → 𝑨 t → 𝑨 (subst ρ t)
--open IsSAT

record SAT (a : Ty) : Set₁ where
  -- constructor sat
  field
    satSet  : TmSet a
    satProp : IsSAT satSet

  open IsSAT satProp public
open SAT public

-- Elementhood for saturated sets.
-- We use a record to instead of just application to help Agda's unifier.
record _∈_ {a Γ} (t : Tm Γ a) (𝓐 : SAT a) : Set where
  constructor ↿_
  field       ⇃_ : satSet 𝓐 t
open _∈_ public

-- Variables inhabit saturated sets.

⟦var⟧ : ∀{a} (𝓐 : SAT a) {Γ} (x : Var Γ a) → var x ∈ 𝓐
⟦var⟧ 𝓐 x = ↿ (satSNe 𝓐 (var x))

-- Smallest semantic type.

⟦⊥⟧ : SAT base
⟦⊥⟧ = record
  { satSet  = SN
  ; satProp = record
    { satSNe    = ne
    ; satSN     = id
    ; satExp    = exp
    ; satRename = renameSN
    }
  }

-- Semantic function type.

_⟦→⟧_ : ∀ {a b} (𝓐 : SAT a) (𝓑 : SAT b) → SAT (a →̂ b)
𝓐 ⟦→⟧ 𝓑 = record
  { satSet  = 𝑪
  ; satProp = record
    { satSNe = CSNe
    ; satSN  = CSN
    ; satExp = CExp
    ; satRename = λ ρ {t} 𝒕 ρ₁ {u} 𝒖 → ≡.subst (λ t₁ → 𝑩 (app t₁ u)) (subst-∙ ρ₁ ρ t) (𝒕 (λ x₂ → ρ₁ (ρ x₂)) 𝒖)
    }
  }
  where
    module 𝓐 = SAT 𝓐
    module 𝓑 = SAT 𝓑
    𝑨 = 𝓐.satSet
    𝑩 = 𝓑.satSet
    𝑪 : TmSet (_ →̂ _)
    𝑪 t = (𝑨 [→] 𝑩) t

    CSNe : SNe ⊆ 𝑪
    CSNe 𝒏 ρ 𝒖 = 𝓑.satSNe (sneApp (renameSNe ρ 𝒏) (𝓐.satSN 𝒖))

    CSN : 𝑪 ⊆ SN
    CSN 𝒕 = unRenameSN (prop→Ind suc ≡.refl) (absVarSN (𝓑.satSN (𝒕 _ (𝓐.satSNe (var v₀)))))

    CExp : ∀{Γ}{t t' : Tm Γ _} → t ⟨ _ ⟩⇒ t' → 𝑪 t' → 𝑪 t
    CExp t⇒ 𝒕 ρ 𝒖 = 𝓑.satExp ((cong (appl _) (appl _) (subst⇒ (renSN ρ) t⇒))) (𝒕 ρ 𝒖)


-- Lemma: If 𝓐, 𝓑 ∈ SAT and t[u] ∈ 𝓑 for all a ∈ 𝓐, then λt ∈ 𝓐 ⟦→⟧ 𝓑

⟦abs⟧ : ∀{a b}{𝓐 : SAT a}{𝓑 : SAT b}{Γ}{t : Tm (a ∷ Γ) b} →
    (∀ {Δ} (ρ : Δ ≤ Γ) {u : Tm Δ a} →
      u ∈ 𝓐 → (subst0 u (subst (lifts ρ) t)) ∈ 𝓑 ) → abs t ∈ (𝓐 ⟦→⟧ 𝓑)
(⇃ ⟦abs⟧ {𝓐 = 𝓐}{𝓑 = 𝓑} 𝒕) ρ 𝒖 =
  SAT.satExp 𝓑 (β (SAT.satSN 𝓐 𝒖)) (⇃ 𝒕 ρ (↿ 𝒖))

-- Lemma: If 𝓐, 𝓑 ∈ SAT and t ∈ 𝓐 ⟦→⟧ 𝓑 and u ∈ 𝓐, then app t u ∈ 𝓑

⟦app⟧ : ∀ {a b} {𝓐 : SAT a} {𝓑 : SAT b} {Γ} {t : Tm Γ (a →̂ b)} {u : Tm Γ a} →
        t ∈ (𝓐 ⟦→⟧ 𝓑) → u ∈ 𝓐 → app t u ∈ 𝓑
⟦app⟧ {𝓑 = 𝓑} {u = u} (↿ 𝒕) (↿ 𝒖) = ≡.subst (λ t → app t u ∈ 𝓑) renId (↿ 𝒕 _ 𝒖)
