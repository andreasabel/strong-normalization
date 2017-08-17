module SN where

open import Relation.Unary using (_∈_; _⊆_)
open import Library
open import Terms
open import Substitution
open import TermShape public


-- Inductive definition of strong normalization.

infix 7 _⟨_⟩⇒_ _⇒ˢ_

mutual

  -- Strongly normalizing evaluation contexts

  SNhole : ∀ {i : Size} {Γ : Cxt} {a b : Ty} → Tm Γ b → ECxt Γ a b → Tm Γ a → Set
  SNhole {i} = PCxt (SN {i})

  -- Strongly neutral terms.

  SNe : ∀ {i : Size} {Γ} {b} → Tm Γ b → Set
  SNe {i} = PNe (SN {i})

  -- Strongly normalizing terms.

  data SN {i : Size}{Γ} : ∀ {a} → Tm Γ a → Set where

    ne   : ∀ {j : Size< i} {a t}
           → (𝒏 : SNe {j} t)
           → SN {a = a} t

    abs  : ∀ {j : Size< i} {a b}{t : Tm (a ∷ Γ) b}
           → (𝒕 : SN {j} t)
           → SN (abs t)

    exp  : ∀ {j₁ j₂ : Size< i} {a t t′}
           → (t⇒ :  t ⟨ j₁ ⟩⇒ t′) (𝒕′ : SN {j₂} t′)
           → SN {a = a} t

  _⟨_⟩⇒_ : ∀ {Γ a} → Tm Γ a → Size → Tm Γ a → Set
  t ⟨ i ⟩⇒ t′ = SN {i} / t ⇒ t′

  -- Strong head reduction

  _⇒ˢ_ : ∀ {i : Size} {Γ} {a} → Tm Γ a → Tm Γ a → Set
  _⇒ˢ_ {i} t t' = (SN {i}) / t ⇒ t'


-- -- Inductive definition of strong normalization.

-- mutual

--   -- Strongly normalizing evaluation contexts

--   data SNhole {i : Size} (n : ℕ) {Γ : Cxt} : {a b : Ty} → Tm Γ b → ECxt Γ a b → Tm Γ a → Set where

--     appl  : ∀ {a b t u}
--             → (𝒖 : SN {i} n u)
--             → SNhole n (app t u) (appl u) (t ∶ (a →̂ b))

--   -- Strongly neutral terms.

--   data SNe {i : Size} (n : ℕ) {Γ} {b} : Tm Γ b → Set where

--     var  : ∀ x                              → SNe n (var x)

--     elim : ∀ {a} {t : Tm Γ a} {E Et}
--            → (𝒏 : SNe {i} n t) (𝑬𝒕 : SNhole {i} n Et E t) → SNe n Et
--     -- elim : ∀ {j₁ j₂ : Size< i}{a} {t : Tm Γ a} {E Et}
--     --        → (𝒏 : SNe {j₁} n t) (𝑬𝒕 : SNhole {j₂} n Et E t) → SNe n Et

--   -- Strongly normalizing terms.

--   data SN {i : Size}{Γ} : ℕ → ∀ {a} → Tm Γ a → Set where

--     ne   : ∀ {j : Size< i} {a n t}
--            → (𝒏 : SNe {j} n t)
--            → SN n {a} t

--     abs  : ∀ {j : Size< i} {a b n}{t : Tm (a ∷ Γ) b}
--            → (𝒕 : SN {j} n t)
--            → SN n (abs t)

--     exp  : ∀ {j₁ j₂ : Size< i} {a n t t′}
--            → (t⇒ : j₁ size t ⟨ n ⟩⇒ t′) (𝒕′ : SN {j₂} n t′)
--            → SN n {a} t

--   _size_⟨_⟩⇒_ : ∀ (i : Size) {Γ}{a} → Tm Γ a → ℕ → Tm Γ a → Set
--   i size t ⟨ n ⟩⇒ t′ = _⟨_⟩⇒_ {i} t n t′

--   -- Strong head reduction

--   data _⟨_⟩⇒_ {i : Size} {Γ} : ∀ {a} → Tm Γ a → ℕ → Tm Γ a → Set where

--     β     : ∀  {a b}{t : Tm (a ∷ Γ) b}{u}
--             → (𝒖 : SN {i} n u)
--             → (app (abs t) u) ⟨ n ⟩⇒ subst0 u t

--     cong  : ∀  {a b t t' Et Et'}{E : ECxt Γ a b}
--             → (𝑬𝒕 : Ehole Et E t)
--             → (𝑬𝒕' : Ehole Et' E t')
--             → (t⇒ : i size t ⟨ n ⟩⇒ t')
--             → Et ⟨ n ⟩⇒ Et'

    -- β     : ∀ {j : Size< i} {a b}{t : Tm (a ∷ Γ) b}{u}
    --         → (𝒖 : SN {j} n u)
    --         → (app (abs t) u) ⟨ n ⟩⇒ subst0 u t

    -- cong  : ∀ {j : Size< i} {a b t t' Et Et'}{E : ECxt Γ a b}
    --         → (𝑬𝒕 : Ehole Et E t)
    --         → (𝑬𝒕' : Ehole Et' E t')
    --         → (t⇒ : j size t ⟨ n ⟩⇒ t')
    --         → Et ⟨ n ⟩⇒ Et'

-- Strong head reduction is deterministic.

det⇒ : ∀ {a Γ} {t t₁ t₂ : Tm Γ a}
       → (t⇒₁ : t ⟨ _ ⟩⇒ t₁) (t⇒₂ : t ⟨ _ ⟩⇒ t₂) → t₁ ≡ t₂
det⇒ (β _) (β _)                                              = ≡.refl
det⇒ (β _) (cong (appl u) (appl .u) (cong () _ _))
det⇒ (cong (appl u) (appl .u) (cong () _ _)) (β _)
det⇒ (cong (appl u) (appl .u) x) (cong (appl .u) (appl .u) y) = ≡.cong (λ t → app t u) (det⇒ x y)

-- Strongly neutrals are closed under application.

sneApp : ∀{Γ a b}{t : Tm Γ (a →̂ b)}{u : Tm Γ a} →
  SNe t → SN u → SNe (app t u)
sneApp 𝒏 𝒖 = elim 𝒏 (appl 𝒖)

-- Substituting strongly neutral terms

record RenSubSNe {i} (vt : VarTm i) (Γ Δ : Cxt) : Set where
  constructor _,_
  field theSubst : RenSub vt Γ Δ
        isSNe    : ∀ {a} (x : Var Γ a) → SNe (vt2tm _ (theSubst x))
open RenSubSNe

RenSN    = RenSubSNe `Var
SubstSNe = RenSubSNe `Tm

-- The singleton SNe substitution.
-- Replaces the first variable by another variable.

sgs-varSNe : ∀ {Γ a} → Var Γ a → SubstSNe (a ∷ Γ) Γ
theSubst (sgs-varSNe x)         = sgs (var x)
isSNe    (sgs-varSNe x) (zero)  = (var x)
isSNe    (sgs-varSNe x) (suc y) = var y


-- The SN-notions are closed under SNe substitution.

mutual
  substSNh : ∀ {i vt Γ Δ a b} → (σ : RenSubSNe {i} vt Γ Δ) → ∀ {E : ECxt Γ a b}{Et t} → (SNh : SNhole Et E t)
                                → SNhole (subst (theSubst σ) Et) (substEC (theSubst σ) E) (subst (theSubst σ) t)
  substSNh σ (appl u) = appl (substSN σ u)

  subst⇒ : ∀ {i vt Γ Δ a} (σ : RenSubSNe {i} vt Γ Δ) {t t' : Tm Γ a} → t ⟨ _ ⟩⇒ t' → subst (theSubst σ) t ⟨ _ ⟩⇒ subst (theSubst σ) t'
  subst⇒ (σ , σ∈Ne) (β {t = t} {u = u} x) = ≡.subst (λ t' → app (abs (subst (lifts σ) t)) (subst σ u) ⟨ _ ⟩⇒ t')
                                                   (sgs-lifts-term {σ = σ} {u} {t})
                                                   (β {t = subst (lifts σ) t} (substSN (σ , σ∈Ne) x))

  subst⇒ σ (cong Eh Eh' t→t')    = cong (substEh (theSubst σ) Eh) (substEh (theSubst σ) Eh') (subst⇒ σ t→t')

  -- Lifting a SNe substitution.

  liftsSNe : ∀ {i vt Γ Δ a} → RenSubSNe {i} vt Γ Δ → RenSubSNe {i} vt (a ∷ Γ) (a ∷ Δ)
  theSubst (liftsSNe σ)                   = lifts (theSubst σ)
  isSNe    (liftsSNe {vt = `Var} (σ , σ∈SNe)) (zero)    = var (zero)
  isSNe    (liftsSNe {vt = `Var} (σ , σ∈SNe)) (suc y) = var (suc (σ y))
  isSNe    (liftsSNe {vt = `Tm } (σ , σ∈SNe)) (zero)    = var (zero)
  isSNe    (liftsSNe {vt = `Tm } (σ , σ∈SNe)) (suc y) = substSNe {vt = `Var} (suc , (λ x → var (suc x))) (σ∈SNe y)

  substSNe : ∀ {i vt Γ Δ τ} → (σ : RenSubSNe {i} vt Γ Δ) → ∀ {t : Tm Γ τ} → SNe t → SNe (subst (theSubst σ) t)
  substSNe σ (var x)            = isSNe σ x
  substSNe σ (elim t∈SNe E∈SNh) = elim (substSNe σ t∈SNe) (substSNh σ E∈SNh)

  substSN : ∀ {i vt Γ Δ τ} → (σ : RenSubSNe {i} vt Γ Δ) → ∀ {t : Tm Γ τ} → SN t → SN (subst (theSubst σ) t)
  substSN σ (ne t∈SNe)         = ne (substSNe σ t∈SNe)
  substSN σ (abs t∈SN)         = abs (substSN (liftsSNe σ) t∈SN)
  substSN σ (exp t→t' t'∈SN)   = exp (subst⇒ σ t→t') (substSN σ t'∈SN)


-- SN is closed under renaming.

renSN :  ∀{Γ Δ} (ρ : Γ ≤ Δ) → RenSN Δ Γ
renSN ρ = (ρ , λ x → var (ρ x))

renameSNe : ∀{a Γ Δ} (ρ : Γ ≤ Δ) {t : Tm Δ a} →
  SNe t → SNe (rename ρ t)
renameSNe ρ = substSNe (renSN ρ)

renameSN : ∀{a Γ Δ} (ρ : Γ ≤ Δ) {t : Tm Δ a} →
  SN t → SN (rename ρ t)
renameSN ρ = substSN (renSN ρ)

-- Variables are SN.

varSN : ∀{Γ a x} → var x ∈ SN {Γ = Γ} {a}
varSN = ne (var _)

-- SN is closed under application to variables.

appVarSN : ∀{Γ a b}{t : Tm Γ (a →̂ b)}{x} → t ∈ SN → app t (var x) ∈ SN
appVarSN (ne t∈SNe)       = ne (elim t∈SNe (appl varSN))
appVarSN (abs t∈SN)       = exp (β varSN) (substSN (sgs-varSNe _) t∈SN)
appVarSN (exp t→t' t'∈SN) = exp (cong (appl (var _)) (appl (var _)) t→t') (appVarSN t'∈SN)

-- Subterm properties of SN

-- If app t u ∈ SN then u ∈ SN.

apprSN : ∀{i a b Γ}{t : Tm Γ (a →̂ b)}{u : Tm Γ a} → SN {i} (app t u) → SN {i} u
apprSN (ne (elim 𝒏 (appl 𝒖)))               = 𝒖
apprSN (exp (β 𝒖) 𝒕)                        = 𝒖
apprSN (exp (cong (appl u) (appl .u) t⇒) 𝒕) = apprSN 𝒕
