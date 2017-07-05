module SN where

open import Relation.Unary using (_∈_; _⊆_)
open import Library
open import Terms
open import Substitution
open import TermShape public


-- Inductive definition of strong normalization.

infix 7 _size_⟨_⟩⇒_ _⟨_⟩⇒_

mutual

  -- Strongly normalizing evaluation contexts

  SNhole : ∀ {i : Size} (n : ℕ) {Γ : Cxt} {a b : Ty} → Tm Γ b → ECxt Γ a b → Tm Γ a → Set
  SNhole {i} n = PCxt (SN {i} n)

  -- Strongly neutral terms.

  SNe : ∀ {i : Size} (n : ℕ) {Γ} {b} → Tm Γ b → Set
  SNe {i} n = PNe (SN {i} n)

  -- Strongly normalizing terms.

  data SN {i : Size}{Γ} : ℕ → ∀ {a} → Tm Γ a → Set where

    ne   : ∀ {j : Size< i} {a n t}
           → (𝒏 : SNe {j} n t)
           → SN n {a} t

    abs  : ∀ {j : Size< i} {a b n}{t : Tm (a ∷ Γ) b}
           → (𝒕 : SN {j} n t)
           → SN n (abs t)

    exp  : ∀ {j₁ j₂ : Size< i} {a n t t′}
           → (t⇒ : j₁ size t ⟨ n ⟩⇒ t′) (𝒕′ : SN {j₂} n t′)
           → SN n {a} t

  _size_⟨_⟩⇒_ : ∀ (i : Size) {Γ}{a} → Tm Γ a → ℕ → Tm Γ a → Set
  i size t ⟨ n ⟩⇒ t′ = SN {i} n / t ⇒ t′

  -- Strong head reduction

  _⟨_⟩⇒_ : ∀ {i : Size} {Γ} {a} → Tm Γ a → ℕ → Tm Γ a → Set
  _⟨_⟩⇒_ {i} t n t' = (SN {i} n) / t ⇒ t'


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

--     β     : ∀  {n a b}{t : Tm (a ∷ Γ) b}{u}
--             → (𝒖 : SN {i} n u)
--             → (app (abs t) u) ⟨ n ⟩⇒ subst0 u t

--     cong  : ∀  {n a b t t' Et Et'}{E : ECxt Γ a b}
--             → (𝑬𝒕 : Ehole Et E t)
--             → (𝑬𝒕' : Ehole Et' E t')
--             → (t⇒ : i size t ⟨ n ⟩⇒ t')
--             → Et ⟨ n ⟩⇒ Et'

    -- β     : ∀ {j : Size< i} {n a b}{t : Tm (a ∷ Γ) b}{u}
    --         → (𝒖 : SN {j} n u)
    --         → (app (abs t) u) ⟨ n ⟩⇒ subst0 u t

    -- cong  : ∀ {j : Size< i} {n a b t t' Et Et'}{E : ECxt Γ a b}
    --         → (𝑬𝒕 : Ehole Et E t)
    --         → (𝑬𝒕' : Ehole Et' E t')
    --         → (t⇒ : j size t ⟨ n ⟩⇒ t')
    --         → Et ⟨ n ⟩⇒ Et'

-- Strong head reduction is deterministic.

det⇒ : ∀ {n a Γ} {t t₁ t₂ : Tm Γ a}
       → (t⇒₁ : t ⟨ n ⟩⇒ t₁) (t⇒₂ : t ⟨ n ⟩⇒ t₂) → t₁ ≡ t₂
det⇒ (β _) (β _)                                              = ≡.refl
det⇒ (β _) (cong (appl u) (appl .u) (cong () _ _))
det⇒ (cong (appl u) (appl .u) (cong () _ _)) (β _)
det⇒ (cong (appl u) (appl .u) x) (cong (appl .u) (appl .u) y) = ≡.cong (λ t → app t u) (det⇒ x y)

-- Strongly neutrals are closed under application.

sneApp : ∀{n Γ a b}{t : Tm Γ (a →̂ b)}{u : Tm Γ a} →
  SNe n t → SN n u → SNe n (app t u)
sneApp 𝒏 𝒖 = elim 𝒏 (appl 𝒖)

-- Functoriality of the SN-notions wrt. evaluation depth n.

-- TODO: these can be expressed in terms of the parametrized notions.
-- mapPNe etc.

mutual
  mapSNe : ∀ {m n} → .(m ≤ℕ n) → ∀ {Γ a}{t : Tm Γ a} → SNe n t -> SNe m t
  mapSNe m≤n (var x) = var x
  mapSNe m≤n (elim t∈Ne E∈SNh) = elim (mapSNe m≤n t∈Ne) (mapSNh m≤n E∈SNh)

  mapSN : ∀ {m n} → .(m ≤ℕ n) → ∀ {Γ a}{t : Tm Γ a} → SN n t -> SN m t
  mapSN m≤n (ne u∈SNe) = ne (mapSNe m≤n u∈SNe)
  mapSN m≤n (abs t∈SN) = abs (mapSN m≤n t∈SN)
  mapSN m≤n (exp t→t' t∈SN) = exp (map⇒ m≤n t→t') (mapSN m≤n t∈SN)

  map⇒ : ∀ {m n} → .(m ≤ℕ n) → ∀ {Γ a}{t t' : Tm Γ a} → t ⟨ n ⟩⇒ t' → t ⟨ m ⟩⇒ t'
  map⇒ m≤n (β t∈SN) = β (mapSN m≤n t∈SN)
  map⇒ m≤n (cong Et Et' t→t') = cong Et Et' (map⇒ m≤n t→t')

  mapSNh : ∀ {m n} → .(m ≤ℕ n) → ∀ {Γ a b}{E : ECxt Γ a b}{Et t} → SNhole n Et E t -> SNhole m Et E t
  mapSNh m≤n (appl u∈SN) = appl (mapSN m≤n u∈SN)



-- Substituting strongly neutral terms

record RenSubSNe {i} (vt : VarTm i) (n : ℕ) (Γ Δ : Cxt) : Set where
  constructor _,_
  field theSubst : RenSub vt Γ Δ
        isSNe    : ∀ {a} (x : Var Γ a) → SNe n (vt2tm _ (theSubst x))
open RenSubSNe

RenSN    = RenSubSNe `Var
SubstSNe = RenSubSNe `Tm

-- Substitutions are functorial in the evaluation depth n

mapSubSNe : ∀ {i vt Γ Δ m n} → m ≤ℕ n → RenSubSNe {i} vt n Γ Δ → RenSubSNe vt m Γ Δ
mapSubSNe m≤n (σ , σ∈SNe) = σ , (λ x → mapSNe m≤n (σ∈SNe x))

-- The singleton SNe substitution.
-- Replaces the first variable by another variable.

sgs-varSNe : ∀ {n Γ a} → Var Γ a → SubstSNe n (a ∷ Γ) Γ
theSubst (sgs-varSNe x)         = sgs (var x)
isSNe    (sgs-varSNe x) (zero)  = (var x)
isSNe    (sgs-varSNe x) (suc y) = var y


-- The SN-notions are closed under SNe substitution.

mutual
  substSNh : ∀ {i vt Γ Δ a b n} → (σ : RenSubSNe {i} vt n Γ Δ) → ∀ {E : ECxt Γ a b}{Et t} → (SNh : SNhole n Et E t)
                                → SNhole n (subst (theSubst σ) Et) (substEC (theSubst σ) E) (subst (theSubst σ) t)
  substSNh σ (appl u) = appl (substSN σ u)

  subst⇒ : ∀ {i vt Γ Δ a n} (σ : RenSubSNe {i} vt n Γ Δ) {t t' : Tm Γ a} → t ⟨ n ⟩⇒ t' → subst (theSubst σ) t ⟨ n ⟩⇒ subst (theSubst σ) t'
  subst⇒ {n = n} (σ , σ∈Ne) (β {t = t} {u = u} x) = ≡.subst (λ t' → app (abs (subst (lifts σ) t)) (subst σ u) ⟨ n ⟩⇒ t')
                                                   (sgs-lifts-term {σ = σ} {u} {t})
                                                   (β {t = subst (lifts σ) t} (substSN (σ , σ∈Ne) x))

  subst⇒ {n = n} σ (cong Eh Eh' t→t')    = cong (substEh (theSubst σ) Eh) (substEh (theSubst σ) Eh') (subst⇒ σ t→t')

  -- Lifting a SNe substitution.

  liftsSNe : ∀ {i vt Γ Δ a n} → RenSubSNe {i} vt n Γ Δ → RenSubSNe {i} vt n (a ∷ Γ) (a ∷ Δ)
  theSubst (liftsSNe σ)                   = lifts (theSubst σ)
  isSNe    (liftsSNe {vt = `Var} (σ , σ∈SNe)) (zero)    = var (zero)
  isSNe    (liftsSNe {vt = `Var} (σ , σ∈SNe)) (suc y) = var (suc (σ y))
  isSNe    (liftsSNe {vt = `Tm } (σ , σ∈SNe)) (zero)    = var (zero)
  isSNe    (liftsSNe {vt = `Tm } (σ , σ∈SNe)) (suc y) = substSNe {vt = `Var} (suc , (λ x → var (suc x))) (σ∈SNe y)

  substSNe : ∀ {i vt Γ Δ τ n} → (σ : RenSubSNe {i} vt n Γ Δ) → ∀ {t : Tm Γ τ} → SNe n t → SNe n (subst (theSubst σ) t)
  substSNe σ (var x)            = isSNe σ x
  substSNe σ (elim t∈SNe E∈SNh) = elim (substSNe σ t∈SNe) (substSNh σ E∈SNh)

  substSN : ∀ {i vt Γ Δ τ n} → (σ : RenSubSNe {i} vt n Γ Δ) → ∀ {t : Tm Γ τ} → SN n t → SN n (subst (theSubst σ) t)
  substSN σ (ne t∈SNe)         = ne (substSNe σ t∈SNe)
  substSN σ (abs t∈SN)         = abs (substSN (liftsSNe σ) t∈SN)
  substSN σ (exp t→t' t'∈SN)   = exp (subst⇒ σ t→t') (substSN σ t'∈SN)


-- SN is closed under renaming.

renSN :  ∀{n Γ Δ} (ρ : Γ ≤ Δ) → RenSN n Δ Γ
renSN ρ = (ρ , λ x → var (ρ x))

renameSNe : ∀{n a Γ Δ} (ρ : Γ ≤ Δ) {t : Tm Δ a} →
  SNe n t → SNe n (rename ρ t)
renameSNe ρ = substSNe (renSN ρ)

renameSN : ∀{n a Γ Δ} (ρ : Γ ≤ Δ) {t : Tm Δ a} →
  SN n t → SN n (rename ρ t)
renameSN ρ = substSN (renSN ρ)

-- Variables are SN.

varSN : ∀{Γ a n x} → var x ∈ SN {Γ = Γ} n {a}
varSN = ne (var _)

-- SN is closed under application to variables.

appVarSN : ∀{Γ a b n}{t : Tm Γ (a →̂ b)}{x} → t ∈ SN n → app t (var x) ∈ SN n
appVarSN (ne t∈SNe)       = ne (elim t∈SNe (appl varSN))
appVarSN (abs t∈SN)       = exp (β varSN) (substSN (sgs-varSNe _) t∈SN)
appVarSN (exp t→t' t'∈SN) = exp (cong (appl (var _)) (appl (var _)) t→t') (appVarSN t'∈SN)

-- Subterm properties of SN

-- If app t u ∈ SN then u ∈ SN.

apprSN : ∀{i n a b Γ}{t : Tm Γ (a →̂ b)}{u : Tm Γ a} → SN {i} n (app t u) → SN {i} n u
apprSN (ne (elim 𝒏 (appl 𝒖)))               = 𝒖
apprSN (exp (β 𝒖) 𝒕)                        = 𝒖
apprSN (exp (cong (appl u) (appl .u) t⇒) 𝒕) = apprSN 𝒕
