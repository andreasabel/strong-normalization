module Reduction where

open import Data.Sum
open import Library
open import Terms
open import Substitution
open import TermShape
open import SN

data βECxt (Γ : Cxt) : (Δ : Cxt) (a b : Ty) → Set where
  appl  : ∀ {a b} (u : Tm Γ a)          → βECxt Γ Γ (a →̂ b) b
  appr  : ∀ {a b} (t : Tm Γ (a →̂  b))   → βECxt Γ Γ a b
  abs   : ∀ {a b}                       → βECxt Γ (a ∷ Γ) b (a →̂  b)

data βEhole {Γ : Cxt} : {Δ : Cxt} {b a : Ty} → Tm Γ b → βECxt Γ Δ a b → Tm Δ a → Set where
  appl  : ∀ {a b} {t : Tm Γ (a →̂ b)} (u : Tm Γ a)  → βEhole (app t u) (appl u) t
  appr  : ∀ {a b u} (t : Tm Γ (a →̂  b))            → βEhole (app t u) (appr t) u
  abs   : ∀ {a b} {t : Tm (a ∷ Γ) b}               → βEhole (abs t) abs t


mkHole : ∀ {Γ Δ} {a b} (E : βECxt Γ Δ a b) {t} → ∃ λ E[t] → βEhole E[t] E t
mkHole (appl u)  = _ , appl u
mkHole (appr t)  = _ , appr t
mkHole abs       = _ , abs

data _⇒β_ {Γ} : ∀ {a} → Tm Γ a → Tm Γ a → Set where

  β     : ∀ {a b}{t : Tm (a ∷ Γ) b}{u}
          → (app (abs t) u) ⇒β subst0 u t

  cong  : ∀ {Δ a b t t' Et Et'}{E : βECxt Γ Δ a b}
          → (𝑬𝒕 : βEhole Et E t)
          → (𝑬𝒕' : βEhole Et' E t')
          → (t⇒β : t ⇒β t')
          → Et ⇒β Et'


subst⇒β : ∀ {m vt a Γ} {t t' : Tm Γ a} {Δ}
           (σ : RenSub {m} vt Γ Δ) → t ⇒β t' → subst σ t ⇒β subst σ t'
subst⇒β σ (β {t = t} {u = u})            = ≡.subst (λ t' → app (abs (subst (lifts σ) t)) (subst σ u) ⇒β t')
                                                   (sgs-lifts-term {σ = σ} {u} {t})
                                           β
subst⇒β σ (cong (appl u) (appl .u) t⇒)   = cong (appl _) (appl _) (subst⇒β σ t⇒)
subst⇒β σ (cong (appr t₁) (appr .t₁) t⇒) = cong (appr _) (appr _) (subst⇒β σ t⇒)
subst⇒β σ (cong abs abs t⇒)              = cong abs abs (subst⇒β (lifts σ) t⇒)

infix 7 _⇒β_ _⇒β*_

data _⇒β*_ {Γ} {a} : Tm Γ a → Tm Γ a → Set where
  []  : ∀ {t} → t ⇒β* t
  _∷_ : ∀ {ti tm to} → ti ⇒β tm → tm ⇒β* to → ti ⇒β* to

_++β_ : ∀ {Γ} {a} {t₀ t₁ t₂ : Tm Γ a} → t₀ ⇒β* t₁ → t₁ ⇒β* t₂ → t₀ ⇒β* t₂
[]       ++β ys = ys
(x ∷ xs) ++β ys = x ∷ (xs ++β ys)

cong* : ∀ {a Γ Δ} {b} {t tβ* : Tm Γ a} {E : βECxt Δ Γ a b}{E[t] E[tβ*]} → βEhole E[t] E t → βEhole E[tβ*] E tβ* → t ⇒β* tβ* → E[t] ⇒β* E[tβ*]
cong* E1         E2          (x ∷ t⇒) = cong E1 (proj₂ (mkHole _)) x ∷ cong* (proj₂ (mkHole _)) E2 t⇒
cong* (appl u)   (appl .u)   []       = []
cong* (appr t₁)  (appr .t₁)  []       = []
cong* abs        abs         []       = []

mutual
  EC→βEC : ∀ {Γ} {a b} (E : ECxt Γ a b) → βECxt Γ Γ a b
  EC→βEC (appl u) = appl u

  mkHole4 : ∀ {Γ} {a b} (E : ECxt Γ a b) {t : Tm Γ a} → βEhole (E [ t ]) (EC→βEC E) t
  mkHole4 (appl u) = appl u

cong*3 : ∀ {Γ a b t t'}(E : ECxt* Γ a b)
          → (t⇒ : t ⇒β t')
          → E [ t ]* ⇒β E [ t' ]*
cong*3 [] t⇒ = t⇒
cong*3 (x ∷ E) t⇒ = cong*3 E (cong (mkHole4 x) (mkHole4 x) t⇒)

cong*4 : ∀ {Γ a b t t'}(E : ECxt* Γ a b)
          → (t⇒ : t ⇒β* t')
          → E [ t ]* ⇒β* E [ t' ]*
cong*4 E [] = []
cong*4 E (x ∷ xs) = cong*3 E x ∷ cong*4 E xs

subst⇒β*₀ : ∀ {m vt a Γ} {t t' : Tm Γ a} {Δ} (σ : RenSub {m} vt Γ Δ) → t ⇒β* t' → subst σ t ⇒β* subst σ t'
subst⇒β*₀ σ [] = []
subst⇒β*₀ σ (x ∷ xs) = (subst⇒β σ x) ∷ (subst⇒β*₀ σ xs)

-- map⇒β : ∀ {m n} → .(m ≤ℕ n) → ∀ {Γ a}{t t' : Tm Γ a} → t ⟨ n ⟩⇒ t' → t ⟨ m ⟩⇒ t'
-- map⇒β m≤n (β t∈SN) = β (mapSN m≤n t∈SN)
-- map⇒β m≤n (cong Et Et' t→t') = cong Et Et' (map⇒ m≤n t→t')

mutual
  subst⇒β* : ∀ {m vt a Γ} {Δ} {σ ρ : RenSub {m} vt Γ Δ} → (∀ {b} (x : Var Γ b) → vt2tm _ (σ x) ⇒β* vt2tm _ (ρ x))
             → (t : Tm Γ a) → subst σ t ⇒β* subst ρ t
  subst⇒β* σ₁ (var x) = σ₁ x
  subst⇒β* {vt = vt} σ₁ (abs t) = cong* abs abs (subst⇒β* (lifts⇒β* {vt = vt} σ₁) t)
  subst⇒β* σ₁ (app t t₁) = cong* (appl _) (appl _) (subst⇒β* σ₁ t) ++β cong* (appr _) (appr _) (subst⇒β* σ₁ t₁)

  lifts⇒β* : ∀ {m vt a Γ} {Δ} {σ ρ : RenSub {m} vt Γ Δ} → (∀ {b} (x : Var Γ b) → vt2tm _ (σ x) ⇒β* vt2tm _ (ρ x))
             →  (∀ {b} (x : Var (a ∷ Γ) b) → vt2tm _ (lifts {a = a} σ x) ⇒β* vt2tm _ (lifts {a = a} ρ x))
  lifts⇒β* {vt = `Var} σ₁ (zero) = []
  lifts⇒β* {vt = `Tm}  σ₁ (zero) = []
  lifts⇒β* {vt = `Var} σ₁ (suc x)   = subst⇒β*₀ {vt = `Var} suc (σ₁ x)
  lifts⇒β* {vt = `Tm}  σ₁ (suc x)   = subst⇒β*₀ {vt = `Var} suc (σ₁ x)

mutual
  beta-shr : ∀ {i a Γ} {t tβ th : Tm Γ a} → t ⇒β tβ → t ⟨ i ⟩⇒ th → (tβ ≡ th) ⊎ Σ _ \ t' → tβ ⟨ i ⟩⇒ t' × th ⇒β* t'
  beta-shr β (β 𝒖)                                                   = inj₁ ≡.refl
  beta-shr (cong (appl u) (appl .u) (cong abs abs tβ⇒)) (β 𝒖)        = inj₂ (_ , β 𝒖 , (subst⇒β (sgs u) tβ⇒ ∷ []))
  beta-shr (cong (appr ._) (appr ._) tβ⇒) (β {t = t} 𝒖)
    = inj₂ (_ , β (mapβSN tβ⇒ 𝒖) , subst⇒β* {vt = `Tm} (λ { {._} (zero) → tβ⇒ ∷ [] ; (suc x) → [] }) t)
  beta-shr β (cong (appl u) (appl .u) (cong () 𝑬𝒕' th⇒))
  beta-shr (cong E1 E2 t⇒) (cong E0 E3 th⇒)                          = helper E1 E2 t⇒ E0 E3 th⇒

    where
      helper : ∀ {i}{a Γ} {t tβ th : Tm Γ a} {Δ a₁} {t₁ ta : Tm Δ a₁}
           {E : βECxt Γ Δ a₁ a} {a₂} {t₂ tb : Tm Γ a₂} {E₁ : ECxt Γ a₂ a} →
         βEhole t E t₁ →
         βEhole tβ E ta →
         t₁ ⇒β ta →
         Ehole t E₁ t₂ →
         Ehole th E₁ tb →
         t₂ ⟨ i ⟩⇒ tb →
         tβ ≡ th ⊎
         Σ (Tm Γ a) (λ tm → Σ (tβ ⟨ i ⟩⇒ tm) (λ x → th ⇒β* tm))
      helper (appl u) (appl .u) t⇒₁ (appl .u) (appl .u) th⇒₁ with beta-shr t⇒₁ th⇒₁
      helper (appl u) (appl .u) t⇒₁ (appl .u) (appl .u) th⇒₁ | inj₁ ≡.refl = inj₁ ≡.refl
      helper (appl u) (appl .u) t⇒₁ (appl .u) (appl .u) th⇒₁ | inj₂ (tm , h⇒tm , tm⇒β)
             = inj₂ (_ , cong (appl _) (appl _) h⇒tm , cong* (appl _) (appl _) tm⇒β)
      helper (appr t₂) (appr .t₂) t⇒₁ (appl t₁) (appl .t₁) th⇒₁ = inj₂ (_ , cong (appl _) (appl _) th⇒₁ , (cong (appr _) (appr _) t⇒₁ ∷ []))

  mapβSNe : ∀ {i a Γ} {t t' : Tm Γ a} → t ⇒β t' → SNe {i} t → SNe {i} t'
  mapβSNe β                                     (elim (elim 𝒏 ()) (appl 𝒖))
  mapβSNe (cong (appl u) (appl .u) t⇒)          (elim 𝒏 (appl 𝒖))   = elim (mapβSNe t⇒ 𝒏) (appl 𝒖)
  mapβSNe (cong (appr t₁) (appr .t₁) t⇒)        (elim 𝒏 (appl 𝒖))   = elim 𝒏 (appl (mapβSN t⇒ 𝒖))
  mapβSNe (cong abs abs t⇒)                     (elim 𝒏 ())

  mapβSN : ∀ {i a Γ} {t t' : Tm Γ a} → t ⇒β t' → SN {i} t → SN {i} t'
  mapβSN t⇒                (ne 𝒏)                      = ne (mapβSNe t⇒ 𝒏)
  mapβSN (cong abs abs t⇒) (abs 𝒕)                     = abs (mapβSN t⇒ 𝒕)
  mapβSN t⇒                (exp t⇒₁ 𝒕)                 with beta-shr t⇒ t⇒₁
  mapβSN t⇒ (exp t⇒₁ 𝒕) | inj₁ ≡.refl = 𝒕
  mapβSN t⇒ (exp t⇒₁ 𝒕) | inj₂ (_ , t⇒h , t⇒β*) = exp t⇒h (mapβ*SN t⇒β* 𝒕)

  mapβ*SN : ∀ {i a Γ} {t t' : Tm Γ a} → t ⇒β* t' → SN {i} t → SN {i} t'
  mapβ*SN []          𝒕 = 𝒕
  mapβ*SN (t⇒ ∷ t⇒β*) 𝒕 = mapβ*SN t⇒β* (mapβSN t⇒ 𝒕)
