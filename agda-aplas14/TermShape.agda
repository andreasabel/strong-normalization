module TermShape where

open import Relation.Unary using (_∈_; _⊆_)
open import Size
open import Library
open import Terms
open import Substitution


-- Evaluation contexts.

data ECxt (Γ : Cxt) : (a b : Ty) → Set where
  appl  : ∀ {a b} (u : Tm Γ a)  → ECxt Γ (a →̂ b) b

-- Ehole Et E t ~~ Et = E[t]

data Ehole {Γ : Cxt} : {a b : Ty} → Tm Γ b → ECxt Γ a b → Tm Γ a → Set where
  appl  : ∀ {a b} {t : Tm Γ (a →̂ b)} (u : Tm Γ a)  → Ehole (app t u) (appl u) t


-- Evaluation contexts are closed under substitution.

substEC : ∀ {i vt Γ Δ a b} → (σ : RenSub {i} vt Γ Δ) → ECxt Γ a b → ECxt Δ a b
substEC σ (appl u) = appl (subst σ u)

substEh : ∀ {i vt Γ Δ a b} → (σ : RenSub {i} vt Γ Δ) → ∀ {E}{Et : Tm Γ b}{t : Tm Γ a} → (Eh : Ehole Et E t)
            → Ehole (subst σ Et) (substEC σ E) (subst σ t)
substEh σ (appl u) = appl (subst σ u)

mkEHole : ∀ {Γ} {a b} (E : ECxt Γ a b) {t} → ∃ λ E[t] → Ehole E[t] E t
mkEHole (appl u)  = _ , appl u


_[_] : ∀ {Γ} {a b} (E : ECxt Γ a b) (t : Tm Γ a) → Tm Γ b
E [ t ] = proj₁ (mkEHole E {t})

data ECxt* (Γ : Cxt) : Ty → Ty → Set where
  [] : ∀ {a} → ECxt* Γ a a
  _∷_ : ∀ {a₀ a₁ a₂} → ECxt Γ a₀ a₁ → ECxt* Γ a₁ a₂ → ECxt* Γ a₀ a₂

_[_]* : ∀ {Γ} {a b} (E : ECxt* Γ a b) (t : Tm Γ a) → Tm Γ b
[] [ t ]* = t
(E ∷ Es) [ t ]* = Es [ E [ t ] ]*

_++*_ : ∀ {Γ a b c} → ECxt* Γ a b → ECxt* Γ b c → ECxt* Γ a c
[] ++* ys = ys
(x ∷ xs) ++* ys = x ∷ (xs ++* ys)

_∷r_ : ∀ {Γ a b c} → ECxt* Γ a b → ECxt Γ b c → ECxt* Γ a c
xs ∷r x = xs ++* (x ∷ [])

data Ehole* {Γ : Cxt} : {a b : Ty} → Tm Γ b → ECxt* Γ a b → Tm Γ a → Set where
  [] : ∀ {a} {t : Tm Γ a} → Ehole* t [] t
  _∷_ : ∀ {a b c t} {E : ECxt Γ b c} {Es : ECxt* Γ a b} {EEst Est}
        → Ehole EEst E Est → Ehole* Est Es t → Ehole* EEst (Es ∷r E) t


-- Inductive definition of strong normalization.


-- Parameterized evaluation contexts

data PCxt {Γ : Cxt} (P : ∀{c} → Tm Γ c → Set) : {a b : Ty} → Tm Γ b → ECxt Γ a b → Tm Γ a → Set where

  appl  : ∀ {a b u}{t : Tm _ (a →̂ b)}
          → (𝒖 : P u)
          → PCxt P (app t u) (appl u) t


-- Parameterized neutral terms.

data PNe {Γ} (P : ∀{c} → Tm Γ c → Set) {b} : Tm Γ b → Set where

  var  : ∀ x                              → PNe P (var x)

  elim : ∀ {a} {t : Tm Γ a} {E Et}
         → (𝒏 : PNe P t) (𝑬𝒕 : PCxt P Et E t) → PNe P Et

-- Parametrized weak head reduction

infix 10 _/_⇒_

data _/_⇒_ {Γ} (P : ∀{c} → Tm Γ c → Set): ∀ {a} → Tm Γ a  → Tm Γ a → Set where

  β     : ∀ {a b}{t : Tm (a ∷ Γ) b}{u}
          → (𝒖 : P u)
          → P / (app (abs t) u) ⇒ subst0 u t

  cong  : ∀ {a b t t' Et Et'}{E : ECxt Γ a b}
          → (𝑬𝒕 : Ehole Et E t)
          → (𝑬𝒕' : Ehole Et' E t')
          → (t⇒ : P / t ⇒ t')
          → P / Et ⇒ Et'

-- Weak head reduction is deterministic.

detP⇒ : ∀ {a Γ} {P : ∀ {c} → Tm Γ c → Set} {t t₁ t₂ : Tm Γ a}
       → (t⇒₁ : P / t ⇒ t₁) (t⇒₂ : P / t ⇒ t₂) → t₁ ≡ t₂
{-
detP⇒ (β 𝒖) (β 𝒖₁) = ≡.refl
detP⇒ (β 𝒖) (cong (appl u) (appl .u) (cong () 𝑬𝒕' d'))
detP⇒ (cong (appl u) (appl .u) (cong () 𝑬𝒕' d)) (β 𝒖)
detP⇒ (cong (appl u) (appl .u) d) (cong (appl .u) (appl .u) d') = ≡.cong (λ t → app t u) (detP⇒ d d')
-}
detP⇒ (β _) (β _)                                              = ≡.refl
detP⇒ (β _) (cong (appl u) (appl .u) (cong () _ _))
detP⇒ (cong (appl u) (appl .u) (cong () _ _)) (β _)
detP⇒ (cong (appl u) (appl .u) x) (cong (appl .u) (appl .u) y) = ≡.cong (λ t → app t u) (detP⇒ x y)


-- Neutrals are closed under application.

pneApp : ∀{Γ a b}{P : ∀{c} → Tm Γ c → Set}{t : Tm Γ (a →̂ b)}{u : Tm Γ a} →
  PNe P t → P u → PNe P (app t u)
pneApp 𝒏 𝒖 = elim 𝒏 (appl 𝒖)


-- Functoriality of the notions wrt. P.

mapPCxt : ∀ {Γ} {P Q : ∀{c} → Tm Γ c → Set} (P⊆Q : ∀ {c}{t : Tm Γ c} → P t → Q t) {a b} {E : ECxt Γ a b}{Et t} → PCxt P Et E t -> PCxt Q Et E t
mapPCxt P⊆Q (appl u∈P) = appl (P⊆Q u∈P)

mapPNe : ∀ {Γ} {P Q : ∀{c} → Tm Γ c → Set} (P⊆Q : ∀ {c}{t : Tm Γ c} → P t → Q t) {a}{t : Tm Γ a} → PNe P t -> PNe Q t
mapPNe P⊆Q (var x) = var x
mapPNe P⊆Q (elim t∈Ne E∈SNh) = elim (mapPNe P⊆Q t∈Ne) (mapPCxt P⊆Q E∈SNh)

mapP⇒ : ∀ {Γ} {P Q : ∀{c} → Tm Γ c → Set} (P⊆Q : ∀ {c}{t : Tm Γ c} → P t → Q t) {a}{t t' : Tm Γ a} → P / t ⇒ t' → Q / t ⇒ t'
mapP⇒ P⊆Q (β t∈P) = β (P⊆Q t∈P)
mapP⇒ P⊆Q (cong Et Et' t→t') = cong Et Et' (mapP⇒ P⊆Q t→t')


_[_]⇒ : ∀ {Γ} {P : ∀{c} → Tm Γ c → Set} {a b} (E : ECxt Γ a b) {t₁ t₂ : Tm Γ a} → P / t₁ ⇒ t₂ → P / E [ t₁ ] ⇒ E [ t₂ ]
E [ t⇒ ]⇒ = cong (proj₂ (mkEHole E)) (proj₂ (mkEHole E)) t⇒

_[_]⇒* : ∀ {Γ} {P : ∀{c} → Tm Γ c → Set} {a b} (E : ECxt* Γ a b) {t₁ t₂ : Tm Γ a} → P / t₁ ⇒ t₂ → P / E [ t₁ ]* ⇒ E [ t₂ ]*
[]       [ t⇒ ]⇒* = t⇒
(E ∷ Es) [ t⇒ ]⇒* = Es [ E [ t⇒ ]⇒ ]⇒*

hole→≡ : ∀ {Γ a b}{Et t}{E : ECxt Γ a b} → (Es : Ehole Et E t) → Et ≡ E [ t ]
hole→≡ (appl u) = ≡.refl

lemma : ∀ {Γ b} {a} {t : Tm Γ a} (Es : ECxt* Γ a b)
         {b₁} {E : ECxt Γ b b₁}
         → E [ Es [ t ]* ] ≡ (Es ++* (E ∷ [])) [ t ]*
lemma [] = ≡.refl
lemma (x ∷ Es) = lemma Es

hole*→≡ : ∀ {Γ a b}{Et t}{E : ECxt* Γ a b} → (Es : Ehole* Et E t) → Et ≡ E [ t ]*
hole*→≡ [] = ≡.refl
hole*→≡ {t = t} (_∷_ {Es = Es} x Es₁) rewrite hole→≡ x | hole*→≡ Es₁ = lemma Es

++*-unit : ∀ {Γ a b} → (xs : ECxt* Γ a b) → xs ++* [] ≡ xs
++*-unit [] = ≡.refl
++*-unit (x ∷ xs) = ≡.cong (_∷_ x) (++*-unit xs)
++*-assoc : ∀ {Γ a b c d} → (xs : ECxt* Γ a b) → {ys : ECxt* Γ b c} → {zs : ECxt* Γ c d} → xs ++* (ys ++* zs) ≡ (xs ++* ys) ++* zs
++*-assoc [] = ≡.refl
++*-assoc (x ∷ xs) = ≡.cong (_∷_ x) (++*-assoc xs)

_++h*_ : ∀ {Γ a b c} {Es1 : ECxt* Γ a b} {Es2 : ECxt* Γ b c} → ∀ {t1 t2 t3} → Ehole* t2 Es1 t3 → Ehole* t1 Es2 t2  → Ehole* t1 (Es1 ++* Es2) t3
_++h*_ {Es1 = Es1} xs [] rewrite ++*-unit Es1      = xs
_++h*_ {Es1 = Es1} xs (_∷_ {E = E} {Es = Es} x ys) rewrite ++*-assoc Es1 {Es} {E ∷ []} = x ∷ (xs ++h* ys)


mkEhole* : ∀ {Γ} {a b} (E : ECxt* Γ a b) {t} → Ehole* (E [ t ]*) E t
mkEhole* [] = []
mkEhole* (E ∷ Es) {t} = (proj₂ (mkEHole E) ∷ []) ++h* mkEhole* Es
