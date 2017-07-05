{-# OPTIONS --allow-unsolved-metas #-}

module NReduction where

open import Data.Sum
open import Library
open import Terms
open import TermShape
open import Substitution
open import SN

data NβECxt (Γ : Cxt) : (Δ : Cxt) (a b : Ty) → (n n' : ℕ) → Set where
  appl  : ∀ {n a b} (u : Tm Γ a)                        → NβECxt Γ Γ (a →̂ b) b n n
  appr  : ∀ {n a b} (t : Tm Γ (a →̂  b))                 → NβECxt Γ Γ a b n n
  abs   : ∀ {n a b}                                     → NβECxt Γ (a ∷ Γ) b (a →̂  b) n n

data NβEhole {n : ℕ} {Γ : Cxt} : {n' : ℕ} → {Δ : Cxt} {b a : Ty} → Tm Γ b → NβECxt Γ Δ a b n n' → Tm Δ a → Set where
  appl  : ∀ {a b}{t : Tm Γ (a →̂ b)} (u : Tm Γ a)                          → NβEhole (app t u) (appl u) t
  appr  : ∀ {a b u} (t : Tm Γ (a →̂  b))                   → NβEhole (app t u) (appr t) u
  abs   : ∀ {a b} {t : Tm (a ∷ Γ) b}                      → NβEhole (abs t) abs t


mkHole : ∀ {n n' Γ Δ} {a b} (E : NβECxt Γ Δ a b n n') {t} → Σ _ \ E[t] → NβEhole E[t] E t
mkHole (appl u)  = _ , appl u
mkHole (appr t)  = _ , appr t
mkHole abs       = _ , abs

infix 7 _⟨_⟩⇒β_

data _⟨_⟩⇒β_ {Γ} : ∀ {a} → Tm Γ a → ℕ → Tm Γ a → Set where

  β     : ∀ {n a b}{t : Tm (a ∷ Γ) b}{u}
          → (app (abs t) u) ⟨ n ⟩⇒β subst0 u t

  cong  : ∀ {n n' Δ a b t t' Et Et'}{E : NβECxt Γ Δ a b n n'}
          → (𝑬𝒕 : NβEhole Et E t)
          → (𝑬𝒕' : NβEhole Et' E t')
          → (t⇒β : t ⟨ n ⟩⇒β t')
          → Et ⟨ n' ⟩⇒β Et'


subst⇒β : ∀ {n m vt a Γ} {t t' : Tm Γ a} {Δ}
           (σ : RenSub {m} vt Γ Δ) → t ⟨ n ⟩⇒β t' → subst σ t ⟨ n ⟩⇒β subst σ t'
subst⇒β {n} σ (β {t = t} {u = u})            = ≡.subst (λ t' → app (abs (subst (lifts σ) t)) (subst σ u) ⟨ n ⟩⇒β t')
                                                   (sgs-lifts-term {σ = σ} {u} {t})
                                           β
subst⇒β σ (cong (appl u) (appl .u) t⇒)   = cong (appl _) (appl _) (subst⇒β σ t⇒)
subst⇒β σ (cong (appr t₁) (appr .t₁) t⇒) = cong (appr _) (appr _) (subst⇒β σ t⇒)
subst⇒β σ (cong abs abs t⇒)              = cong abs abs (subst⇒β (lifts σ) t⇒)

data _⟨_⟩⇒β*_ {Γ} {a} : Tm Γ a → ℕ → Tm Γ a → Set where
  []  : ∀ {n t} → t ⟨ n ⟩⇒β* t
  _∷_ : ∀ {n ti tm to} → ti ⟨ n ⟩⇒β tm → tm ⟨ n ⟩⇒β* to → ti ⟨ n ⟩⇒β* to

_++β_ : ∀ {n} {Γ} {a} {t₀ t₁ t₂ : Tm Γ a} → t₀ ⟨ n ⟩⇒β* t₁ → t₁ ⟨ n ⟩⇒β* t₂ → t₀ ⟨ n ⟩⇒β* t₂
[] ++β ys = ys
(x ∷ xs) ++β ys = x ∷ (xs ++β ys)

cong* : ∀ {n n' a Γ Δ} {b} {t tβ* : Tm Γ a} {E : NβECxt Δ Γ a b n n'}{E[t] E[tβ*]} → NβEhole E[t] E t → NβEhole E[tβ*] E tβ* → t ⟨ n ⟩⇒β* tβ* → E[t] ⟨ n' ⟩⇒β* E[tβ*]
cong* (appl u)   (appl .u)   []       = []
cong* (appr t₁)  (appr .t₁)  []       = []
cong* abs        abs         []       = []
cong* E1         E2          (x ∷ t⇒) = cong E1 (proj₂ ((mkHole _))) x ∷ cong* (proj₂ ((mkHole _))) E2 t⇒


subst⇒β*₀ : ∀ {n m vt a Γ} {t t' : Tm Γ a} {Δ} (σ : RenSub {m} vt Γ Δ) → t ⟨ n ⟩⇒β* t' → subst σ t ⟨ n ⟩⇒β* subst σ t'
subst⇒β*₀ σ [] = []
subst⇒β*₀ σ (x ∷ xs) = (subst⇒β σ x) ∷ (subst⇒β*₀ σ xs)

open import Reduction

nβ⇒β : ∀ {n a Γ} {t t' : Tm Γ a} → t ⟨ n ⟩⇒β t' → t ⇒β t'
nβ⇒β β = β
nβ⇒β (cong E1 E2 t⇒) = cong (help E1) (help E2) (nβ⇒β t⇒)
 where
    help' : ∀ {n a Γ} {n₁ Δ a₁}
           (E : NβECxt Γ Δ a₁ a n₁ n) → βECxt Γ Δ a₁ a
    help' (appl u) = appl u
    help' (appr t) = appr t
    help' abs = abs

    help : ∀ {n a Γ} {t : Tm Γ a} {n₁ Δ a₁} {t₁ : Tm Δ a₁}
           {E : NβECxt Γ Δ a₁ a n₁ n}
           (E1 : NβEhole t E t₁) →
           βEhole t (help' E) t₁
    help (appl u) = appl u
    help (appr t) = appr t
    help abs = abs


nβ*⇒β* : ∀ {n a Γ} {t t' : Tm Γ a} → t ⟨ n ⟩⇒β* t' → t ⇒β* t'
nβ*⇒β* [] = []
nβ*⇒β* (x ∷ xs) = nβ⇒β x ∷ nβ*⇒β* xs

mapNβSNe : ∀ {i n m a Γ} {t t' : Tm Γ a} → t ⟨ m ⟩⇒β t' → SNe {i} n t → SNe {i} n t'
mapNβSNe t⇒ 𝒕 = mapβSNe (nβ⇒β t⇒) 𝒕

mapNβSN : ∀ {i n m a Γ} {t t' : Tm Γ a} → t ⟨ m ⟩⇒β t' → SN {i} n t → SN {i} n t'
mapNβSN t⇒ 𝒕 = mapβSN (nβ⇒β t⇒) 𝒕

_[_]⇒β : ∀ {Γ} {n} {a b} (E : ECxt Γ a b) {t₁ t₂ : Tm Γ a} →  t₁ ⟨ n ⟩⇒β t₂ → E [ t₁ ] ⟨ n ⟩⇒β E [ t₂ ]
appl u [ t⇒ ]⇒β = cong (appl u) (appl u) t⇒

_[_]⇒β* : ∀ {Γ} {n} {a b} (E : ECxt* Γ a b) {t₁ t₂ : Tm Γ a} → t₁ ⟨ n ⟩⇒β t₂ → E [ t₁ ]* ⟨ n ⟩⇒β E [ t₂ ]*
[]       [ t⇒ ]⇒β* = t⇒
(E ∷ Es) [ t⇒ ]⇒β* = Es [ E [ t⇒ ]⇒β ]⇒β*

data SnocView {Γ} {a} {t : Tm Γ a} : ∀ {b} (Es : ECxt* Γ a b) → Set where
  [] : SnocView []
  cons : ∀ {b c d} {El : ECxt Γ a c} (Er : ECxt Γ d b) {Ers : ECxt* Γ _ _} {Els : ECxt* Γ _ _}
         → (El ∷ Els) [ t ]* ≡ Er [ Ers [ t ]* ] → SnocView {b = b} (El ∷ Els)

snocView : ∀ {Γ} {a b} (E : ECxt* Γ a b) (t : Tm Γ a) → SnocView {t = t} E
snocView [] t = []
snocView (E ∷ Es) t with snocView Es (E [ t ])
snocView (E ∷ .[]) t | []                                 = cons E  {Ers = []}      ≡.refl
snocView (E ∷ ._) t  | cons Er {Ers = Ers} {Els = Els} eq = cons Er {Ers = E ∷ Ers} eq



data _Redex {Γ} : ∀ {a} → Tm Γ a → Set where

  β     : ∀ {a b}{t : Tm (a ∷ Γ) b}{u}
          → (app (abs t) u) Redex

mutual
  EC→NβEC : ∀ {Γ} {n a b} (E : ECxt Γ a b) → NβECxt Γ Γ a b n n
  EC→NβEC (appl u) = appl u

  mkHole2 : ∀ {Γ} {n a b} (E : ECxt Γ a b) {t : Tm Γ a} → NβEhole (E [ t ]) (EC→NβEC {n = n} E) t
  mkHole2 (appl u) = appl u

mkHole3 : ∀ {Γ} {n a b c} (E : ECxt Γ a b) {Es : ECxt* Γ _ _} {t : Tm Γ c} → NβEhole ((Es ∷r E) [ t ]*) (EC→NβEC {n = n} E) (Es [ t ]*)
mkHole3 E {Es} {t} rewrite ≡.sym (lemma {t = t} Es {E = E}) = mkHole2 E {Es [ t ]*}

≡subst⇒β : ∀ {n a Γ} {t t1 t' t'1 : Tm Γ a} → t ≡ t1 → t' ≡ t'1 → t ⟨ n ⟩⇒β t' → t1 ⟨ n ⟩⇒β t'1
≡subst⇒β ≡.refl ≡.refl x = x

split : ∀ {Γ} {n} {a b} (E : ECxt* Γ a b) {t₁ : Tm Γ a}{t₂ Et₁ : Tm Γ b} →
         Ehole* Et₁ E t₁ → t₁ Redex →
         Et₁ ⟨ n ⟩⇒β t₂ → (Σ _ \ t₃ → Ehole* t₂ E t₃ × t₁ ⟨ n ⟩⇒β t₃)
         ⊎ (Σ _ \ E₁ → Ehole* t₂ E₁ t₁ × (∀ t → E [ t ]* ⟨ n ⟩⇒β E₁ [ t ]*))
split ._ [] r t⇒ = inj₁ (_ , [] , t⇒)
split .(appl u ∷ []) (appl u ∷ []) () β
split ._ (appl u ∷ (() ∷ eq)) r β
split ._ (appl u ∷ eq) r (cong (appl .u) (appl .u) t⇒) with split _ eq r t⇒
split ._ (appl u ∷ eq) r (cong (appl .u) (appl .u) t⇒) | inj₁ (x , eq0 , t⇒') = inj₁ (_ , ((appl u) ∷ eq0) , t⇒')
split ._ (_∷_ {Es = Es} (appl u) eq) r (cong (appl .u) (appl .u) t⇒) | inj₂ (Es' , eq0 , f) = inj₂ (_ , ((appl u ∷ eq0) ,
                                                        (λ t → cong (mkHole3 (appl u) {Es}) (mkHole3 (appl u) {Es'}) (f t))))
split ._ (_∷_ {Es = Es} (appl t) eq) r (cong (appr Est) (appr .Est) t⇒) = inj₂ (_ , ((appl _ ∷ eq) ,
      ( (λ t₁ → ≡subst⇒β (lemma Es) (lemma Es) {! _⟨_⟩⇒β_.cong (appr (Es [ t₁ ]*)) (appr (Es [ t₁ ]*)) t⇒ !}) ) ))

cong*2 : ∀ {Γ n a b t t'}(E : ECxt* Γ a b)
          → (t⇒ : t ⟨ n ⟩⇒β t')
          → E [ t ]* ⟨ n ⟩⇒β E [ t' ]*
cong*2 E t⇒ = E [ t⇒ ]⇒β*
