module SN where

open import Library
open import Syntax
open import RenamingAndSubstitution

-- Reduction

data _↦_ {Γ} : ∀{a} (t t' : Tm Γ a) → Set where
  β    : ∀{a b} {t : Tm (Γ , a) b} {u} → app (abs t) u ↦ sub0 t u
  abs  : ∀{a b} {t t' : Tm (Γ , a) b} (r : t ↦ t') → abs t ↦ abs t'
  appl : ∀{a b} {t t' : Tm Γ (a ⇒ b)} {u} (r : t ↦ t') → app t u ↦ app t' u
  appr : ∀{a b} {t : Tm Γ (a ⇒ b)} {u u'} (r : u ↦ u') → app t u ↦ app t u'

ren↦ : ∀{Γ Δ a} (ρ : Ren Γ Δ) {t t' : Tm Δ a} (r : t ↦ t') → ren ρ t ↦ ren ρ t'
-- ren↦ {Γ} {Δ} {a} ρ {t} {t'} r = {!r!}
ren↦ {Γ} {Δ} ρ β = {!!}
ren↦ {Γ} {Δ} ρ (abs r) = abs (ren↦ (liftr ρ) r)
ren↦ {Γ} {Δ} ρ (appl r) = {!!}
ren↦ {Γ} {Δ} ρ (appr r) = {!!}

ren↦inv : ∀{Γ Δ a} (ρ : Ren Γ Δ) (t : Tm Δ a) {t' : Tm Γ a} (r : ren ρ t ↦ t') →
  ∃ λ (u : Tm Δ a) → (t ↦ u) × (t' ≡ ren ρ u)
ren↦inv ρ (var x) ()
ren↦inv ρ (app (abs t) t₁) β = sub0 t t₁ , β , {!refl!}
ren↦inv ρ (abs t) (abs r) with ren↦inv (liftr ρ) t r
ren↦inv ρ (abs t) (abs r) | u , r' , e = abs u , abs r' , cong abs e
ren↦inv ρ (app t t₁) (appl r) with ren↦inv ρ t r
ren↦inv ρ (app t t₁) (appl r) | u , r' , refl = app u t₁ , appl r' , refl
ren↦inv ρ (app t t₁) (appr r) with ren↦inv ρ t₁ r
... | u , r' , refl = app t u , appr r' , refl

-- Strongly normalizing terms

data SN {Γ : Cxt} {a : Ty} (t : Tm Γ a) : Set where
  sn : (∀ t' (r : t ↦ t') → SN t') → SN t

-- SN is closed under renaming

renSN : ∀{Γ Δ a} (ρ : Ren Γ Δ) {t : Tm Δ a} (s : SN t) → SN (ren ρ t)
renSN ρ (sn f) = sn λ _ r → case ren↦inv ρ _ r of
  λ{ (t'' , r' , refl) → renSN ρ (f t'' r') }

-- Strong head reduction (weak head reduction that preserves SN under expansion)

data _s↦_ {Γ} : ∀{a} (t t' : Tm Γ a) → Set where
  β    : ∀{a b} {t : Tm (Γ , a) b} {u} (s : SN u) → app (abs t) u s↦ sub0 t u
  appl : ∀{a b} {t t' : Tm Γ (a ⇒ b)} {u} (r : t s↦ t') → app t u s↦ app t' u

-- Strong head reduction is closed under renaming

rens↦ : ∀{Γ Δ a} (ρ : Ren Γ Δ) {t t' : Tm Δ a} (r : t s↦ t') → ren ρ t s↦ ren ρ t'
rens↦ ρ (β s) = {!β!}
  -- Need lemma:
  --   app (abs (ren (liftr ρ) .t)) (ren ρ .u) s↦
  --     ren ρ (sub (subId , .u) .t)rens↦ ρ (appl r) = appl (rens↦ ρ r)

-- SN is closed under strong head expansion

s↦SN : ∀{Γ a}{t t' : Tm Γ a} (r : t s↦ t') (s : SN t') → SN t
-- s↦SN r s = sn λ t' → λ{ β → {!!} ; (abs r') → {!!} ; (appl r') → {!!} ; (appr r') → {!!}}
s↦SN (β s')   s = sn (λ t' → λ{ β → s ; (appl (abs r)) → {!!} ; (appr r) → {!!}})
s↦SN (appl r) s = {!!}

-- Reducibility: Kripke logical predicate

Red : (a : Ty) {Γ : Cxt} (t : Tm Γ a) → Set
Red ★       {Γ} t = SN t
Red (a ⇒ b) {Γ} t = ∀{Γ'}(ρ : Ren Γ' Γ) u (s : Red a u) → Red b (app (ren ρ t) u)

-- Reducibility is closed under renaming

renRed : ∀{Γ Δ a} (ρ : Ren Γ Δ) {t : Tm Δ a} (p : Red a t) → Red a (ren ρ t)
renRed {Γ} {Δ} {★}     ρ {t} p = renSN ρ p
renRed {Γ} {Δ} {a ⇒ b} ρ {t} p = λ ρ₁ u s →
  subst (λ z → Red b (app z u)) (rencomp ρ₁ ρ t)
    (p (renComp ρ₁ ρ) u s)

-- Reducibility is closed under strong head expansion

expRed : ∀{Γ a} {t t' : Tm Γ a} (r : t s↦ t') (p : Red a t') → Red a t
expRed {Γ} {★}     {t} {t'} r p       = s↦SN r p
expRed {Γ} {a ⇒ b} {t} {t'} r p ρ u s = expRed (appl {!!}) (p ρ u s)
