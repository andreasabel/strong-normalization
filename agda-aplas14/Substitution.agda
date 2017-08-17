{-# OPTIONS --copatterns --sized-types #-}

module Substitution where

open import Library
open import Terms

-- VarTm n specifies whether the substitution produces variables or terms.
-- The index is used to impose an order on the constructors
-- and so pass termination checking in lift/subst.

data VarTm : ℕ → Set where
  `Var : VarTm 0
  `Tm  : VarTm 1

max01 : ℕ → ℕ → ℕ
max01 0 m = m
max01 n m = n

_∙VT_ : ∀ {m n} → VarTm m → VarTm n → VarTm (max01 m n)
`Var ∙VT vt = vt
`Tm  ∙VT vt = `Tm

VT : ∀ {m} → VarTm m → Cxt → Ty → Set
VT `Var Γ a = Var Γ a
VT `Tm  Γ a = Tm Γ a

vt2tm : ∀ {Γ a m} vt → VT {m} vt Γ a → Tm Γ a
vt2tm `Var x = var x
vt2tm `Tm  t = t

RenSub : ∀ {m} → VarTm m → Cxt → Cxt → Set
RenSub vt Γ Δ = ∀ {a} → Var Γ a → VT vt Δ a

mutual

  -- Lifiting a substitution

  lifts : ∀ {m vt Γ Δ a} → RenSub {m} vt Γ Δ → RenSub vt (a ∷ Γ) (a ∷ Δ)
  lifts {vt = `Var} σ (zero)    = zero
  lifts {vt = `Var} σ (suc x) = suc (σ x)
  lifts {vt = `Tm}  σ (zero)    = var (zero)
  lifts {vt = `Tm}  σ (suc x) = subst {vt = `Var} suc (σ x)

  -- Performing a substitution

  subst : ∀ {m vt Γ Δ τ} → RenSub {m} vt Γ Δ → Tm Γ τ → Tm Δ τ

  subst σ (abs t)     = abs (subst (lifts σ) t)
  subst σ (app t u)   = app (subst σ t) (subst σ u)
  subst σ (var x)     = vt2tm _ (σ x)

-- Performing substitution, inductive specification

data IndSubst {m vt Γ Δ} (σ : RenSub {m} vt Γ Δ) : ∀ {τ} → Tm Γ τ → Tm Δ τ → Set where

  var  : ∀{a t} (x : Var Γ a)
       → vt2tm _ (σ x) ≡ t
       → IndSubst σ (var x) t

  abs  : ∀{a b} {t : Tm (a ∷ Γ) b} {t'}
       → IndSubst (lifts σ) t t'
       → IndSubst σ (abs t) (abs t')

  app  : ∀{a b} {t : Tm Γ (a →̂ b)} {u t' u'}
       → IndSubst σ t t'
       → IndSubst σ u u'
       → IndSubst σ (app t u) (app t' u')

-- Performing renaming, inductive specification

data IndRen {Γ Δ} (σ : RenSub `Var Γ Δ) : ∀ {τ} → Tm Γ τ → Tm Δ τ → Set where

  var  : ∀{a y} (x : Var Γ a)
       → (σ x) ≡ y
       → IndRen σ (var x) (var y)

  abs  : ∀{a b} {t : Tm (a ∷ Γ) b} {t'}
       → IndRen (lifts σ) t t'
       → IndRen σ (abs t) (abs t')

  app  : ∀{a b} {t : Tm Γ (a →̂ b)} {u t' u'}
       → IndRen σ t t'
       → IndRen σ u u'
       → IndRen σ (app t u) (app t' u')

-- Logical equivalence between inductive and algorithmic substitution

IndS→prop : ∀ {m vt Γ Δ} (σ : RenSub {m} vt Γ Δ) {τ} {t : Tm Γ τ} {t' : Tm Δ τ} → IndSubst σ t t' → subst σ t ≡ t'
IndS→prop σ (var x ≡.refl) = ≡.refl
IndS→prop σ (abs t)     = ≡.cong abs (IndS→prop (lifts σ) t)
IndS→prop σ (app t t₁)  = ≡.cong₂ app (IndS→prop σ t) (IndS→prop σ t₁)

prop→IndS' : ∀ {m vt Γ Δ} (σ : RenSub {m} vt Γ Δ) {τ} (t : Tm Γ τ) → IndSubst σ t (subst σ t)
prop→IndS' σ (var x) = var x ≡.refl
prop→IndS' σ (abs t)     = abs (prop→IndS' (lifts σ) t)
prop→IndS' σ (app t u)   = app (prop→IndS' σ t) (prop→IndS' σ u)

prop→IndS : ∀ {m vt Γ Δ} (σ : RenSub {m} vt Γ Δ) {τ} {t : Tm Γ τ} {t' : Tm Δ τ} → subst σ t ≡ t' → IndSubst σ t t'
prop→IndS _ ≡.refl = prop→IndS' _ _


-- Logical equivalence between inductive and algorithmic renaming

Ind→prop : ∀ {Γ Δ} (σ : RenSub `Var Γ Δ) {τ} {t : Tm Γ τ} {t' : Tm Δ τ} → IndRen σ t t' → subst σ t ≡ t'
Ind→prop σ (var x ≡.refl) = ≡.refl
Ind→prop σ (abs t)     = ≡.cong abs (Ind→prop (lifts σ) t)
Ind→prop σ (app t t₁)  = ≡.cong₂ app (Ind→prop σ t) (Ind→prop σ t₁)

prop→Ind' : ∀ {Γ Δ} (σ : RenSub `Var Γ Δ) {τ} (t : Tm Γ τ) → IndRen σ t (subst σ t)
prop→Ind' σ (var x) = var x ≡.refl
prop→Ind' σ (abs t)     = abs (prop→Ind' (lifts σ) t)
prop→Ind' σ (app t u)   = app (prop→Ind' σ t) (prop→Ind' σ u)

prop→Ind : ∀ {Γ Δ} (σ : RenSub `Var Γ Δ) {τ} {t : Tm Γ τ} {t' : Tm Δ τ} → subst σ t ≡ t' → IndRen σ t t'
prop→Ind _ ≡.refl = prop→Ind' _ _

-- Identity substitution

ids : ∀ {i vt Γ} → RenSub {i} vt Γ Γ
ids {vt = `Var} x = x
ids {vt = `Tm } x = var x

-- substitution composition

_•s_ : ∀ {Γ₀ Γ₁ Γ₂}
         {n}{vt2 : VarTm n}(τ : RenSub vt2 Γ₁ Γ₂)
         {m}{vt1 : VarTm m}(σ : RenSub vt1 Γ₀ Γ₁) → RenSub (vt1 ∙VT vt2) Γ₀ Γ₂
_•s_ τ {vt1 = `Var} σ x = τ (σ x)
_•s_ τ {vt1 = `Tm } σ x = subst τ (σ x)

-- Term substitution

Subst : Cxt → Cxt → Set
Subst Γ Δ = ∀ {a : Ty} → Var Γ a → Tm Δ a


-- Extending a substitution

_∷s_ : ∀ {Γ Δ a} → Tm Γ a → Subst Δ Γ → Subst (a ∷ Δ) Γ
(t ∷s σ) (zero) = t
(t ∷s σ) (suc x) = σ x

-- Substitution for 0th variable

sgs : ∀ {Γ a} → Tm Γ a → Subst (a ∷ Γ) Γ
sgs t = t ∷s ids

-- Substituting for the 0th variable [u/0]t

subst0 : ∀ {Γ a b} → Tm Γ a → Tm (a ∷ Γ) b → Tm Γ b
subst0 u = subst (sgs u)

-- Renamings

Ren : (Γ Δ : Cxt) → Set
Ren = RenSub `Var

_≤_  : (Γ Δ : Cxt) → Set
_≤_ Γ Δ = RenSub `Var Δ Γ

rename : ∀ {Γ Δ : Cxt} {a : Ty} (η : Γ ≤ Δ) (x : Tm Δ a) → Tm Γ a
rename = subst

-- Weakening renaming

weak : ∀{Γ a} → (a ∷ Γ) ≤ Γ
weak = suc

-- Weakening substitution

weaks : ∀{n}{vt : VarTm n}{a Γ Δ} (σ : RenSub vt Γ Δ) → RenSub vt (Γ) (a ∷ Δ)
weaks {vt = `Var} σ x = suc (σ x)
weaks {vt = `Tm} σ x = rename suc (σ x)

-- Properties

_≡s_ : ∀ {Γ Δ} {m n vt1 vt2} → (f : RenSub {m} vt1 Γ Δ)(g : RenSub {n} vt2 Γ Δ) → Set
f ≡s g = (∀ {a} x → vt2tm _ (f {a} x) ≡ vt2tm _ (g x))

mutual
  subst-ext : ∀ {Γ Δ} {m n vt1 vt2} {f : RenSub {m} vt1 Γ Δ}{g : RenSub {n} vt2 Γ Δ} → f ≡s g → ∀ {a} (t : Tm Γ a) → subst f t ≡ subst g t
  subst-ext f≐g (var v) = (f≐g v)
  subst-ext {f = f} {g = g} f≐g (abs t)     = ≡.cong abs (subst-ext (lifts-ext {f = f} {g = g} f≐g) t)
  subst-ext f≐g (app t t₁)  = ≡.cong₂ app (subst-ext f≐g t) (subst-ext f≐g t₁)

  lifts-ext : ∀ {Γ Δ b} {m n vt1 vt2} {f : RenSub {m} vt1 Γ Δ}{g : RenSub {n} vt2 Γ Δ} → f ≡s g → lifts {a = b} f ≡s lifts g
  lifts-ext {vt1 = `Var} {`Var} f≐g (zero) = ≡.refl
  lifts-ext {vt1 = `Var} {`Var} {f} {g} f≐g (suc x) with f x | g x | f≐g x
  lifts-ext {Γ} {Δ} {b} {._} {._} {`Var} {`Var} f≐g (suc x) | z | .z | ≡.refl = ≡.refl
  lifts-ext {vt1 = `Var} {`Tm} f≐g (zero) = ≡.refl
  lifts-ext {vt1 = `Var} {`Tm} f≐g (suc x) rewrite ≡.sym (f≐g x) = ≡.refl
  lifts-ext {vt1 = `Tm} {`Var} f≐g (zero) = ≡.refl
  lifts-ext {vt1 = `Tm} {`Var} f≐g (suc x) rewrite (f≐g x) = ≡.refl
  lifts-ext {vt1 = `Tm} {`Tm} f≐g (zero) = ≡.refl
  lifts-ext {vt1 = `Tm} {`Tm} f≐g (suc x) = ≡.cong (subst suc) (f≐g x)

mutual
  subst-∙ : ∀ {Γ₀ Γ₁ Γ₂}
           {n}{vt2 : VarTm n}(τ : RenSub vt2 Γ₁ Γ₂)
           {m}{vt1 : VarTm m}(σ : RenSub vt1 Γ₀ Γ₁) → ∀ {a} (t : Tm Γ₀ a) → subst (τ •s σ) t ≡ subst τ (subst σ t)
  subst-∙ τ {vt1 = `Var} σ (var x) = ≡.refl
  subst-∙ τ {vt1 = `Tm} σ (var x) = ≡.refl
  subst-∙ τ σ (abs t)     = ≡.cong abs (≡.trans (subst-ext (lifts-∙ τ σ) t) (subst-∙ (lifts τ) (lifts σ) t))
  subst-∙ τ σ (app t t₁)  = ≡.cong₂ app (subst-∙ τ σ t) (subst-∙ τ σ t₁)

  lifts-∙ : ∀ {Γ₀ Γ₁ Γ₂}
         {n}{vt2 : VarTm n}(τ : RenSub vt2 Γ₁ Γ₂)
         {m}{vt1 : VarTm m}(σ : RenSub vt1 Γ₀ Γ₁) → ∀ {a} → lifts {a = a} (τ •s σ) ≡s (lifts τ •s lifts σ)
  lifts-∙ {vt2 = `Var} τ {vt1 = `Var} σ (zero)    = ≡.refl
  lifts-∙ {vt2 = `Tm}  τ {vt1 = `Var} σ (zero)    = ≡.refl
  lifts-∙ {vt2 = `Var} τ {vt1 = `Var} σ (suc x) = ≡.refl
  lifts-∙ {vt2 = `Tm}  τ {vt1 = `Var} σ (suc x) = ≡.refl
  lifts-∙ {vt2 = `Var} τ {vt1 = `Tm}  σ (zero)    = ≡.refl
  lifts-∙ {vt2 = `Tm}  τ {vt1 = `Tm}  σ (zero)    = ≡.refl
  lifts-∙ {vt2 = `Var} τ {vt1 = `Tm}  σ (suc x) = ≡.trans (≡.sym (subst-∙ suc τ (σ x))) (subst-∙ (lifts τ) suc (σ x))
  lifts-∙ {vt2 = `Tm}  τ {vt1 = `Tm}  σ (suc x) = ≡.trans (≡.sym (subst-∙ suc τ (σ x))) (subst-∙ (lifts τ) suc (σ x))

mutual
  subst-id : ∀ {m vt Γ a} → (t : Tm Γ a) → subst (ids {m} {vt}) t ≡ t
  subst-id {vt = `Var} (var v) = ≡.refl
  subst-id {vt = `Tm}  (var v) = ≡.refl
  subst-id {m} {vt} {Γ} (abs t)     = ≡.cong abs (≡.trans (subst-ext {n = m} {vt2 = vt} (lifts-id {m} {vt}) t) (subst-id t))
  subst-id (app t t₁)  = ≡.cong₂ app (subst-id t) (subst-id t₁)

  lifts-id : ∀ {m vt Γ b} → lifts {a = b} (ids {m} {vt} {Γ = Γ}) ≡s ids {m} {vt} {Γ = b ∷ Γ}
  lifts-id {vt = `Var} (zero)    = ≡.refl
  lifts-id {vt = `Var} (suc x) = ≡.refl
  lifts-id {vt = `Tm}  (zero)    = ≡.refl
  lifts-id {vt = `Tm}  (suc x) = ≡.refl

sgs-lifts : ∀ {m vt Γ Δ a} {σ : RenSub {m} vt Γ Δ} {u : Tm Γ a} → (sgs (subst σ u) •s lifts σ) ≡s (σ •s sgs u)
sgs-lifts {vt = `Var} = (λ { (zero) → ≡.refl ; (suc x) → ≡.refl })
sgs-lifts {vt = `Tm} {σ = σ} {u} = (λ { (zero) → ≡.refl ; (suc x) → ≡.sym (≡.trans (≡.sym (subst-id (σ x)))
                                                                               (subst-∙ (sgs (subst σ u)) {vt1 = `Var} suc (σ x))) })
sgs-lifts-term : ∀ {m vt Γ Δ a b} {σ : RenSub {m} vt Γ Δ} {u : Tm Γ a}{t : Tm (a ∷ Γ) b}
                 → subst (sgs (subst σ u)) (subst (lifts σ) t) ≡ subst σ (subst (sgs u) t)
sgs-lifts-term {σ = σ} {u} {t} = (≡.trans (≡.sym (subst-∙ (sgs (subst σ u)) (lifts σ) t))
                                 (≡.trans (subst-ext sgs-lifts t)
                                          (subst-∙ σ (sgs u) t)))

renId : ∀ {Γ a}{t : Tm Γ a} → rename id t ≡ t
renId = subst-id _

contract : ∀ {a Γ} → RenSub `Var (a ∷ a ∷ Γ) (a ∷ Γ)
contract (zero)    = zero
contract (suc x) = x


contract-sgs : ∀ {a Γ} → contract {a} {Γ} ≡s sgs (var zero)
contract-sgs (zero)  = ≡.refl
contract-sgs (suc x) = ≡.refl

sgs-weak₀ : ∀ {Γ a} {u : Tm Γ a} {b} (x : Var Γ b) → sgs u (suc x) ≡ var x
sgs-weak₀ x = ≡.refl

sgs-weak₁ : ∀ {Γ a} {u : Tm Γ a} → (sgs u ∘ suc) ≡s (ids {vt = `Tm})
sgs-weak₁ x = ≡.refl

sgs-weak : ∀ {Γ a} {u : Tm Γ a} → (sgs u •s weak) ≡s (ids {vt = `Tm})
sgs-weak x = ≡.refl

cons-to-sgs :  ∀ {Γ Δ a} (u : Tm Δ a) (σ : Subst Γ Δ)
               → (u ∷s σ) ≡s (sgs u •s lifts σ)
cons-to-sgs u σ (zero) = ≡.refl
cons-to-sgs u σ (suc x) = begin
    σ x                               ≡⟨ ≡.sym (subst-id (σ x)) ⟩
    subst (ids {vt = `Tm}) (σ x)      ≡⟨ subst-ext (λ _ → ≡.refl) (σ x) ⟩
    subst (sgs u •s weak) (σ x)       ≡⟨ subst-∙ (sgs u) weak (σ x) ⟩
    subst (sgs u) (subst suc (σ x))
  ∎
  where open ≡-Reasoning
-- -}
