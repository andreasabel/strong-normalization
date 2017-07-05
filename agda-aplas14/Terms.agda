module Terms where

open import Library

-- * Variables
------------------------------------------------------------------------

data Ty : Set where
  base : Ty
  _→̂_ : (a b : Ty) → Ty

-- Typing contexts.

Cxt = List Ty

-- Variables.

data Var : (Γ : Cxt) (a : Ty) → Set where
  zero : ∀{Γ a}                 → Var (a ∷ Γ) a
  suc  : ∀{Γ a b} (x : Var Γ a) → Var (b ∷ Γ) a

-- De Bruijn index 0.

v₀ : ∀ {a Γ} → Var (a ∷ Γ) a
v₀ = zero

-- * Terms
------------------------------------------------------------------------

-- Well-typed terms.

data Tm (Γ : Cxt) : (a : Ty) → Set where
  var  : ∀{a}          (x : Var Γ a)                   → Tm Γ a
  abs  : ∀{a b}        (t : Tm (a ∷ Γ) b)              → Tm Γ (a →̂ b)
  app  : ∀{a b}        (t : Tm Γ (a →̂ b)) (u : Tm Γ a) → Tm Γ b
