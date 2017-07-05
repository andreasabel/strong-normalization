-- Imports from the standard library

module Library where

-- open import Level using () renaming (suc to lsuc) public

open import Data.Fin using (Fin; zero; suc) public
open import Data.List using (List; []; _∷_; map) public
open import Data.Nat
  using    (ℕ; zero; suc; z≤n; s≤s; pred; _≤′_; ≤′-refl; ≤′-step )
  renaming (_≤_ to _≤ℕ_;  _⊔_ to max)
  public
open import Data.Nat.Properties
  using (_+-mono_; ≤⇒≤′)
  renaming (≤-decTotalOrder to decTotalOrderℕ)
  public
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂) renaming (map to map×) public

open import Function using (id; _∘_) public

open import Induction.WellFounded using (Acc; acc) public

open import Relation.Binary using (module DecTotalOrder)
open import Relation.Binary.List.Pointwise as ListEq using ([]; _∷_) renaming (Rel to ≅L) hiding (module Rel) public
module ≅L = ListEq
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; module ≡-Reasoning) public
module ≡ = PropEq
open import Size public

module DecTotalOrderℕ = DecTotalOrder decTotalOrderℕ
module ≤ℕ = DecTotalOrderℕ

caseMax : ∀{m n} (P : ℕ → Set)
          → (pn : (m≤n : m ≤ℕ n) → P n)
          → (pm : (n≤m : n ≤ℕ m) → P m)
          → P (max m n)
caseMax {zero } {n    } P pn pm = pn z≤n
caseMax {suc m} {zero } P pn pm = pm z≤n
caseMax {suc m} {suc n} P pn pm = caseMax (P ∘ suc) (pn ∘ s≤s) (pm ∘ s≤s)

n≤sn : ∀{n} → n ≤ℕ suc n
n≤sn = (z≤n {1}) +-mono DecTotalOrderℕ.refl

pred≤ℕ : ∀{n m} → suc n ≤ℕ suc m → n ≤ℕ m
pred≤ℕ (s≤s p) = p


record ⊤ {a} : Set a where

-- TODOs

postulate
  TODO : ∀ {a}{A : Set a} → A

-- -}
