{-# OPTIONS --allow-unsolved-metas #-}

-- Type interpretation and soundness of typing.

module Soundness where

open import Library
open import Terms
open import Substitution
open import SN
open import SN.AntiRename
open import SAT3

-- Type interpretation

infix 3 ⟦_⟧_

⟦_⟧≤ : (a : Ty) {n : ℕ} → SAT≤ a n

⟦_⟧_ : (a : Ty) (n : ℕ) → SAT a n
⟦ base  ⟧ n  = {!!}
⟦ a →̂ b ⟧ n  = ⟦ a ⟧≤ {n} ⟦→⟧ ⟦ b ⟧≤ {n}

⟦_⟧≤′ : (a : Ty) {n : ℕ} → ∀ {m} → m ≤′ n → SAT a m

⟦ a ⟧≤ m≤n = ⟦ a ⟧≤′ (≤⇒≤′ m≤n)

⟦_⟧≤′ a .{m}     {m} ≤′-refl = ⟦ a ⟧ m
⟦_⟧≤′ a .{suc n} {m} (≤′-step {n} m≤n) = ⟦ a ⟧≤′ m≤n

in≤′ : (a : Ty) {n : ℕ} → ∀ {m} → (m≤n : m ≤′ n) → SAT.satSet (⟦ a ⟧ m) ⊆ SAT.satSet (⟦ a ⟧≤′ m≤n)
in≤′ a ≤′-refl       𝑡 = 𝑡
in≤′ a (≤′-step m≤n) 𝑡 = in≤′ a m≤n 𝑡

out≤′ : (a : Ty) {n : ℕ} → ∀ {m} → (m≤n : m ≤′ n) → SAT.satSet (⟦ a ⟧≤′ m≤n) ⊆ SAT.satSet (⟦ a ⟧ m)
out≤′ a ≤′-refl 𝑡 = 𝑡
out≤′ a (≤′-step m≤n) 𝑡 = out≤′ a m≤n 𝑡

coerce≤ : (a : Ty) {n n' : ℕ} → ∀ {m} → (m≤n : m ≤ℕ n) (m≤n' : m ≤ℕ n') → SAT.satSet (⟦ a ⟧≤′ (≤⇒≤′ m≤n)) ⊆ SAT.satSet (⟦ a ⟧≤′ (≤⇒≤′ m≤n'))
coerce≤ a ≤1 ≤2 𝑡 = in≤′ a (≤⇒≤′ ≤2) (out≤′ a (≤⇒≤′ ≤1) 𝑡)

map⟦_⟧ : ∀ (a : Ty) → ∀ {m n} → m ≤ℕ n → ∀ {Γ} {t : Tm Γ a} → SAT.satSet (⟦ a ⟧ n) t
                                           → SAT.satSet (⟦ a ⟧ m) t
map⟦_⟧ base m≤n t = {!!}
map⟦_⟧ (a →̂ b) m≤n 𝑡          = λ l l≤m ρ 𝑢 → let l≤n = ≤ℕ.trans l≤m m≤n in
                                  coerce≤ b l≤n l≤m (𝑡 l l≤n ρ (coerce≤ a l≤m l≤n 𝑢))

map⟦_⟧∈ : ∀ (a : Ty) → ∀ {m n} → (m ≤ℕ n) → ∀ {Γ} {t : Tm Γ a} → t ∈ (⟦ a ⟧ n)
                                            → t ∈ (⟦ a ⟧ m)
map⟦_⟧∈ a m≤n (↿ 𝑡) = ↿ (map⟦ a ⟧ m≤n 𝑡)

-- Context interpretation (semantic substitutions)

⟦_⟧C : ∀ Γ {n} → ∀ {Δ} (σ : Subst Γ Δ) → Set
⟦ Γ ⟧C {n} σ = ∀ {a} (x : Var Γ a) → σ x ∈ (⟦ a ⟧ n)

Ext : ∀ {a n Δ Γ} {t : Tm Δ a} → (𝒕 : t ∈ (⟦ a ⟧ n)) →
      ∀ {σ : Subst Γ Δ} (θ : ⟦ Γ ⟧C σ) → ⟦ a ∷ Γ ⟧C (t ∷s σ)
Ext {a} 𝒕 θ (zero)  = 𝒕
Ext {a} 𝒕 θ (suc x) = θ x

Rename : ∀ {n Δ Δ'} → (ρ : Ren Δ Δ') →
         ∀ {Γ}{σ : Subst Γ Δ} (θ : ⟦ Γ ⟧C {n} σ) →
         ⟦ Γ ⟧C (ρ •s σ)
Rename ρ θ {a} x = ↿ SAT.satRename (⟦ a ⟧ _) ρ (⇃ θ x)

Map : ∀ {m n} → (m≤n : m ≤ℕ n) →
      ∀ {Γ Δ} {σ : Subst Γ Δ} (θ : ⟦ Γ ⟧C σ) → ⟦ Γ ⟧C σ
Map m≤n θ {a} x = map⟦ a ⟧∈ m≤n (θ x)



sound : ∀ {n a Γ} (t : Tm Γ a) {Δ} {σ : Subst Γ Δ} → (θ : ⟦ Γ ⟧C {n} σ) → subst σ t ∈ (⟦ a ⟧ n)
sound (var x) θ = θ x
sound (abs t) {σ = σ} θ = ⟦abs⟧ {𝓐 = ⟦ _ ⟧≤} {𝓑 = ⟦ _ ⟧≤} (λ l≤m ρ {u} 𝑢 →
  let open ≡-Reasoning
      eq : subst (u ∷s (ρ •s σ)) t ≡ subst0 u (subst (lifts ρ) (subst (lifts σ) t))
      eq = begin

             subst (u ∷s (ρ •s σ)) t

           ≡⟨ subst-ext (cons-to-sgs u _) t ⟩

              subst (sgs u •s lifts (ρ •s σ)) t

           ≡⟨ subst-∙ _ _ t ⟩

             subst0 u (subst (lifts (ρ •s σ)) t)

           ≡⟨ ≡.cong (subst0 u) (subst-ext (lifts-∙ ρ σ) t) ⟩

             subst0 u (subst (lifts ρ •s lifts σ) t)

           ≡⟨ ≡.cong (subst0 u) (subst-∙ (lifts ρ) (lifts σ) t) ⟩

             subst0 u (subst (lifts ρ) (subst (lifts σ) t))
           ∎
  in (≡.subst (λ tu → tu ∈⟨ l≤m ⟩ (⟦ _ ⟧≤)) eq (↿ in≤′ _ (≤⇒≤′ l≤m) (⇃ sound t (Ext (↿ out≤′ _ (≤⇒≤′ l≤m) (⇃ 𝑢)) ((Rename ρ (Map l≤m θ))))))))

sound {n} (app {a} {b} t u) θ = ↿ out≤′ b (≤⇒≤′ ≤ℕ.refl)
       (⇃ ⟦app⟧ {n} {𝓐 = ⟦ _ ⟧≤} {𝓑 = ⟦ _ ⟧≤} ≤ℕ.refl (sound t θ) (↿ in≤′ a (≤⇒≤′ ≤ℕ.refl) (⇃ sound u θ)))
