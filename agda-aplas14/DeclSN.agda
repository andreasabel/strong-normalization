{-# OPTIONS --copatterns --sized-types #-}

module DeclSN where

open import Data.Sum
open import Library
open import Terms
open import Substitution
open import TermShape
open import SN
open import NReduction
open import Reduction

-- SN as accessibility

data sn {Γ} (n : ℕ) {a} (t : Tm Γ a) : Set where
  acc : (∀ {t'} → t ⟨ n ⟩⇒β t' → sn n t') → sn n t

sn⇒β :  ∀ {Γ} {n : ℕ} {a} {t t' : Tm Γ a} → sn n t → t ⟨ n ⟩⇒β t' → sn n t'
sn⇒β (acc h) r = h r

varsn : ∀ {Γ} {n : ℕ} {a} (x : Var Γ a) → sn n (var x)
varsn x = acc λ { (cong () _ _) }

abssn : ∀ {Γ} {n : ℕ} {a b} {t : Tm (a ∷ Γ) b} → sn n t → sn n (abs t)
abssn (acc f) = acc (λ { {._} (cong abs abs x)  → abssn (f x) })

subsn : ∀ {Γ Δ} {n n' : ℕ} {a b} {f : Tm Γ a -> Tm Δ b} →
        (g : ∀ {t t' : Tm Γ a} → t ⟨ n ⟩⇒β t' → f t ⟨ n' ⟩⇒β f t') →
        ∀ {t} → sn n' (f t) → sn n t
subsn g (acc ft) = acc (\ t⇒ -> subsn g (ft (g t⇒)))

-- Goal here: prove that sne is closed under application.


appsn : ∀{n Γ a b}{t : Tm Γ (a →̂ b)}{u : Tm Γ a} → sn n t → sn n u → SNe n t →
                 ∀ {t' : Tm Γ b} → app t u ⟨ n ⟩⇒β t' → sn n t'
appsn t       u       (elim 𝒏 ()) β
appsn (acc t) 𝒖       𝒏           (cong (appl u) (appl .u) t⇒) = acc (appsn (t t⇒) 𝒖      (mapNβSNe t⇒ 𝒏))
appsn 𝒕       (acc u) 𝒏           (cong (appr t) (appr .t) t⇒) = acc (appsn 𝒕      (u t⇒) 𝒏)

elimsn : ∀ {n Γ a b}{E : ECxt Γ a b}{t : Tm Γ a}{Et : Tm Γ b} → sn n t → PCxt (sn n) Et E t → SNe n t →
         ∀ {Et' : Tm Γ b} → Et ⟨ n ⟩⇒β Et' → sn n Et'
elimsn 𝒕 (appl 𝒖) 𝒏           t⇒                    = appsn 𝒕 𝒖 𝒏 t⇒




substβsn : ∀ {i m vt a Γ n} {Δ} {σ ρ : RenSub {m} vt Γ Δ} → (∀ {b} (x : Var Γ b) → vt2tm _ (σ x) ⟨ n ⟩⇒β* vt2tm _ (ρ x))
             → (t : Tm Γ a) → SN {i} n (subst σ t) → SN {i} n (subst ρ t)
substβsn f t x₁ = mapβ*SN (subst⇒β* (λ x → nβ*⇒β* (f x)) t) x₁


antiSubst : ∀ {n Γ a b} {t : Tm (a ∷ Γ) b}{u : Tm Γ a} → sn n (subst (sgs u) t) → sn n t
antiSubst {t = t} = subsn (λ x → NReduction.subst⇒β (sgs _) x)

subexpsn : ∀ {n Γ a b} (E : ECxt* Γ a b) {t : Tm Γ a} → sn n (E [ t ]*) -> sn n t
subexpsn E = subsn \ x -> cong*2 E x

mutual

  appsn₃ : ∀ {i n a b c Γ} {u : Tm Γ a} {t : Tm (a ∷ Γ) b}{Es : ECxt* Γ b c}{x} → sn n (Es [ x ]*) → sn n t → SN {i} n (Es [ subst (sgs u) t ]*)
           → sn n u → sn n (Es [ app (abs t) u ]*)
  appsn₃ {Es = Es} x t t[u] u = acc (λ t⇒ → help {Es = Es} x t t[u] u (mkEhole* Es) t⇒) where
    help : ∀ {i n a b c Γ} {u : Tm Γ a} {t : Tm (a ∷ Γ) b} {t' : Tm Γ c} {x}  {z}{Es : ECxt* Γ b c} → sn n (Es [ x ]*) → sn n t →
         SN {i} n (Es [ subst (u ∷s var) t ]*) →
         sn n u → Ehole* z Es (app (abs t) u) → z ⟨ n ⟩⇒β t' → sn n t'
    help {Es = Es} x t t[u]∈sn u∈sn eq t⇒ with split Es eq β t⇒
    help x t₂ t[u]∈sn u∈sn eq t⇒ | inj₁ (._ , a₁ , β) rewrite hole*→≡ a₁ = fromSN t[u]∈sn
    help {Es = Es} x (acc t₃) t[u]∈sn u∈sn eq t⇒ | inj₁ (._ , a₁ , cong (appl u₁) (appl .u₁) (cong abs abs b₁)) rewrite hole*→≡ a₁
      = appsn₃ {Es = Es} x (t₃ b₁) (mapNβSN (cong*2 Es (NReduction.subst⇒β (sgs u₁) b₁)) t[u]∈sn) u∈sn
    help {t = t} {Es = Es} x t₃ t[u]∈sn (acc u∈sn) eq t⇒ | inj₁ (._ , a₁ , cong (appr ._) (appr ._) b₁) rewrite hole*→≡ a₁
      = appsn₃ {Es = Es} x t₃ (mapβ*SN (cong*4 Es
                                          (subst⇒β* (λ { {._} zero → nβ⇒β b₁ ∷ [] ; (suc n) → [] }) t)) t[u]∈sn) (u∈sn b₁)
    help {x = x} (acc f) t₂ t[u]∈sn u∈sn eq t⇒ | inj₂ (Es' , a , g) rewrite hole*→≡ a
         = appsn₃ {Es = Es'} (f (g x)) t₂ (mapNβSN (g _) t[u]∈sn) u∈sn


  helperCxt : ∀ {i j Γ n a b} {t th to : Tm Γ a}  → (Es : ECxt* Γ a b)
              →       i size t ⟨ n ⟩⇒ th → SN {j} n (Es [ th ]*) → sn n (Es [ th ]*) -> t ⟨ n ⟩⇒β to → sn n (Es [ to ]*)

  helperCxt E (β 𝒖)    𝒕h 𝑡h β    = 𝑡h

  helperCxt E (β         𝒖) 𝒕h 𝑡h (cong (appl  u) (appl .u) (cong abs abs t⇒))
    = appsn₃ {Es = E} 𝑡h (sn⇒β (antiSubst (subexpsn E 𝑡h)) t⇒)
              (mapNβSN (cong*2 E (NReduction.subst⇒β (sgs u) t⇒)) 𝒕h)
              (fromSN 𝒖)
  helperCxt E (β {t = t} 𝒖) 𝒕h 𝑡h (cong (appr ._) (appr ._)               t⇒)
    = appsn₃ {Es = E} 𝑡h (antiSubst (subexpsn E 𝑡h))
              (mapβ*SN (cong*4 E (subst⇒β* (λ { {._} zero → nβ⇒β t⇒ ∷ [] ; (suc x) → [] }) t)) 𝒕h)
              (sn⇒β (fromSN 𝒖) t⇒)

  helperCxt E (cong (appl u) (appl .u) (cong () 𝑬𝒕' th⇒)) 𝒕h 𝑡h β

  helperCxt E (cong (appl u) (appl .u) th⇒) 𝒕h 𝑡h (cong (appl .u)    (appl .u)    t⇒) = helperCxt (appl u ∷ E) th⇒ 𝒕h 𝑡h t⇒

  helperCxt E (cong (appl u) (appl .u) th⇒) 𝒕h (acc 𝑡h) (cong (appr t) (appr .t)           t⇒)
            = acc (helperCxt [] (E [ cong (appl _) (appl _) th⇒ ]⇒*) (mapNβSN t⇒' 𝒕h) (𝑡h t⇒'))
               where t⇒' = E [ cong (appr _) (appr _)           t⇒  ]⇒β*


  fromSN : ∀ {i} {Γ} {n : ℕ} {a} {t : Tm Γ a} → SN {i} n t → sn n t
  fromSN (ne 𝒏)       = fromSNe 𝒏
  fromSN (abs t₁)     = abssn (fromSN t₁)
  fromSN (exp t⇒ t₁)  = acc (helperCxt [] t⇒ t₁ (fromSN t₁))

  fromSNe : ∀ {i Γ n a} {t : Tm Γ a} → SNe {i} n t → sn n t
  fromSNe (elim 𝒏 E) = acc (elimsn (fromSNe 𝒏) (mapPCxt fromSN E) 𝒏)
  fromSNe (var x)    = varsn x
