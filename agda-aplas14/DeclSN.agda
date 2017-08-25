module DeclSN where

open import Data.Sum
open import Library
open import Terms
open import Substitution
open import TermShape
open import SN
open import Reduction

-- SN as accessibility

data sn {Γ} {a} (t : Tm Γ a) : Set where
  acc : (∀ {t'} → t ⇒β t' → sn t') → sn t

sn⇒β :  ∀ {Γ} {a} {t t' : Tm Γ a} → sn t → t ⇒β t' → sn t'
sn⇒β (acc h) r = h r

varsn : ∀ {Γ} {a} (x : Var Γ a) → sn (var x)
varsn x = acc λ { (cong () _ _) }

abssn : ∀ {Γ} {a b} {t : Tm (a ∷ Γ) b} → sn t → sn (abs t)
abssn (acc f) = acc (λ { {._} (cong abs abs x)  → abssn (f x) })

subsn : ∀ {Γ Δ} {a b} {f : Tm Γ a -> Tm Δ b} →
        (g : ∀ {t t' : Tm Γ a} → t ⇒β t' → f t ⇒β f t') →
        ∀ {t} → sn (f t) → sn t
subsn g (acc ft) = acc λ t⇒ → subsn g (ft (g t⇒))

-- Goal here: prove that sne is closed under application.

appsn : ∀ {Γ a b} {t : Tm Γ (a →̂ b)} {u} → sn t → sn u → SNe t →
        ∀ {r : Tm Γ b} → app t u ⇒β r → sn r
appsn (acc 𝒕) 𝒖       𝒏           (cong (appl u) (appl .u) t⇒) = acc (appsn (𝒕 t⇒) 𝒖      (mapβSNe t⇒ 𝒏 ))
appsn 𝒕       (acc u) 𝒏           (cong (appr t) (appr .t) t⇒) = acc (appsn 𝒕      (u t⇒) 𝒏)
appsn 𝒕       u       (elim 𝒏 ()) β

elimsn : ∀ {Γ a b}{E : ECxt Γ a b}{t : Tm Γ a}{Et : Tm Γ b} → sn t → PCxt sn Et E t → SNe t →
         ∀ {Et' : Tm Γ b} → Et ⇒β Et' → sn Et'
elimsn 𝒕 (appl 𝒖) 𝒏 t⇒ = appsn 𝒕 𝒖 𝒏 t⇒


substβsn : ∀ {i m vt a Γ} {Δ} {σ ρ : RenSub {m} vt Γ Δ} → (∀ {b} (x : Var Γ b) → vt2tm _ (σ x) ⇒β* vt2tm _ (ρ x))
             → (t : Tm Γ a) → SN {i} (subst σ t) → SN {i} (subst ρ t)
substβsn f t =  mapβ*SN (subst⇒β* f t)

antiSubst : ∀ {Γ a b} {t : Tm (a ∷ Γ) b}{u : Tm Γ a} → sn (subst (sgs u) t) → sn t
antiSubst {t = t} = subsn (λ x → subst⇒β (sgs _) x)

_[_]⇒β : ∀ {Γ} {a b} (E : ECxt Γ a b) {t₁ t₂ : Tm Γ a} →  t₁ ⇒β t₂ → E [ t₁ ] ⇒β E [ t₂ ]
appl u [ t⇒ ]⇒β = cong (appl u) (appl u) t⇒

_[_]⇒β* : ∀ {Γ} {a b} (E : ECxt* Γ a b) {t₁ t₂ : Tm Γ a} → t₁ ⇒β t₂ → E [ t₁ ]* ⇒β E [ t₂ ]*
[]       [ t⇒ ]⇒β* = t⇒
(E ∷ Es) [ t⇒ ]⇒β* = Es [ E [ t⇒ ]⇒β ]⇒β*


cong*2 : ∀ {Γ a b t t'}(E : ECxt* Γ a b)
          → (t⇒ : t ⇒β t')
          → E [ t ]* ⇒β E [ t' ]*
cong*2 E t⇒ =  E [ t⇒ ]⇒β*


subexpsn : ∀ {Γ a b} (E : ECxt* Γ a b) {t : Tm Γ a} → sn (E [ t ]*) -> sn t
subexpsn E = subsn (cong*3 E)


data _Redex {Γ} : ∀ {a} → Tm Γ a → Set where

  β     : ∀ {a b}{t : Tm (a ∷ Γ) b}{u}
          → (app (abs t) u) Redex

mkHole2 : ∀ {Γ} {a b} (E : ECxt Γ a b) {t : Tm Γ a} → βEhole (E [ t ]) (EC→βEC E) t
mkHole2 (appl u) = appl u

mkHole3 : ∀ {Γ} {a b c} (E : ECxt Γ a b) {Es : ECxt* Γ _ _} {t : Tm Γ c} → βEhole ((Es ∷r E) [ t ]*) (EC→βEC E) (Es [ t ]*)
mkHole3 E {Es} {t} rewrite ≡.sym (lemma {t = t} Es {E = E}) = mkHole2 E {Es [ t ]*}

≡subst⇒β : ∀ {a Γ} {t t1 t' t'1 : Tm Γ a} → t ≡ t1 → t' ≡ t'1 → t ⇒β t' → t1 ⇒β t'1
≡subst⇒β ≡.refl ≡.refl x = x


split : ∀ {Γ} {a b} (E : ECxt* Γ a b) {t₁ : Tm Γ a}{t₂ Et₁ : Tm Γ b} →
         Ehole* Et₁ E t₁ → t₁ Redex →
         Et₁ ⇒β t₂ → (∃ λ t₃ → Ehole* t₂ E t₃ × t₁ ⇒β t₃)
         ⊎ (∃ λ E₁ → Ehole* t₂ E₁ t₁ × (∀ t → E [ t ]* ⇒β E₁ [ t ]*))
split ._ [] r t⇒ = inj₁ (_ , [] , t⇒)
split .(appl u ∷ []) (appl u ∷ []) () β
split ._ (appl u ∷ (() ∷ eq)) r β
split ._ (appl u ∷ eq) r (cong (appl .u) (appl .u) t⇒) with split _ eq r t⇒
split ._ (appl u ∷ eq) r (cong (appl .u) (appl .u) t⇒) | inj₁ (x , eq0 , t⇒') = inj₁ (_ , ((appl u) ∷ eq0) , t⇒')
split ._ (_∷_ {Es = Es} (appl u) eq) r (cong (appl .u) (appl .u) t⇒) | inj₂ (Es' , eq0 , f) = inj₂ (_ , ((appl u ∷ eq0) ,
                                                        (λ t → cong (mkHole3 (appl u) {Es}) (mkHole3 (appl u) {Es'}) (f t))))
split ._ (_∷_ {Es = Es} (appl t) eq) r (cong (appr Est) (appr .Est) t⇒) = inj₂ (_ , ((appl _ ∷ eq) ,
      (λ t₁ → ≡subst⇒β (lemma Es {E = appl t}) (lemma Es {E = appl _}) (_⇒β_.cong {E = (appr (Es [ t₁ ]*))} (βEhole.appr (Es [ t₁ ]*)) (appr (Es [ t₁ ]*)) t⇒))))

mutual

  appsn₃ : ∀ {i a b c Γ} {u : Tm Γ a} {t : Tm (a ∷ Γ) b}{Es : ECxt* Γ b c}{x} → sn (Es [ x ]*) → sn t → SN {i} (Es [ subst (sgs u) t ]*)
           → sn u → sn (Es [ app (abs t) u ]*)
  appsn₃ {Es = Es} x t t[u] u = acc (λ t⇒ → help {Es = Es} x t t[u] u (mkEhole* Es) t⇒)
    where
    help : ∀ {i a b c Γ} {u : Tm Γ a} {t : Tm (a ∷ Γ) b} {t' : Tm Γ c} {x}  {z}{Es : ECxt* Γ b c} → sn (Es [ x ]*) → sn t →
         SN {i} (Es [ subst (u ∷s var) t ]*) →
         sn u → Ehole* z Es (app (abs t) u) → z ⇒β t' → sn t'

    help {Es = Es} x t t[u]∈sn u∈sn eq t⇒ with split Es eq β t⇒
    help x t₂ t[u]∈sn u∈sn eq t⇒ | inj₁ (._ , a₁ , β) rewrite hole*→≡ a₁ = fromSN t[u]∈sn
    help {Es = Es} x (acc t₃) t[u]∈sn u∈sn eq t⇒ | inj₁ (._ , a₁ , cong (appl u₁) (appl .u₁) (cong abs abs b₁)) rewrite hole*→≡ a₁
      = appsn₃ {Es = Es} x (t₃ b₁) (mapβSN (cong*3 Es (subst⇒β (sgs u₁) b₁)) t[u]∈sn) u∈sn
    help {t = t} {Es = Es} x t₃ t[u]∈sn (acc u∈sn) eq t⇒ | inj₁ (._ , a₁ , cong (appr ._) (appr ._) b₁) rewrite hole*→≡ a₁
      = appsn₃ {Es = Es} x t₃ (mapβ*SN (cong*4 Es
                                          (subst⇒β* (λ { {._} zero → b₁ ∷ [] ; (suc n) → [] }) t)) t[u]∈sn) (u∈sn b₁)
    help {x = x} (acc f) t₂ t[u]∈sn u∈sn eq t⇒ | inj₂ (Es' , a , g) rewrite hole*→≡ a
         = appsn₃ {Es = Es'} (f (g x)) t₂ (mapβSN (g _) t[u]∈sn) u∈sn


  helperCxt : ∀ {i j Γ a b} {t th to : Tm Γ a}  → (Es : ECxt* Γ a b)
              →       t ⟨ i ⟩⇒ th → SN {j} (Es [ th ]*) → sn (Es [ th ]*) -> t ⇒β to → sn (Es [ to ]*)

  helperCxt E (β 𝒖)    𝒕h 𝑡h β    = 𝑡h

  helperCxt E (β         𝒖) 𝒕h 𝑡h (cong (appl  u) (appl .u) (cong abs abs t⇒))
    = appsn₃ {Es = E} 𝑡h (sn⇒β (antiSubst (subexpsn E 𝑡h)) t⇒)
              (mapβSN (cong*3 E (subst⇒β (sgs u) t⇒)) 𝒕h)
              (fromSN 𝒖)
  helperCxt E (β {t = t} 𝒖) 𝒕h 𝑡h (cong (appr ._) (appr ._) t⇒)
    = appsn₃ {Es = E} 𝑡h (antiSubst (subexpsn E 𝑡h))
              (mapβ*SN (cong*4 E (subst⇒β* (λ { zero → t⇒ ∷ [] ; (suc _) → [] }) t)) 𝒕h)
              (sn⇒β (fromSN 𝒖) t⇒)

  helperCxt E (cong (appl u) (appl .u) (cong () 𝑬𝒕' th⇒)) 𝒕h 𝑡h β

  helperCxt E (cong (appl u) (appl .u) th⇒) 𝒕h 𝑡h       (cong (appl .u) (appl .u) t⇒) = helperCxt (appl u ∷ E) th⇒ 𝒕h 𝑡h t⇒

  helperCxt E (cong (appl u) (appl .u) th⇒) 𝒕h (acc 𝑡h) (cong (appr t)  (appr .t) t⇒)
            = acc (helperCxt [] (E [ cong (appl _) (appl _) th⇒ ]⇒*) (mapβSN t⇒' 𝒕h) (𝑡h t⇒'))
               where
               t⇒' =  E [ cong (appr _) (appr _) t⇒  ]⇒β*


  fromSN : ∀ {i} {Γ} {a} {t : Tm Γ a} → SN {i} t → sn t
  fromSN (ne 𝒏)       = fromSNe 𝒏
  fromSN (abs t₁)     = abssn (fromSN t₁)
  fromSN (exp t⇒ t₁)  = acc (helperCxt [] t⇒ t₁ (fromSN t₁))

  fromSNe : ∀ {i Γ a} {t : Tm Γ a} → SNe {i} t → sn t
  fromSNe (elim 𝒏 E) = acc (elimsn (fromSNe 𝒏) (mapPCxt fromSN E) 𝒏)
  fromSNe (var x)    = varsn x
