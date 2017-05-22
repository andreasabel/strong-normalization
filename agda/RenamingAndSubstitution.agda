module RenamingAndSubstitution where

open import Library
open import Syntax
open ≡-Reasoning

infixr 4 _,_

------------------------------------------------------------------------
-- Renaming
------------------------------------------------------------------------

-- Renamings from Γ to Δ are snoc-lists of variables living in Δ,
-- one for each entry in Γ.

data Ren (Δ : Cxt) : (Γ : Cxt) → Set where
  ε   : Ren Δ ε
  _,_ : ∀ {Γ a} (ρ : Ren Δ Γ) (x : Var Δ a) → Ren Δ (Γ , a)

-- A renaming in  Ren Δ Γ  is a code for a
-- renaming function in  Var Γ ∙→ Var Δ.

lookr : ∀{Γ Δ} → Ren Δ Γ → ∀ {σ} → Var Γ σ → Var Δ σ
lookr (xs , x) zero    = x
lookr (xs , x) (suc i) = lookr xs i

-- Weaking a renaming by increasing all variables by 1.
-- This lets them live in the extended context Γ , σ.

wkr : ∀{Γ Δ σ} → Ren Γ Δ → Ren (Γ , σ) Δ
wkr ε        = ε
wkr (xs , x) = wkr xs , suc x

-- Lifting a renaming to go under a binder.

liftr : ∀{Γ Δ σ} → Ren Γ Δ → Ren (Γ , σ) (Δ , σ)
liftr xs = wkr xs , zero

-- The category of renamings (operations only).
------------------------------------------------------------------------

-- The identity renaming.

renId : ∀{Γ} → Ren Γ Γ
renId {ε}     = ε
renId {Γ , _} = liftr (renId {Γ})

-- Forward composition of renamings.

renComp : ∀{Φ Γ Δ} → Ren Δ Γ → Ren Γ Φ → Ren Δ Φ
renComp xs ε        = ε
renComp xs (ys , y) = renComp xs ys , lookr xs y

-- Various combinations of renamings.
------------------------------------------------------------------------

-- Weakening a renaming acts behaves like
-- post-composing the renaming function with successor.

lookrwkr : ∀{Γ Δ σ τ}(xs : Ren Δ Γ)(i : Var Γ σ) →
           lookr (wkr {σ = τ} xs) i ≡ suc (lookr xs i)
lookrwkr (xs , _) zero    = refl
lookrwkr (xs , _) (suc i) = lookrwkr xs i

-- A weakning cancels a renaming extension.

lemrr : ∀{Φ Γ Δ σ}(xs : Ren Φ Γ)(x : Var Φ σ)(ys : Ren Γ Δ) →
       renComp (xs , x) (wkr ys) ≡ renComp xs ys
lemrr xs x ε        = refl
lemrr xs x (ys , y) = cong (_, lookr xs y) (lemrr xs x ys)

-- Associativity of renaming composition in case the first
-- renaming is a weakening.

wkrcomp : ∀{Φ Γ Δ σ}(xs : Ren Φ Γ)(ys : Ren Γ Δ) →
  renComp (wkr {σ = σ} xs) ys ≡ wkr {σ = σ} (renComp xs ys)
wkrcomp xs ε        = refl
wkrcomp xs (ys , y) = cong₂ _,_ (wkrcomp xs ys) (lookrwkr xs y)

-- Composition of liftings is a lifting.

liftrcomp : ∀{Φ Γ Δ σ}(xs : Ren Φ Γ)(ys : Ren Γ Δ) →
  renComp (liftr {σ = σ} xs) (liftr {σ = σ} ys) ≡ liftr {σ = σ} (renComp xs ys)
liftrcomp xs ys = begin
  renComp (wkr xs , zero) (wkr ys) , zero  ≡⟨ cong (_, zero) (lemrr (wkr xs) zero ys) ⟩
  renComp (wkr xs) ys              , zero  ≡⟨ cong (_, zero) (wkrcomp xs ys) ⟩
  wkr (renComp xs ys)              , zero  ∎

-- lookr is a morphism from the category  Ren
-- to the category of the corresponding renaming functions on variables.
------------------------------------------------------------------------

-- The identity renaming corresponds to the identity function.

lookrid : ∀{Γ σ}(x : Var Γ σ) → lookr renId x ≡ x
lookrid zero    = refl
lookrid (suc x) = begin
  lookr (wkr renId) x  ≡⟨ lookrwkr renId x ⟩
  suc (lookr renId x)  ≡⟨ cong suc (lookrid x) ⟩
  suc x                ∎

-- A composition of renamings corresponds to the composition
-- of the corresponding renaming functions.

lookrcomp : ∀{Φ Γ Δ}(f : Ren Δ Γ)(g : Ren Γ Φ){σ}(i : Var Φ σ) →
            lookr (renComp f g) i ≡ (lookr f ∘ lookr g) i
lookrcomp f (g , v) zero = refl
lookrcomp f (g , v) (suc i) = lookrcomp f g i

-- Laws for the category of renamings.
------------------------------------------------------------------------

-- Left identity of forward composition

lidr : ∀{Φ Γ}(xs : Ren Φ Γ) → renComp renId xs ≡ xs
lidr ε        = refl
lidr (xs , x) = cong₂ _,_ (lidr xs) (lookrid x)

-- Right identity of forward composition

ridr : ∀{Φ Γ}(xs : Ren Φ Γ) → renComp xs renId ≡ xs
ridr {Γ = ε}     ε  = refl
ridr {Γ = Γ , σ} (xs , x) = begin
  renComp (xs , x) (wkr renId) , x  ≡⟨ cong (_, x) (lemrr xs x renId) ⟩
  renComp xs renId             , x  ≡⟨ cong (_, x) (ridr xs) ⟩
  xs                           , x  ∎


-- Renaming of terms.
------------------------------------------------------------------------

-- Renaming in a term.

ren : ∀{Γ Δ} → Ren Δ Γ → ∀ {σ} → Tm Γ σ → Tm Δ σ
ren xs (var x)   = var (lookr xs x)
ren xs (abs t)   = abs (ren (liftr xs) t)
ren xs (app t u) = app (ren xs t) (ren xs u)

-- ren is a morphism from Ren
-- to the corresponding category of renaming functions on terms.

renid : ∀{Γ σ}(t : Tm Γ σ) → ren renId t ≡ t
renid (var x)   = cong var (lookrid x)
renid (abs t)   = cong abs (renid t)
renid (app t u) = cong₂ app (renid t) (renid u)

rencomp : ∀ {Φ Γ Δ}(f : Ren Δ Γ)(g : Ren Γ Φ){σ}(t : Tm Φ σ) →
            ren (renComp f g) t ≡ (ren f ∘ ren g) t
rencomp f g (var x)   = cong var (lookrcomp f g x)
rencomp f g (abs t)   = begin
  abs (ren (liftr (renComp f g))         t)   ≡⟨ cong (λ xs → abs $ ren xs t) (sym $ liftrcomp f g) ⟩
  abs (ren (renComp (liftr f) (liftr g)) t)   ≡⟨ cong abs (rencomp (liftr f) (liftr g) t) ⟩
  abs (ren (liftr f) (ren (liftr g) t))       ∎
rencomp f g (app t u) = cong₂ app (rencomp f g t) (rencomp f g u)

-- Weakening a term.

weak : ∀{Γ b} a → Tm Γ b → Tm (Γ , a) b
weak a = ren (wkr renId)


-- Renaming of normal forms.
------------------------------------------------------------------------

mutual
  rennf : ∀{Γ Δ} → Ren Γ Δ → ∀{a} → Nf Δ a → Nf Γ a
  rennf α (ne t)   = ne (rennen α t)
  rennf α (abs t)  = abs (rennf (liftr α) t)

  rennen : ∀{Γ Δ} → Ren Γ Δ → ∀{a} → Ne Δ a → Ne Γ a
  rennen α (var x) = var (lookr α x)
  rennen α (app n x) = app (rennen α n) (rennf α x)

------------------------------------------------------------------------
-- Substitution
------------------------------------------------------------------------

data Sub (Δ : Cxt) : (Γ : Cxt) → Set where
  ε   : Sub Δ ε
  _,_ : ∀ {Γ a} (ρ : Sub Δ Γ) (v : Tm Δ a) → Sub Δ (Γ , a)

ren2sub : ∀{Γ Δ} → Ren Γ Δ → Sub Γ Δ
ren2sub ε        = ε
ren2sub (xs , x) = ren2sub xs , var x

looks : ∀{Γ Δ} → Sub Δ Γ → ∀ {σ} → Var Γ σ → Tm Δ σ
looks (xs , x) zero    = x
looks (xs , x) (suc i) = looks xs i

wks : ∀{Γ Δ σ} → Sub Γ Δ → Sub (Γ , σ) Δ
wks ε        = ε
wks (xs , x) = wks xs , ren (wkr renId) x

lifts : ∀{Γ Δ σ} → Sub Γ Δ → Sub (Γ , σ) (Δ , σ)
lifts xs = wks xs , var zero

sub : ∀{Γ Δ} → Sub Δ Γ → ∀{σ} → Tm Γ σ → Tm Δ σ
sub xs (var x)   = looks xs x
sub xs (abs t)   = abs (sub (lifts xs) t)
sub xs (app t u) = app (sub xs t) (sub xs u)

subId : ∀{Γ} → Sub Γ Γ
subId {ε}     = ε
subId {Γ , _} = lifts (subId {Γ})

subComp : ∀{Φ Γ Δ} → Sub Δ Γ → Sub Γ Φ → Sub Δ Φ
subComp xs ε        = ε
subComp xs (ys , y) = subComp xs ys , sub xs y

-- Substitute the last variable

sub0 : ∀{Γ a b} → Tm (Γ , a) b → Tm Γ a → Tm Γ b
sub0 t u = sub (subId , u) t

-- Substitution laws

lookswks : ∀{Γ Δ σ τ}(i : Var Γ σ)(xs : Sub Δ Γ) →
           looks (wks {σ = τ} xs) i ≡ ren (wkr {σ = τ} renId) (looks xs i)
lookswks zero    (xs , _) = refl
lookswks (suc i) (xs , _) = lookswks i xs

lemsr : ∀{Φ Γ Δ σ}(xs : Sub Φ Γ)(x : Tm Φ σ)(ys : Ren Γ Δ) →
        subComp (xs , x) (ren2sub (wkr ys)) ≡ subComp xs (ren2sub ys)
lemsr xs x ε        = refl
lemsr xs x (ys , y) = cong (λ zs → zs , looks xs y) (lemsr xs x ys)

lookslookr : ∀{Φ Γ Δ}(f : Sub Δ Γ)(g : Ren Γ Φ){σ}(x : Var Φ σ) →
            looks (subComp f (ren2sub g)) x ≡ looks f (lookr g x)
lookslookr f (g , _) zero    = refl
lookslookr f (g , _) (suc x) = lookslookr f g x

wksrcomp : ∀{Φ Γ Δ σ}(xs : Sub Φ Γ)(ys : Ren Γ Δ) →
  subComp (wks {σ = σ} xs) (ren2sub ys) ≡ wks {σ = σ} (subComp xs (ren2sub ys))
wksrcomp xs ε        = refl
wksrcomp xs (ys , y) = cong₂ Sub._,_ (wksrcomp xs ys) (lookswks y xs)

liftsrcomp : ∀{Φ Γ Δ σ}(xs : Sub Φ Γ)(ys : Ren Γ Δ) →
             subComp (lifts {σ = σ} xs) (ren2sub (liftr ys)) ≡ lifts {σ = σ} (subComp xs (ren2sub ys))
liftsrcomp xs ys = begin
  subComp (wks xs , var zero) (ren2sub (wkr ys)) , var zero ≡⟨ cong (_, var zero) (lemsr (wks xs) (var zero) ys) ⟩
  subComp (wks xs) (ren2sub ys)                  , var zero ≡⟨ cong (_, var zero) (wksrcomp xs ys) ⟩
  wks (subComp xs (ren2sub ys))                  , var zero ∎

subren : ∀{Φ Γ Δ}(f : Sub Δ Γ)(g : Ren Γ Φ){σ}(t : Tm Φ σ) →
         (sub f ∘ ren g) t ≡ sub (subComp f (ren2sub g)) t
subren f g (var x)   = sym $ lookslookr f g x
subren f g (abs t)   = begin
  abs (sub (lifts f) (ren (liftr g) t))               ≡⟨ cong abs $ subren (lifts f) (liftr g) t ⟩
  abs (sub (subComp (lifts f) (ren2sub (liftr g))) t) ≡⟨ cong (λ f → abs (sub f t)) $ liftsrcomp f g ⟩
  abs (sub (lifts (subComp f (ren2sub g))) t)         ∎
subren f g (app t u) = cong₂ app (subren f g t) (subren f g u)

looksid : ∀{Γ σ}(x : Var Γ σ) → looks subId x ≡ var x
looksid zero    = refl
looksid (suc x) = begin
  looks (wks subId) x             ≡⟨ lookswks x subId ⟩
  ren (wkr renId) (looks subId x) ≡⟨ cong (ren (wkr renId)) (looksid x) ⟩
  ren (wkr renId) (var x)         ≡⟨⟩
  var (lookr (wkr renId) x)       ≡⟨ cong var $ lookrwkr renId x ⟩
  var (suc (lookr renId x))       ≡⟨ cong (λ x → var (suc x)) (lookrid x) ⟩ -- using ∘ makes it go yellow
  var (suc x)                     ∎

subid : ∀{Γ σ}(t : Tm Γ σ) → sub subId t ≡ t
subid (var x)   = looksid x
subid (abs t)   = cong abs (subid t)
subid (app t u) = cong₂ app (subid t) (subid u)

sidl : ∀{Φ Γ}(xs : Sub Φ Γ) → subComp subId xs ≡ xs
sidl ε        = refl
sidl (xs , t) = cong₂ _,_ (sidl xs) (subid t)

sidr2 : ∀{Φ Γ}(xs : Sub Φ Γ) → subComp xs (ren2sub renId) ≡ xs
sidr2 {Γ = ε} ε            = refl
sidr2 {Γ = Γ , a} (xs , x) = begin
  subComp (xs , x) (ren2sub (wkr renId)) , x ≡⟨ cong (_, x) (lemsr xs x renId) ⟩
  subComp xs (ren2sub renId)             , x ≡⟨ cong (_, x) (sidr2 xs) ⟩
  xs                                     , x ∎

liftSubRen : ∀{Γ Δ a b} (f : Sub Δ Γ) (t : Tm Γ b)
  → sub (lifts f) (weak a t) ≡ sub (wks f) t
liftSubRen {a = a} f t = begin
  sub (lifts f) (weak a t)  ≡⟨ subren (lifts f) (wkr renId) t ⟩
  sub (subComp (lifts f) (ren2sub (wkr renId))) t ≡⟨ cong (λ f' → sub f' t) (lemsr (wks f) (var zero) renId) ⟩
  sub (subComp (wks f) (ren2sub renId)) t ≡⟨ cong (λ f' → sub f' t) (sidr2 (wks f)) ⟩
  sub (wks f) t ∎

lemss : ∀{Φ Γ Δ σ}(xs : Sub Φ Γ)(x : Tm Φ σ)(ys : Sub Γ Δ) →
        subComp (xs , x) (wks ys) ≡ subComp xs ys
lemss xs x ε        = refl
lemss xs x (ys , y) = begin
  subComp (xs , x) (wks ys) , sub (xs , x) (ren (wkr renId) y)               ≡⟨ cong₂ _,_ (lemss xs x ys) (subren (xs , x) (wkr renId) y) ⟩
  subComp xs       ys       , sub (subComp (xs , x) (ren2sub (wkr renId))) y ≡⟨ cong (λ g → subComp xs ys , sub g y) (lemsr xs x renId) ⟩
  subComp xs       ys       , sub (subComp xs       (ren2sub renId))       y ≡⟨ cong (λ g → subComp xs ys , sub g y) (sidr2 xs) ⟩
  subComp xs       ys       , sub xs                                       y ∎

ren2sublook : ∀{Γ Δ σ}(f : Ren Δ Γ)(i : Var Γ σ) →
              var (lookr f i) ≡ looks (ren2sub f) i
ren2sublook (f , _) zero    = refl
ren2sublook (f , _) (suc i) = ren2sublook f i

ren2subwk : ∀{Γ Δ σ}(g : Ren Δ Γ) →
            ren2sub (wkr {σ = σ} g) ≡ wks {σ = σ} (ren2sub g)
ren2subwk ε       = refl
ren2subwk (g , x) = begin
  (ren2sub (wkr g) , var (suc x))               ≡⟨ cong₂ (λ xs x → xs , var (suc x)) (ren2subwk g) (sym $ lookrid x) ⟩
  (wks (ren2sub g) , var (suc (lookr renId x))) ≡⟨ cong (λ x → wks (ren2sub g) , var x) (sym $ lookrwkr renId x) ⟩
  (wks (ren2sub g) , var (lookr (wkr renId) x)) ∎

ren2sublift : ∀{Γ Δ σ}(g : Ren Δ Γ) →
            ren2sub (liftr {σ = σ} g) ≡ lifts {σ = σ} (ren2sub g)
ren2sublift g = cong (_, var zero) (ren2subwk g)

ren2subren : ∀{Γ Δ σ}(f : Ren Δ Γ)(t : Tm Γ σ) → ren f t ≡ sub (ren2sub f) t
ren2subren f (var x)   = ren2sublook f x
ren2subren f (abs t)   = begin
  abs (ren (liftr f) t)               ≡⟨ cong abs (ren2subren (liftr f) t) ⟩
  abs (sub (ren2sub (liftr f)) t)     ≡⟨ cong (λ f → abs (sub f t)) (ren2sublift f) ⟩
  abs (sub (lifts (ren2sub f)) t) ∎
ren2subren f (app t u) = cong₂ app (ren2subren f t) (ren2subren f u)

wkrscomp : ∀{Φ Γ Δ σ}(xs : Ren Φ Γ)(ys : Sub Γ Δ) →
  subComp (ren2sub (wkr {σ = σ} xs)) ys ≡ wks {σ = σ} (subComp (ren2sub xs) ys)
wkrscomp xs ε        = refl
wkrscomp xs (ys , y) = begin
  subComp (ren2sub (wkr xs)) ys , sub (ren2sub (wkr xs)) y                 ≡⟨ cong₂ _,_ (wkrscomp xs ys) (sym $ ren2subren (wkr xs) y) ⟩
  wks (subComp (ren2sub xs) ys) , ren (wkr xs) y                           ≡⟨ cong (λ f → wks (subComp (ren2sub xs) ys) , ren (wkr f) y) (sym $ lidr xs) ⟩
  wks (subComp (ren2sub xs) ys) , ren (wkr (renComp renId xs))  y          ≡⟨ cong (λ f → wks (subComp (ren2sub xs) ys) , ren f y) (sym $ wkrcomp renId xs) ⟩
  wks (subComp (ren2sub xs) ys) , ren (renComp (wkr renId)  xs) y          ≡⟨ cong (wks (subComp (ren2sub xs) ys) ,_) (rencomp (wkr renId) xs y) ⟩
  wks (subComp (ren2sub xs) ys) , ren (wkr renId) (ren xs y)               ≡⟨ cong (λ t → wks (subComp (ren2sub xs) ys) , ren (wkr renId) t) (ren2subren xs y)  ⟩
  wks (subComp (ren2sub xs) ys) , ren (wkr renId) (sub (ren2sub xs) y)     ∎

liftrscomp : ∀{Φ Γ Δ σ}(xs : Ren Φ Γ)(ys : Sub Γ Δ) →
  subComp (ren2sub (liftr {σ = σ} xs)) (lifts ys) ≡ lifts {σ = σ} (subComp (ren2sub xs) ys)
liftrscomp xs ys = begin
  (subComp (ren2sub (wkr xs) , var zero) (wks ys) , var zero) ≡⟨ cong (_, var zero) (lemss (ren2sub (wkr xs)) (var zero) ys) ⟩
  (subComp (ren2sub (wkr xs)) ys                  , var zero) ≡⟨ cong (_, var zero) (wkrscomp xs ys) ⟩
  (wks (subComp (ren2sub xs) ys)                  , var zero) ∎

renlooks : ∀{Φ Γ Δ}(f : Ren Δ Γ)(g : Sub Γ Φ){σ}(x : Var Φ σ) →
         (ren f ∘ looks g) x ≡ looks (subComp (ren2sub f) g) x
renlooks f (_ , v) zero    = ren2subren f v
renlooks f (g , _) (suc x) = renlooks f g x

rensub : ∀{Φ Γ Δ}(f : Ren Δ Γ)(g : Sub Γ Φ){σ}(t : Tm Φ σ) →
         (ren f ∘ sub g) t ≡ sub (subComp (ren2sub f) g) t
rensub f g (var x) = renlooks f g x
rensub f g (abs t) = begin
  abs (ren (liftr f) (sub (lifts g) t))               ≡⟨ cong abs $ rensub (liftr f) (lifts g) t ⟩
  abs (sub (subComp (ren2sub (liftr f)) (lifts g)) t) ≡⟨ cong (λ f → abs (sub f t)) (liftrscomp f g) ⟩
  abs (sub (lifts (subComp (ren2sub f) g)) t)         ∎
rensub f g (app t u) = cong₂ app (rensub f g t) (rensub f g u)

lookscomp : ∀{Φ Γ Δ}(f : Sub Δ Γ)(g : Sub Γ Φ){σ}(x : Var Φ σ) →
            looks (subComp f g) x ≡ sub f (looks g x)
lookscomp f (g , _) zero    = refl
lookscomp f (g , _) (suc x) = lookscomp f g x

ren2subid : ∀{Γ} → subId {Γ} ≡ ren2sub renId
ren2subid {ε}     = refl
ren2subid {Γ , a} = begin
  (wks subId           , var zero) ≡⟨ cong (λ f → wks f , var zero) (ren2subid {Γ}) ⟩
  (wks (ren2sub renId) , var zero) ≡⟨ cong (_, var zero) (sym $ ren2subwk renId) ⟩
  (ren2sub (wkr renId) , var zero) ∎

wksscomp : ∀{Φ Γ Δ σ}(xs : Sub Φ Γ)(ys : Sub Γ Δ) →
  subComp (wks {σ = σ} xs) ys ≡ wks {σ = σ} (subComp xs ys)
wksscomp xs ε        = refl
wksscomp xs (ys , y) = begin
  subComp (wks xs) ys , sub (wks xs)                           y ≡⟨ cong (λ f → subComp (wks xs) ys , sub (wks f) y) (sym $ sidl xs) ⟩
  subComp (wks xs) ys , sub (wks (subComp subId xs))           y ≡⟨ cong₂ _,_ (wksscomp xs ys) (cong (λ f → sub (wks (subComp f xs)) y) ren2subid) ⟩
  wks (subComp xs ys) , sub (wks (subComp (ren2sub renId) xs)) y ≡⟨ cong (λ f → wks (subComp xs ys) , sub f y) (sym $ wkrscomp renId xs) ⟩
  wks (subComp xs ys) , sub (subComp (ren2sub (wkr renId)) xs) y ≡⟨ cong (wks (subComp xs ys) ,_) (sym $ rensub (wkr renId) xs y) ⟩
  wks (subComp xs ys) , ren (wkr renId) (sub xs y)               ∎

sidr : ∀{Φ Γ}(xs : Sub Φ Γ) → subComp xs subId ≡ xs
sidr xs = begin
  subComp xs subId           ≡⟨ cong (subComp xs) ren2subid ⟩
  subComp xs (ren2sub renId) ≡⟨ sidr2 xs ⟩
  xs                         ∎

liftscomp : ∀{Φ Γ Δ σ}(xs : Sub Φ Γ)(ys : Sub Γ Δ) →
  subComp (lifts {σ = σ} xs) (lifts ys) ≡ lifts {σ = σ} (subComp xs ys)
liftscomp xs ys = begin
  subComp (wks xs , var zero) (wks ys) , var zero ≡⟨ cong (_, var zero) (lemss (wks xs) (var zero) ys) ⟩
  subComp (wks xs) ys                  , var zero ≡⟨ cong (_, var zero) (wksscomp xs ys) ⟩
  wks (subComp xs ys)                  , var zero ∎

subcomp : ∀{Φ Γ Δ}(f : Sub Δ Γ)(g : Sub Γ Φ){σ}(t : Tm Φ σ) →
          sub (subComp f g) t ≡ (sub f ∘ sub g) t
subcomp f g (var x)   = lookscomp f g x
subcomp f g (abs t)   = begin
  abs (sub (lifts (subComp f g)) t)         ≡⟨ cong (λ f → abs (sub f t)) (sym $ liftscomp f g) ⟩
  abs (sub (subComp (lifts f) (lifts g)) t) ≡⟨ cong abs (subcomp (lifts f) (lifts g) t) ⟩
  abs (sub (lifts f) (sub (lifts g) t))     ∎
subcomp f g (app t u) = cong₂ app (subcomp f g t) (subcomp f g u)

--

mutual
  renembNe : ∀{Γ Δ a}(u : Ne Γ a)(σ : Ren Δ Γ) →
             ren σ (embNe u) ≡ embNe (rennen σ u)
  renembNe (var x)   σ = refl
  renembNe (app u n) σ = cong₂ app (renembNe u σ) (renembNf n σ)

  renembNf : ∀{Γ Δ a}(n : Nf Γ a)(σ : Ren Δ Γ) →
             ren σ (embNf n) ≡ embNf (rennf σ n)
  renembNf (abs n) σ = cong abs (renembNf n (liftr σ))
  renembNf (ne n)  σ = renembNe n σ
-- -}
