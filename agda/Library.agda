-- Interface to standard library.

module Library where

open import Function public
  hiding (_∋_)

open import Level public
  using (Level) renaming (zero to lzero; suc to lsuc)

open import Size public

open import Category.Monad public
  using (RawMonad; module RawMonad)

open import Data.Empty public
  using (⊥; ⊥-elim)

open import Data.List public
  using (List; []; _∷_; map)

open import Data.Maybe public
  using (Maybe; just; nothing) renaming (map to fmap)

open import Data.Nat public
  using (ℕ; zero; suc; _+_; _≟_)

open import Data.Product public
  using (∃; _×_; _,_) renaming (proj₁ to fst; proj₂ to snd)
--infixr 1 _,_

open import Data.Sum public
  using (_⊎_; [_,_]′) renaming (inj₁ to inl; inj₂ to inr)

open import Data.Unit  public
  using (⊤)

open import Function public
  using (_∘_; flip; case_of_)
  renaming (id to idf)

open import Relation.Nullary public
  using (Dec; yes; no)

open import Relation.Binary public
  using (Setoid; module Setoid)

import Relation.Binary.PreorderReasoning
module Pre = Relation.Binary.PreorderReasoning

open import Relation.Binary.PropositionalEquality public
  using ( _≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning
        ; inspect; [_])

--open ≡-Reasoning renaming (begin_ to proof_) public

open import Relation.Binary.HeterogeneousEquality public
  using (_≅_; refl; ≡-to-≅; module ≅-Reasoning)
  renaming (sym to hsym; trans to htrans; cong to hcong;
            cong₂ to hcong₂; subst to hsubst)
{-
hcong₃ : {A : Set}
         {B : A → Set}
         {C : ∀ a → B a → Set}
         {D : ∀ a b → C a b → Set}
         (f : ∀ a b c → D a b c)
         {a a' : A} → a ≅ a' →
         {b : B a}{b' : B a'} → b ≅ b' →
         {c : C a b}{c' : C a' b'} → c ≅ c' →
         f a b c ≅ f a' b' c'
hcong₃ f refl refl refl = refl

≅-to-≡ : ∀ {a} {A : Set a} {x y : A} → x ≅ y → x ≡ y
≅-to-≡ refl = refl

record Cat : Set1 where
  field Obj  : Set
        Hom  : Obj → Obj → Set
        iden : ∀{X} → Hom X X
        comp : ∀{X Y Z} → Hom Y Z → Hom X Y → Hom X Z
        idl  : ∀{X Y}{f : Hom X Y} → comp iden f ≅ f
        idr  : ∀{X Y}{f : Hom X Y} → comp f iden ≅ f
        ass  : ∀{W X Y Z}{f : Hom Y Z}{g : Hom X Y}{h : Hom W X} →
               comp (comp f g) h ≅ comp f (comp g h)
open Cat public

record Fun (C D : Cat) : Set where
  open Cat
  field OMap  : Obj C → Obj D
        HMap  : ∀{X Y} → Hom C X Y → Hom D (OMap X) (OMap Y)
        fid   : ∀{X} → HMap (iden C {X}) ≅ iden D {OMap X}
        fcomp : ∀{X Y Z}{f : Hom C Y Z}{g : Hom C X Y} →
                HMap (comp C f g) ≅ comp D (HMap f) (HMap g)

open Fun public

postulate ext : {A : Set}{B B' : A → Set}{f : ∀ a → B a}{g : ∀ a → B' a} →
                (∀ a → f a ≅ g a) → f ≅ g

postulate iext : {A : Set}{B B' : A → Set}
                 {f : ∀ {a} → B a}{g : ∀{a} → B' a} →
                 (∀ a → f {a} ≅ g {a}) →
                 _≅_ {_}{ {a : A} → B a} f { {a : A} → B' a} g
-}
