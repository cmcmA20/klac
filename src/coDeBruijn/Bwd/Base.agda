{-# OPTIONS --safe #-}
module coDeBruijn.Bwd.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′

infixl 17 _-,_
data Bwd (A : Type ℓ) : Type ℓ where
  []   :             Bwd A
  _-,_ : Bwd A → A → Bwd A

infixl 6 _++_
_++_ : Bwd A → Bwd A → Bwd A
xs ++ []      = xs
xs ++ ys -, y = (xs ++ ys) -, y

map : (A → B) → Bwd A → Bwd B
map f []        = []
map f (xs -, x) = map f xs -, f x

_|>_ : {B : A → Type ℓ′} → (a : A) → ((a : A) → B a) → B a
_|>_ = flip _$_

module Thinning (K : Type ℓ) where

  private variable
    k : K
    iz iz′ jz jz′ kz kz′ ijz ijz′ : Bwd K

  infixr 19 _⊑_
  data _⊑_ : (_ _ : Bwd K) → Type ℓ where
    _o′ : iz ⊑ jz → iz        ⊑ (jz -, k)
    _os : iz ⊑ jz → (iz -, k) ⊑ (jz -, k)
    oz  :           []        ⊑ []

  _⟵_ : K → Bwd K → Type ℓ
  k ⟵ kz = ([] -, k) ⊑ kz

  _++⊑_ : (θ : iz ⊑ jz) (φ : iz′ ⊑ jz′) → (iz ++ iz′) ⊑ (jz ++ jz′)
  θ ++⊑ (φ o′) = (θ ++⊑ φ) o′
  θ ++⊑ (φ os) = (θ ++⊑ φ) os
  θ ++⊑ oz     = θ

  oi : kz ⊑ kz
  oi {[]     } = oz
  oi {_  -, _} = oi os

  oe : [] ⊑ kz
  oe {[]     } = oz
  oe {_  -, _} = oe o′

  infixl 24 _⋆_
  _⋆_ : (θ : iz ⊑ jz) (φ : jz ⊑ kz) → iz ⊑ kz
  θ      ⋆ (φ o′) = (θ ⋆ φ) o′
  (θ o′) ⋆ (φ os) = (θ ⋆ φ) o′
  (θ os) ⋆ (φ os) = (θ ⋆ φ) os
  oz     ⋆ oz     = oz
