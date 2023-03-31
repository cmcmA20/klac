{-# OPTIONS --safe #-}
open import Cubical.Foundations.Prelude
module coDeBruijn.Thinning.Base {𝑘} (K : Type 𝑘) where

open import Cubical.Foundations.Function

open import coDeBruijn.Bwd.Base

private variable
  i k : K
  iz iz′ jz jz′ kz : Bwd K

infixr 19 _⊑_
data _⊑_ : (_ _ : Bwd K) → Type 𝑘 where
  _o′ : iz ⊑ jz → iz        ⊑ (jz -, k)
  _os : iz ⊑ jz → (iz -, k) ⊑ (jz -, k)
  oz  :           []        ⊑ []

_⟵_ : K → Bwd K → Type 𝑘
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
