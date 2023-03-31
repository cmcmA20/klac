{-# OPTIONS --safe #-}
open import Cubical.Categories.Category.Base
module coDeBruijn.Sliced.Base {ℓ} {ℓ′} (𝒞 : Category ℓ ℓ′) where

open import Cubical.Foundations.Prelude

open Category 𝒞

infixl 15 _⇑_
infixl 14 _↑_
record _⇑_ {ℓ″} (T : ob → Type ℓ″) (d : ob) : Type (ℓ-max ℓ (ℓ-max ℓ′ ℓ″)) where
  constructor _↑_
  field
    { support } : ob
    thing       : T support
    thinning    : Hom[ support , d ]

-- map⇑ : ∀[ P ⇒ Q ] → ∀[ P ⇑_ ⇒ Q ⇑_ ]
-- map⇑ = ?
