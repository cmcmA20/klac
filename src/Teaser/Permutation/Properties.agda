{-# OPTIONS --safe #-}
module Teaser.Permutation.Properties where

open import Cubical.Relation.Nullary.Base using (¬_)

open import Teaser.Prelude
open import Teaser.Permutation.Base

private variable
  ℓᵃ : Level
  A  : Type ℓᵃ

@0 ¬[]≡∷ : {x : A} {xs : List↭ A} → ¬ [] ≡ x ∷ xs
¬[]≡∷ p = true≢false (cong discrim-empty p)
  where
  open import Cubical.Data.Bool using (Bool; false; true; isSetBool; true≢false)
  discrim-empty : List↭ A → Bool
  discrim-empty = rec-set true (λ _ _ → false) (λ _ _ _ → refl) isSetBool
