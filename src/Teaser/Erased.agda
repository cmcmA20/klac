{-# OPTIONS --safe --erased-cubical #-}
module Teaser.Erased where

open import Cubical.Foundations.Prelude

record Erased {ℓᵃ} (@0 A : Type ℓᵃ) : Type ℓᵃ where
  constructor [_]
  field
    @0 erased : A

open Erased public

open import Teaser.PropositionalTruncation using (∥_∥₁; ∣_∣₁; squash₁)
  renaming (rec to ∥∥₁-rec; map to ∥∥₁-map; map2 to ∥∥₁-map2)
  public

private variable
  ℓᵃ ℓᵇ : Level
  A : Type ℓᵃ
  B : Type ℓᵇ

∥_∥ᴱ : (@0 A : Type ℓᵃ) → Type ℓᵃ
∥ A ∥ᴱ = Erased ∥ A ∥₁

[_]ᴱ : @0 A → ∥ A ∥ᴱ
[ x ]ᴱ = [ ∣ x ∣₁ ]

map : (@0 f : A → B) (@0 x : ∥ A ∥ᴱ) → ∥ B ∥ᴱ
map f [ x ] = [ ∥∥₁-map f x ]

@0 squashᴱ : isProp ∥ A ∥ᴱ
squashᴱ [ x ] [ y ] = cong (λ a → [ a ]) (squash₁ x y)
