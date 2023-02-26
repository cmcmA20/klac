{-# OPTIONS --safe #-}
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
  ℓᵃ ℓᵇ ℓᶜ : Level
  A : Type ℓᵃ
  B : Type ℓᵇ
  C : Type ℓᶜ

∥_∥ᴱ : (@0 A : Type ℓᵃ) → Type ℓᵃ
∥ A ∥ᴱ = Erased ∥ A ∥₁

[_]ᴱ : @0 A → ∥ A ∥ᴱ
[ x ]ᴱ = [ ∣ x ∣₁ ]

map : (@0 f : A → B) (@0 x : ∥ A ∥ᴱ) → ∥ B ∥ᴱ
map f [ x ] = [ ∥∥₁-map f x ]

map2 : (@0 f : A → B → C) → (@0 x : ∥ A ∥ᴱ) (@0 y : ∥ B ∥ᴱ) → ∥ C ∥ᴱ
map2 f [ x ] [ y ] = [ ∥∥₁-map2 f x y ]

@0 squashᴱ : isProp ∥ A ∥ᴱ
squashᴱ [ x ] [ y ] = cong (λ a → [ a ]) (squash₁ x y)
