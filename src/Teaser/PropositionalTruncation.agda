{-# OPTIONS --safe --erased-cubical #-}
module Teaser.PropositionalTruncation where

open import Cubical.Foundations.Prelude

data ∥_∥₁ {ℓᵃ} (A : Type ℓᵃ) : Type ℓᵃ where
  ∣_∣₁       : A → ∥ A ∥₁
  @0 squash₁ : (x y : ∥ A ∥₁) → x ≡ y

private variable
  ℓᵃ ℓᵇ ℓᶜ : Level
  A : Type ℓᵃ
  B : Type ℓᵇ
  C : Type ℓᶜ

rec : (@0 Bprop : isProp B) → (A → B) → ∥ A ∥₁ → B
rec Bprop f ∣ x ∣₁ = f x
rec Bprop f (squash₁ x y i) = Bprop (rec Bprop f x) (rec Bprop f y) i

map : (A → B) → (∥ A ∥₁ → ∥ B ∥₁)
map f = rec squash₁ (∣_∣₁ ∘ f)
  where open import Cubical.Foundations.Function

open import Cubical.Foundations.HLevels using (isPropΠ)
map2 : (A → B → C) → (∥ A ∥₁ → ∥ B ∥₁ → ∥ C ∥₁)
map2 f = rec (isPropΠ (λ _ → squash₁)) (map ∘ f)
  where open import Cubical.Foundations.Function
