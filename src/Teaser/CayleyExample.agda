{-# OPTIONS --safe --overlapping-instances --instance-search-depth=2 #-}
module Teaser.CayleyExample where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Erased

open import Cubical.Data.Nat

open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Monoid.Instances.Nat

open import Cubical.Interface.HLevels

private variable
  ℓ : Level

module _ (M : Monoid ℓ) where
  open MonoidStr (M .snd) using () renaming (ε to 1m; _·_ to _*_)

  UnitLeft : Type ℓ
  UnitLeft = ∀ x → 1m * x ≡ x

  UnitRight : Type ℓ
  UnitRight = ∀ x → x * 1m ≡ x

  Associative : Type ℓ
  Associative = ∀ x y z → x * (y * z) ≡ (x * y) * z

module Addition where
  open import Cubical.Algebra.Monoid.Cayley NatMonoid using (𝔐; strictify)

  ℕ′ : Type
  ℕ′ = ⟨ 𝔐 ⟩

  open MonoidStr (str 𝔐) using () renaming (_·_ to _✦_) public

  private
    @0 watchThis₁ : UnitLeft NatMonoid
    watchThis₁ = strictify UnitLeft λ _ → refl

    @0 watchThis₂ : UnitRight NatMonoid
    watchThis₂ = strictify UnitRight λ _ → refl

    @0 watchThis₃ : Associative NatMonoid
    watchThis₃ = strictify Associative λ _ _ _ → refl

open Addition

module List (A : Type ℓ) ⦃ _ : IsSet A ⦄ where

  open import Cubical.Data.List
  open import Cubical.Data.List.Instances

  ListMonoid : Monoid _
  ListMonoid = makeMonoid {M = List A} [] _++_ (λ xs _ _ → sym (++-assoc xs _ _)) ++-unit-r (λ _ → refl)

  open import Cubical.Algebra.Monoid.Cayley ListMonoid
  DiffList : Type ℓ
  DiffList = ⟨ 𝔐 ⟩
