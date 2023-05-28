{-# OPTIONS --safe --overlapping-instances --instance-search-depth=3 #-}
module Teaser.Test where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Nat
open import Cubical.Data.List.Base
open import Cubical.Data.Bool

open import Cubical.HITs.Int

open import Cubical.Instances.DecEq
open import Cubical.Instances.HLevels


module _ {A : Type} {a : A} ⦃ _ : IsSet A ⦄ where

  foo : ⦃ IsSet (List A) ⦄ → A
  foo = a

  bar : A
  bar = foo

foo′ : (xs ys : List ℕ) → ⦃ IsGroupoid (xs ≡ ys) ⦄ → ℕ
foo′ xs ys with xs ≟ ys
... | yes _ = 1
... | no  _ = 0

-- baz : ℕ
-- baz = foo′ [] []



private variable
  ℓ : Level
  A : Type ℓ

test : ℤ → ℤ → Bool
test m n with  m ≟ n
... | no  m≢n = false
... | yes m≢  = true

succEquiv : ℤ ≃ ℤ
succEquiv = isoToEquiv (iso succ pred succPred predSucc)
  where
  succPred : ∀ m → succ (pred m) ≡ m
  succPred (neg x) = {!!}
  succPred (pos x) = {!!}
  succPred (0₋≡0₊ i) = {!!}
  -- succPred (neg _)       = refl
  -- succPred (pos zero)    = 0₋≡0₊
  -- succPred (pos (suc _)) = refl
  -- succPred (0₋≡0₊ i) j = 0₋≡0₊ (i ∧ j)

  predSucc : ∀ m → pred (succ m) ≡ m
  predSucc (neg zero)    = sym 0₋≡0₊
  predSucc (neg (suc _)) = refl
  predSucc (pos _)       = refl
  predSucc (0₋≡0₊ i) j = sym 0₋≡0₊ (~ i ∧ j)

succEquiv′ : ℤ ≃ ℤ
succEquiv′ = isoToEquiv (iso succ pred succPred predSucc)
  where
  succPred : ∀ m → succ (pred m) ≡ m
  succPred = elim-prop (λ _ → refl) (λ { zero → 0₋≡0₊ ; (suc _) → refl })

  predSucc : ∀ m → pred (succ m) ≡ m
  predSucc = elim-prop (λ { zero → sym 0₋≡0₊ ; (suc _) → refl }) (λ _ → refl)
