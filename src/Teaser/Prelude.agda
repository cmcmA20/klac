{-# OPTIONS --safe #-}
module Teaser.Prelude where

open import Cubical.Foundations.Function public
open import Cubical.Foundations.HLevels public
open import Cubical.Foundations.Prelude public
open import Cubical.Data.Nat.Base using (ℕ)

private variable ℓ : Level

record @0 IsOfHLevel (n : ℕ) (A : Type ℓ) : Type ℓ where
  field
    iohl : isOfHLevel n A
open IsOfHLevel ⦃ ... ⦄ public

@0 IsContr : Type ℓ → Type ℓ
IsContr = IsOfHLevel 0

@0 IsProp : Type ℓ → Type ℓ
IsProp = IsOfHLevel 1

@0 IsSet : Type ℓ → Type ℓ
IsSet = IsOfHLevel 2
