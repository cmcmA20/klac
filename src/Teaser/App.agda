{-# OPTIONS --guardedness #-}
module Teaser.App where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Instances
open import Cubical.Data.Sum
open import Cubical.Data.List

open import Cubical.HITs.PropositionalTruncation as ∥∥₁

open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary.Poset
open import Cubical.Relation.Binary.Toset

open import Cubical.Interface.Show

open import Cubical.IO

open IsPoset
open IsToset
open Show ⦃ ... ⦄

_≤″_ : ℕ → ℕ → Type₀
m ≤″ n = ∥ m ≤ n ∥₁

_≤?_ : (x y : ℕ) → Dec (x ≤″ y)
x ≤? y = Dec∥∥ (≤Dec x y)

ℕ-is-toset : IsToset _≤″_
is-prop-valued (isPoset ℕ-is-toset) _ _ = squash₁
is-refl (isPoset ℕ-is-toset) _          = ∣ ≤-refl ∣₁
is-trans (isPoset ℕ-is-toset) _ _ _     = ∥∥₁.map2 ≤-trans
is-antisym (isPoset ℕ-is-toset) _ _ p q = ∥∥₁.rec (isSetℕ _ _) (λ x → x) (∥∥₁.map2 ≤-antisym p q)
total ℕ-is-toset x y with x ≟ y
... | lt (k , p) = inl ∣ suc k , sym (+-suc _ _) ∙ p ∣₁
... | eq p       = inl ∣ 0 , p ∣₁
... | gt (k , p) = inr ∣ suc k , sym (+-suc _ _) ∙ p ∣₁

ℕ-toset : Toset ℓ-zero ℓ-zero
ℕ-toset = toset ℕ _≤″_ ℕ-is-toset

open import Teaser.Sorting ℕ-toset
open import Teaser.Permutation using (List→List↭)
open Insertion using (insertSort)

main : Main
main = run do
  s ← getLine
  let
    xs = 4 ∷ 2 ∷ 0 ∷ 1 ∷ 3 ∷ 3 ∷ 7 ∷ []
    result = insertSort _≤?_ (List→List↭ xs)
  printLn $ result .fst
