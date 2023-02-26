{-# OPTIONS --safe #-}
module Teaser.Permutation.Base where

open import Teaser.Prelude

private variable
  ℓᵃ ℓᵇ : Level
  A : Type ℓᵃ
  B : Type ℓᵇ

infixr 5 _∷_
data List↭ (A : Type ℓᵃ) : Type ℓᵃ where
  []  : List↭ A
  _∷_ : A → List↭ A → List↭ A
  @0 swap  : (x₁ x₂ : A) (xs : List↭ A) → x₁ ∷ x₂ ∷ xs ≡ x₂ ∷ x₁ ∷ xs
  @0 trunc : isSet (List↭ A)

module _ {B : List↭ A → Type ℓᵇ}
         ([]* : B [])
         (_∷*_ : (a : A) {as : List↭ A} → B as → B (a ∷ as))
         (@0 swap* : (x₁ x₂ : A) {xs : List↭ A} (b : B xs) → PathP (λ i → B (swap x₁ x₂ xs i)) (x₁ ∷* (x₂ ∷* b)) (x₂ ∷* (x₁ ∷* b)))
         (@0 trunc* : (xs : List↭ A) → isSet (B xs)) where
  elim-set : (xs : List↭ A) → B xs
  elim-set []       = []*
  elim-set (x ∷ xs) = x ∷* elim-set xs
  elim-set (swap x₁ x₂ xs i) = swap* x₁ x₂ (elim-set xs) i
  elim-set (trunc xs xs′ p q i j) =
    isOfHLevel→isOfHLevelDep 2 trunc* (elim-set xs) (elim-set xs′)
                                      (cong elim-set p) (cong elim-set q)
                                      (trunc xs xs′ p q) i j


module _ {B : Type ℓᵇ}
         ([]* : B)
         (_∷*_ : (a : A) → B → B)
         (@0 swap* : (x₁ x₂ : A) → (b : B) → (x₁ ∷* (x₂ ∷* b)) ≡ (x₂ ∷* (x₁ ∷* b)))
         (@0 B-Set : isSet B) where
  rec-set : List↭ A → B
  rec-set = elim-set []* (λ a → a ∷*_) (λ x₁ x₂ → swap* x₁ x₂) (λ _ → B-Set)


open import Cubical.Data.List.Base using (List; []; _∷_)
List→List↭ : List A → List↭ A
List→List↭ []       = []
List→List↭ (x ∷ xs) = x ∷ List→List↭ xs
