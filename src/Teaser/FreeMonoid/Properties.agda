{-# OPTIONS --safe #-}
module Teaser.FreeMonoid.Properties where

open import Teaser.Prelude
open import Teaser.FreeMonoid.Base

private variable
  ℓᵃ ℓᵇ : Level
  A : Type ℓᵃ
  B : Type ℓᵇ

module _ ⦃ @0 A-set : IsSet A ⦄ where
  open import Cubical.Data.List.Base using (List) renaming ([] to []′; _∷_ to _∷′_; _++_ to _++′_)

  @0 distrib-over-++ : (xs ys : List A) → List→FreeMonoid (xs ++′ ys) ≡ List→FreeMonoid xs · List→FreeMonoid ys
  distrib-over-++ []′      _ = sym (leftId _)
  distrib-over-++ (_ ∷′ _) _ = cong ([ _ ] ·_) (distrib-over-++ _ _) ∙ sym (assoc _ _ _)

  @0 observe : FreeMonoid A ≡ List A
  observe = ua (isoToEquiv same)
    where
    open import Cubical.Foundations.Univalence using (ua)
      
    fun∘inv : (xs : List A) → FreeMonoid→List (List→FreeMonoid xs) ≡ xs
    fun∘inv []′       = refl
    fun∘inv (x ∷′ xs) = cong (x ∷′_) (fun∘inv xs)

    inv∘fun : (xs : FreeMonoid A) → List→FreeMonoid (FreeMonoid→List xs) ≡ xs
    inv∘fun = elim-prop refl (λ _ → rightId _) (λ p q → distrib-over-++ _ _ ∙ cong₂ _·_ p q) (trunc _ _) 

    open import Cubical.Foundations.Isomorphism using (isoToEquiv; Iso)
    open Iso
    same : Iso (FreeMonoid A) (List A)
    fun same = FreeMonoid→List
    inv same = List→FreeMonoid
    rightInv same = fun∘inv
    leftInv same = inv∘fun
