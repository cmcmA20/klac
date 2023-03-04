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

open import Cubical.Algebra.Monoid using (Monoid; IsMonoid; MonoidStr; makeIsMonoid)
module @0 Test {A : Type ℓᵃ} ⦃ A-set : IsSet A ⦄ (A-mon-str : MonoidStr A) where
  open MonoidStr A-mon-str

  ε′ : A
  ε′ = MonoidStr.ε A-mon-str

  _·′_ : A → A → A
  _·′_ = MonoidStr._·_ A-mon-str

  free-monoid-is-really-free : FreeMonoid A → A
  free-monoid-is-really-free = rec-set ε′ (_·′ ε′) _·′_ ·IdL ·IdR (λ _ _ _ → sym (·Assoc _ _ _)) (A-set .iohl)

module @0 Test₂ where
  open Test
  open import Cubical.Data.Nat using (ℕ; isSetℕ; ·-identityʳ; ·-identityˡ; ·-assoc) renaming (_·_ to _*_)
  open import Cubical.Algebra.Monoid.Instances.Nat

  instance
    IsSetℕ : IsSet ℕ
    IsOfHLevel.iohl IsSetℕ = isSetℕ

  testExpression : FreeMonoid ℕ
  testExpression = ε · ([ 2 ] · ([ 3 ] · ([ 4 ] · ε)))

  result₁ : ℕ
  result₁ = free-monoid-is-really-free (NatMonoid .snd) testExpression

  _ : result₁ ≡ 9
  _ = refl

  NatMonoidMult : Monoid ℓ-zero
  fst NatMonoidMult = ℕ
  MonoidStr.ε (snd NatMonoidMult) = 1
  MonoidStr._·_ (snd NatMonoidMult) = _*_
  MonoidStr.isMonoid (snd NatMonoidMult) = makeIsMonoid isSetℕ ·-assoc ·-identityʳ ·-identityˡ

  result₂ : ℕ
  result₂ = free-monoid-is-really-free (NatMonoidMult .snd) testExpression

  _ : result₂ ≡ 24
  _ = refl
