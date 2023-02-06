{-# OPTIONS --safe --erased-cubical #-}
module Teaser.Toset where

open import Cubical.Foundations.Prelude

private variable ℓ ℓ′ : Level

module _ where
  open import Cubical.Data.Sum.Base using (_⊎_; inl; inr)
  open import Cubical.Relation.Binary.Poset using (IsPoset)

  record @0 IsToset {A : Type ℓ} (@0 _≤_ : A → A → Type ℓ′) : Type (ℓ-max ℓ ℓ′) where
    no-eta-equality
    constructor istoset

    field
      @0 isPoset : IsPoset _≤_
      @0 total   : (x y : A) → (x ≤ y) ⊎ (y ≤ x)

    open import Cubical.Relation.Nullary using (¬_)
    total′ : (x y : A) → ¬ (x ≤ y) → y ≤ x
    total′ x y x≰y with total x y
    ... | inr y≤x = y≤x
    ... | inl x≤y = ⊥-rec (x≰y x≤y)
      where open import Cubical.Data.Empty using () renaming (rec to ⊥-rec)

  record TosetStr (ℓ′ : Level) (A : Type ℓ) : Type (ℓ-max ℓ (ℓ-suc ℓ′)) where
    constructor tosetstr
    field
      @0 _≤_     : A → A → Type ℓ′
      @0 isToset : IsToset _≤_

    infixl 7 _≤_
    open module @0 IT = IsToset isToset public
    open module @0 IP = IsPoset isPoset public

open import Teaser.Erased using (Erased; ∥_∥ᴱ; [_]; ∣_∣₁)
TypeWithStrᴱ : {ℓ′ : Level} (ℓ : Level) → (@0 S : Type ℓ → Type ℓ′) → Type (ℓ-max (ℓ-suc ℓ) ℓ′)
TypeWithStrᴱ ℓ S = Σ[ X ∈ Type ℓ ] Erased (S X)

Toset : ∀ ℓ ℓ′ → Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ′))
Toset ℓ ℓ′ = TypeWithStrᴱ ℓ (TosetStr ℓ′)

toset : (A : Type ℓ) (@0 _≤_ : A → A → Type ℓ′) (@0 h : IsToset _≤_) → Toset ℓ ℓ′
toset A _≤_ h = A , [ tosetstr _≤_ h ]
