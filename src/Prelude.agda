{-# OPTIONS --safe #-}
module Prelude where

open import Agda.Primitive
  using (Level; _⊔_) renaming (lzero to 0ℓ; lsuc to suc-ℓ)
  public

module Universes where

  Type : (ℓ : Level) → Set (suc-ℓ ℓ)
  Type ℓ = Set ℓ

  𝓤 : (ℓ : Level) → Type (suc-ℓ ℓ)
  𝓤 = Type

  Type₀ : Type (suc-ℓ 0ℓ)
  Type₀ = Type 0ℓ
  𝓤₀ : Type (suc-ℓ 0ℓ)
  𝓤₀ = Type₀

  Type₁ : Type (suc-ℓ (suc-ℓ 0ℓ))
  Type₁ = Type (suc-ℓ 0ℓ)
  𝓤₁ : Type (suc-ℓ (suc-ℓ 0ℓ))
  𝓤₁ = Type (suc-ℓ 0ℓ)

  Type₂ : Type (suc-ℓ (suc-ℓ (suc-ℓ 0ℓ)))
  Type₂ = Type (suc-ℓ (suc-ℓ 0ℓ))
  𝓤₂ : Type (suc-ℓ (suc-ℓ (suc-ℓ 0ℓ)))
  𝓤₂ = Type (suc-ℓ (suc-ℓ 0ℓ))

open Universes public

variable
  ℓ ℓ₀ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

open import Data.Product public

fst = proj₁
snd = proj₂

Σ-syntax′ = Σ-syntax

syntax Σ-syntax′ A (λ x → B) = Σ x ꞉ A , B

Π-syntax : (A : Set ℓ₁) → (A → Set ℓ₂) → Set (ℓ₁ ⊔ ℓ₂)
Π-syntax A B = (x : A) → B x

Π-syntax′ = Π-syntax

syntax Π-syntax  A (λ x → B) = Π[ x ∈ A ] B
syntax Π-syntax′ A (λ x → B) = Π x ꞉ A , B

open import Relation.Binary.PropositionalEquality public

module HLevels where

  isProp : Type ℓ → Type ℓ 
  isProp A = (x y : A) → x ≡ y

  isContr : Type ℓ → Type ℓ
  isContr A = A × isProp A

open HLevels public
