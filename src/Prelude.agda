{-# OPTIONS --safe #-}
module Prelude where

open import Agda.Primitive
  using (Level) renaming (lzero to 0ℓ; lsuc to suc-ℓ)
  public

module Universes where

  Type : (ℓ : Level) → Set (suc-ℓ ℓ)
  Type ℓ = Set ℓ
  {-# DISPLAY Set ℓ = Type ℓ #-}

  𝓤 : (ℓ : Level) → Type (suc-ℓ ℓ)
  𝓤 = Type

  Type₀ : Type (suc-ℓ 0ℓ)
  Type₀ = Type 0ℓ
  {-# DISPLAY Set = Type₀ #-}
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

module Typeformers where

  record Σ (A : Type₀) (B : A → Type₀) : Type₀ where
    constructor _,_
    field
      fst : A
      snd : B fst

  open Σ public

  infixr 4 _,_

  syntax Σ A (λ x → b) = Σ x ꞉ A , b

  infix -1 Σ

  _×_ : Type₀ → Type₀ → Type₀
  A × B = Σ x ꞉ A , B

  Pi : (A : Type₀) (B : A → Type₀) → Type₀
  Pi A B = (x : A) → B x

  syntax Pi A (λ x → b) = Π x ꞉ A , b

open Typeformers public
