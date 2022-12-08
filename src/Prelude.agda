{-# OPTIONS --no-load-primitives #-}
module Prelude where

module Universes where

  infixl 6 _⊔_

  {-# BUILTIN TYPE Type #-}
  {-# BUILTIN PROP Prop #-}
  {-# BUILTIN SETOMEGA Typeω #-}
  {-# BUILTIN STRICTSET      SSet  #-}
  {-# BUILTIN STRICTSETOMEGA SSetω #-}

  postulate
    Level : Type

  {-# BUILTIN LEVEL Level #-}

  postulate
    0ℓ    : Level
    suc-ℓ : (ℓ : Level) → Level
    _⊔_   : (ℓ₁ ℓ₂ : Level) → Level

  {-# BUILTIN LEVELZERO 0ℓ #-}
  {-# BUILTIN LEVELSUC  suc-ℓ  #-}
  {-# BUILTIN LEVELMAX  _⊔_   #-}

  𝓤₀ = Type

  𝓤₁ = Type (suc-ℓ 0ℓ)

  𝓤₂ = Type (suc-ℓ (suc-ℓ 0ℓ))

open Universes public

module Typeformers where

  record Σ (A : Type) (B : A → Type) : Type where
    constructor _,_
    field
      fst : A
      snd : B fst

  open Σ public

  infixr 4 _,_

  syntax Σ A (λ x → b) = Σ x ꞉ A , b

  infix -1 Σ

  _×_ : Type → Type → Type
  A × B = Σ x ꞉ A , B

  Pi : (A : Type) (B : A → Type) → Type
  Pi A B = (x : A) → B x

  syntax Pi A (λ x → b) = Π x ꞉ A , b

open Typeformers public
