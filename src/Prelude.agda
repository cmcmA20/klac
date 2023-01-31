{-# OPTIONS --safe #-}
module Prelude where

open import Agda.Primitive
  using (Level; _⊔_) renaming (lzero to 0ℓ; lsuc to suc-ℓ; Set to Type)
  public
open import Agda.Primitive using () renaming (Set to 𝓤)
  public

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

it : {A : Type ℓ} → ⦃ x : A ⦄ → A
it ⦃ x ⦄ = x

Σ-≡ : {A : Type₀} {B : A → Type₀} {P Q : Σ a ꞉ A , B a} →
      (basePath : fst P ≡ fst Q) → (liftedPath : subst B basePath (snd P) ≡ snd Q) →
      P ≡ Q
Σ-≡ refl refl = refl
