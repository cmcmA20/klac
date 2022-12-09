{-# OPTIONS --safe #-}
module Prelude where

open import Agda.Primitive
  using (Level; _⊔_) renaming (lzero to 0ℓ; lsuc to suc-ℓ)
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

private
  variable
    ℓ ℓ₁ ℓ₂ : Level

module Typeformers where

  record Σ (A : Type ℓ₁) (B : A → Type ℓ₂) : Type (ℓ₁ ⊔ ℓ₂) where
    constructor _,_
    field
      fst : A
      snd : B fst

  open Σ public

  infixr 4 _,_

  syntax Σ A (λ x → b) = Σ x ꞉ A , b

  infix -1 Σ

  _×_ : Type ℓ₁ → Type ℓ₂ → Type _
  A × B = Σ x ꞉ A , B

  Pi : (A : Type ℓ₁) (B : A → Type ℓ₂) → Type _
  Pi A B = (x : A) → B x

  syntax Pi A (λ x → b) = Π x ꞉ A , b

open Typeformers public


module Equality where

  private
    variable
      A B : Type ℓ

  data _≡_ {A : Type ℓ} : A → A → Type ℓ where
    refl : (x : A) → x ≡ x
  infix 0 _≡_
  {-# BUILTIN EQUALITY _≡_ #-}

  cong : (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
  cong f (refl _) = refl (f _)

  sym : {x y : A} → x ≡ y → y ≡ x
  sym (refl _) = refl _

  trans : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  trans p (refl _) = p

  subst : {A : Type ℓ₁} {B : A → Type ℓ₂} {x y : A} → x ≡ y → B x → B y
  subst (refl _) p = p

  module ≡-Reasoning {A : Set ℓ} where

    infix  3 _∎
    infixr 2 _≡⟨⟩_ step-≡ step-≡˘
    infix  1 begin_

    begin_ : {x y : A} → x ≡ y → x ≡ y
    begin_ x≡y = x≡y

    _≡⟨⟩_ : (x : A) → {y : A} → x ≡ y → x ≡ y
    _ ≡⟨⟩ x≡y = x≡y

    step-≡ : (x : A) {y z : A} → y ≡ z → x ≡ y → x ≡ z
    step-≡ _ y≡z x≡y = trans x≡y y≡z

    step-≡˘ : (x : A) {y z : A} → y ≡ z → y ≡ x → x ≡ z
    step-≡˘ _ y≡z y≡x = trans (sym y≡x) y≡z

    _∎ : (x : A) → x ≡ x
    _∎ _ = refl _

    syntax step-≡  x y≡z x≡y = x ≡⟨  x≡y ⟩ y≡z
    syntax step-≡˘ x y≡z y≡x = x ≡˘⟨ y≡x ⟩ y≡z

open Equality public
