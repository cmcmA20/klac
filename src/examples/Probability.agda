-- {-# OPTIONS --safe #-}
{-# OPTIONS --allow-unsolved-metas #-}
module examples.Probability where

open import Algebra using (Monoid)
import Algebra.Morphism as Morphism
open import Data.Integer using (ℤ; +_; _◃_; +<+) renaming (_+_ to _⊕_; _*_ to _⋆_)
import Data.Integer as ℤ
open import Data.Integer.Properties using (*-1-monoid; pos-+) renaming (*-identityʳ to *-identityʳ-ℤ)
import Data.Integer.Properties as ℤₚ
open import Agda.Builtin.Nat using (div-helper)
open import Agda.Builtin.Bool
open import Data.Sign.Base using () renaming (+ to +ˢ)
open import Data.Nat using (ℕ; suc; NonZero; z≤n; s≤s) renaming (_+_ to _✧_; _*_ to _✦_; _/_ to _／_)
open import Data.Nat.GCD
open import Data.Nat.Properties using () renaming (*-identityʳ to *-identityʳ-ℕ; +-comm to +-comm-ℕ)
open import Data.Nat.Coprimality using (Coprime; 1-coprimeTo) renaming (sym to sym′)
open import Data.Product using (Σ; _,_)
open import Data.Rational
  using (↥_; ↧_; ℚ; mkℚ; fromℚᵘ; mkℚ+; 0ℚ; 1ℚ; _<_; *<*; Positive; normalize; positive; _+_; _*_; _/_; 1/_)
  renaming (NonZero to NonZero-ℚ; NonNegative to NonNegative-ℚ)
import Data.Rational as ℚ
open import Data.Rational.Properties
open import Data.Vec using (Vec; []; _∷_)
open import Effect.Functor using (RawFunctor)
open import Function.Base using (_$_)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; cong₂; subst; module ≡-Reasoning) renaming (sym to symm)
open import Data.Empty

private
  variable
    ℓ ℓ₁ ℓ₂ : Level
    A B : Set ℓ
    n : ℕ
    r r₁ r₂ : ℚ

data D (A : Set ℓ) : ℚ → Set ℓ where
  []    : D A 0ℚ
  _~_∷_ : {r s : ℚ} → A → (w : ℚ) ⦃ wp : Positive w ⦄ ⦃ p : w + r ≡ s ⦄ → D A r → D A s

map : {r : ℚ} → (f : A → B) → D A r → D B r
map _ []           = []
map f (x ~ w ∷ xs) = f x ~ w ∷ map f xs

functor : RawFunctor {ℓ} (λ T → D T r)
functor = record { _<$>_ = map }

posProd : {x y : ℚ} → ⦃ Positive x ⦄ → ⦃ Positive y ⦄ → Positive (x * y)
posProd {x = x} {y = y} = positive (subst (_< x * y) (*-zeroˡ y) (*-monoˡ-<-pos y (positive⁻¹ x)))

rescale : (s : ℚ) → ⦃ Positive s ⦄ → D A r → D A (s * r)
rescale s []           = subst (D _) (symm (*-zeroʳ s)) []
rescale s {{ps}} (_~_∷_ x w {{_}} {{p}} xs) = 
  subst (λ j → D _ (s * j)) p $
  subst (D _) (symm (*-distribˡ-+ s w _)) (_~_∷_ x (s * w) {{posProd {s} {w}}} (rescale s xs))

_++_ : D A r₁ → D A r₂ → D A (r₁ + r₂)
[]           ++ ys = subst (D _) (symm (identityˡ _)) ys
  where open Monoid +-0-monoid
_++_ {_} {_} {r₁} {r₂} (_~_∷_ {r} x w {{_}} {{p}} xs) ys =
  subst (λ j → D _ (j + r₂)) p $
  subst (D _) (symm (assoc w r r₂)) (x ~ w ∷ (xs ++ ys))
  where open Monoid +-0-monoid

-- replicate : (n : ℕ) → D A r → D A (⇧ n * r)
-- replicate {_} {_} {r} 0 _ = subst (D _) (symm (*-zeroˡ r)) []
-- replicate (suc n) xs = subst (D _) {!!} (xs ++ replicate n xs)

-- finitely supported probability measure on `A`
𝒟 : Set ℓ → Set ℓ
𝒟 A = D A 1ℚ

concat : D (D A r₁) r₂ → D A (r₂ * r₁)
concat {_} {_} {r₁} [] = subst (D _) (symm (*-zeroˡ r₁)) []
concat {_} {_} {r₁} (_~_∷_ {r} xs w {{_}} {{p}} xxs) =
  subst (λ j → D _ (j * r₁)) p $
  subst (D _) (symm (*-distribʳ-+ r₁ w r)) (rescale w xs ++ concat xxs)

E : 𝒟 (𝒟 A) → 𝒟 A
E = concat

-- Dirac's delta
δ : A → 𝒟 A
δ x = x ~ 1ℚ ∷ []

⇧_ : ℕ → ℚ
⇧ n = mkℚ+ n 1 (sym′ (1-coprimeTo _))

-- mad shit starts here

module Arith where
  open import Data.Rational.Unnormalised using (ℚᵘ; mkℚᵘ; 0ℚᵘ; 1ℚᵘ) renaming (_+_ to _+ᵘ_)
  open import Data.Rational.Unnormalised.Properties using () renaming (+-0-monoid to +-0-monoidᵘ)

  biba : {k : ℕ} → +ˢ ◃ k ≡ + k
  biba {0    } = refl
  biba {suc k} = refl

  module ℕtoℚᵘ = Morphism.Definitions ℕ ℚᵘ _≡_

  ⇧ᵘ_ : ℕ → ℚᵘ
  ⇧ᵘ n = mkℚᵘ (+ n) 0

  pluᵘ : ℕtoℚᵘ.Homomorphic₂ ⇧ᵘ_ _✧_ _+ᵘ_
  pluᵘ x y = cong (λ j → mkℚᵘ j 0) $
    begin
      + (x ✧ y)
    ≡⟨⟩
      + x ⊕ + y
    ≡⟨ cong (λ j → j ⊕ (+ y)) (symm biba) ⟩
      (+ˢ ◃ x) ⊕ (+ y)
    ≡⟨ cong (λ j → (+ˢ ◃ x) ⊕ j) (symm biba) ⟩
      (+ˢ ◃ x) ⊕ (+ˢ ◃ y)
    ≡⟨ cong (λ j → (+ˢ ◃ j) ⊕ (+ˢ ◃ y)) (symm (*-identityʳ-ℕ x)) ⟩
      (+ˢ ◃ x ✦ 1) ⊕ (+ˢ ◃ y)
    ≡⟨ cong (λ j → (+ˢ ◃ x ✦ 1) ⊕ (+ˢ ◃ j)) (symm (*-identityʳ-ℕ _)) ⟩
      (+ˢ ◃ x ✦ 1) ⊕ (+ˢ ◃ y ✦ 1)
    ∎ where open ≡-Reasoning

  module ℕtoℚ = Morphism.Definitions ℕ ℚ _≡_

  module ℚᵘtoℚ = Morphism.Definitions ℚᵘ ℚ _≡_

  plu : ℕtoℚ.Homomorphic₂ ⇧_ _✧_ _+_
  plu x y with x ✧ y Data.Nat.≡ᵇ 1 in eqb
  ... | false = {!!}
  ... | true =
    begin
      mkℚ (+ (x ✧ y)) 0 _
    ≡⟨⟩
      mkℚ+ (x ✧ y) 1 (sym′ (1-coprimeTo _))
    ≡⟨ mkℚ+-cong {{_}} {{_}} {!!} {!!} ⟩
      normalize (x ✧ y) 1
    ≡⟨⟩
      ((+ x) ⊕ (+ y)) / 1
    ≡⟨ cong (λ j → (j ⊕ (+ y)) / 1) (symm (biba {x})) ⟩
      ((+ˢ ◃ x) ⊕ (+ y)) / 1
    ≡⟨ cong (λ j → ((+ˢ ◃ x) ⊕ j) / 1) (symm biba) ⟩
      ((+ˢ ◃ x) ⊕ (+ˢ ◃ y)) / 1
    ≡⟨ cong (λ j → ((+ˢ ◃ j) ⊕ (+ˢ ◃ y)) / 1) {x} {x ✦ 1} (symm (*-identityʳ-ℕ x)) ⟩
      ((+ˢ ◃ x ✦ 1) ⊕ (+ˢ ◃ y)) / 1
    ≡⟨ cong (λ j → ((+ˢ ◃ x ✦ 1) ⊕ j) / 1) (cong (λ k → +ˢ ◃ k) (symm (*-identityʳ-ℕ y))) ⟩
      ((+ˢ ◃ x ✦ 1) ⊕ (+ˢ ◃ y ✦ 1)) / 1
    ∎ where open ≡-Reasoning
--  plu x y = let z = toℚᵘ-isMonoidHomomorphism-+ in {!!}

open Arith

U : (xs : Vec A n) → D A (⇧ n)
U []                       = []
U {_} {_} {suc n} (x ∷ xs) = subst (D _) (symm (plu 1 n)) (δ x ++ U xs)

-- finite uniform distribution
𝒰 : (xs : Vec A (suc n)) → 𝒟 A
𝒰 {_} {_} {n} xs = subst (D _) (*-inverseˡ (⇧ (suc n))) $ rescale (1/_ (⇧ suc n)) (U xs)
