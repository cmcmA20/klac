{-# OPTIONS --safe #-}
module examples.BoolNat where

open import Prelude

open import Data.Bool.Base using (false; true) renaming (Bool to 𝔹)
open import Data.Nat.Base using (ℕ; zero; suc)

Injective : {ℓ : Level} {A B : Type ℓ} → (A → B) → Type ℓ
Injective {_} {A} {B} f = Σ f⁻¹ ꞉ (B → A) , Π x ꞉ A , (f⁻¹ (f x) ≡ x)

_↪_ : Type₀ → Type₀ → Type _
A ↪ B = Σ f ꞉ (A → B) , Injective f

to : ℕ ↪ ℕ
proj₁ to n = n
proj₁ (proj₂ to) n = n
proj₂ (proj₂ to) n = refl

suc-not-zero : {n : ℕ} → (suc n) ≢ 0
suc-not-zero = λ ()

suc-inj : {m n : ℕ} → suc m ≡ suc n → m ≡ n
suc-inj refl = refl

ℕ-is-not-Bool : ℕ ≢ 𝔹
ℕ-is-not-Bool prf with subst (ℕ ↪_) prf to
... | from , to′ , q with from 0 | from 1 | from 2 | q 0 | q 1 | q 2
... | false | false | _     | q₀ | q₁ | _  = suc-not-zero (trans (sym q₁) q₀)
... | false | true  | false | q₀ | _  | q₂ = suc-not-zero (trans (sym q₂) q₀)
... | false | true  | true  | _  | q₁ | q₂ = suc-not-zero (suc-inj (trans (sym q₂) q₁))
... | true  | false | false | _  | q₁ | q₂ = suc-not-zero (suc-inj (trans (sym q₂) q₁))
... | true  | false | true  | q₀ | _  | q₂ = suc-not-zero (trans (sym q₂) q₀)
... | true  | true  | _     | q₀ | q₁ | _  = suc-not-zero (trans (sym q₁) q₀)
