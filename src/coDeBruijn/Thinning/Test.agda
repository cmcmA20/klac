module coDeBruijn.Thinning.Test where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat.Base
open import coDeBruijn.Bwd
open import coDeBruijn.Thinning.Base ℕ
open import coDeBruijn.Thinning.Properties ℕ

ex₁ : Bwd ℕ
ex₁ = [] -, 1  -, 2  -, 7  -, 3  -, 7

ex₂ : Bwd ℕ
ex₂ = [] -, 1  -,       7

θ : ex₂ ⊑ ex₁
θ   = oz    os    o′    os    o′    o′

φ : ex₂ ⊑ ex₁
φ   = oz    os    o′    o′    o′    os

boba : restrict θ ≡ restrict φ
boba = refl
