module Teaser.InfNat.Properties where

open import Cubical.Foundations.Prelude
open import Teaser.InfNat.Base

+Assoc : ∀ m n k → m + (n + k) ≡ (m + n) + k
+Assoc m n k = ⟪ +Assoc″ ⟫⇓ m
  module +Assoc′ where
  +Assoc″ : ℕ∞⇒ (λ m → m + (n + k) ≡ (m + n) + k)
  ⟪ +Assoc″ ⟫zero    = refl
  ⟪ +Assoc″ ⟫suc _ p = cong suc p
  ⟪ +Assoc″ ⟫∞       = refl
  ⟪ +Assoc″ ⟫prop _  = trunc _ _

UnitR : ∀ m → m + zero ≡ m
UnitR = ⟪ UnitR″ ⟫⇓
  module UnitR′ where
  UnitR″ : ℕ∞⇒ (λ m → m + zero ≡ m) 
  ⟪ UnitR″ ⟫zero    = refl
  ⟪ UnitR″ ⟫suc _ p = cong suc p
  ⟪ UnitR″ ⟫∞       = refl
  ⟪ UnitR″ ⟫prop _  = trunc _ _

@0 InfR : ∀ m → m + ∞ ≡ ∞
InfR = ⟪ InfR″ ⟫⇓
  module InfR′ where
  InfR″ : ℕ∞⇒ (λ m → m + ∞ ≡ ∞)
  ⟪ InfR″ ⟫zero = refl
  ⟪ InfR″ ⟫suc _ p = cong suc p ∙ inf
  ⟪ InfR″ ⟫∞ = refl
  ⟪ InfR″ ⟫prop _ = trunc _ _

@0 +sucComm : ∀ m n → suc (m + n) ≡ m + suc n
+sucComm m n = ⟪ +sucComm″ ⟫⇓ m
  module +sucComm′ where
  +sucComm″ : ℕ∞⇒ λ m → suc m + n ≡ m + suc n
  ⟪ +sucComm″ ⟫zero = refl
  ⟪ +sucComm″ ⟫suc m p = cong suc p
  ⟪ +sucComm″ ⟫∞ = inf
  ⟪ +sucComm″ ⟫prop _ = trunc _ _

-- @0 +Comm : ∀ m n → m + n ≡ n + m
-- +Comm m n = ⟪ +Comm″ ⟫⇓ m
--   module +Comm′ where
--   +Comm″ : ℕ∞⇒ (λ m → m + n ≡ n + m)
--   ⟪ +Comm″ ⟫zero = sym (UnitR _)
--   ⟪ +Comm″ ⟫suc m p = cong suc p ∙ +sucComm n m
--   ⟪ +Comm″ ⟫∞ = sym inf ∙ {!!}
--   ⟪ +Comm″ ⟫prop _ = trunc _ _
