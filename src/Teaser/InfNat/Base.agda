module Teaser.InfNat.Base where

open import Teaser.Prelude

data ℕ∞ : Type where
  zero : ℕ∞
  suc  : ℕ∞ → ℕ∞
  ∞    : ℕ∞
  @0 inf  : suc ∞ ≡ ∞
  @0 trunc : isSet ℕ∞

private variable
  ℓᵇ : Level
  B : Type ℓᵇ

-- module _ {B : ℕ∞ → Type ℓᵇ}
--          (zero* : B zero)
--          (suc*  : {m : ℕ∞} → B m → B (suc m))
--          (∞*    : B ∞) where

--   module _ (@0 inf* : PathP (λ i → B (inf i)) (suc* ∞*) ∞*)
--            (@0 trunc* : (m : ℕ∞) → isSet (B m)) where
--     elim-set : (n : ℕ∞) → B n
--     elim-set zero    = zero*
--     elim-set (suc n) = suc* (elim-set n)
--     elim-set ∞       = ∞*
--     elim-set (inf i) = inf* i
--     elim-set (trunc k k′ p q i j) = isOfHLevel→isOfHLevelDep 2 trunc* (elim-set k) (elim-set k′) (cong elim-set p) (cong elim-set q) (trunc k k′ p q) i j

--   module _ (@0 B-prop : {m : ℕ∞} → isProp (B m)) where
--     elim-prop : (n : ℕ∞) → B n
--     elim-prop = elim-set (toPathP (B-prop _ _)) (λ _ → isProp→isSet B-prop)

-- module _ (zero* : B)
--          (suc*  : B → B)
--          (∞*    : B)
--          (@0 inf* : suc* ∞* ≡ ∞*)
--          (@0 B-set : isSet B) where
--   rec-set : ℕ∞ → B
--   rec-set = elim-set zero* suc* ∞* inf* (λ _ → B-set)

record ℕ∞⟶_ (B : ℕ∞ → Type ℓᵇ) : Type ℓᵇ where
  constructor elim-set
  field
    ⟨_⟩zero : B zero
    ⟨_⟩suc  : (m : ℕ∞) → B m → B (suc m)
    ⟨_⟩∞    : B ∞
    @0 ⟨_⟩inf : PathP (λ i → B (inf i)) (⟨_⟩suc _ ⟨_⟩∞) ⟨_⟩∞
    @0 ⟨_⟩set : (m : ℕ∞) → isSet (B m)

  ⟨_⟩⇓ : (m : ℕ∞) → B m
  ⟨ zero  ⟩⇓ = ⟨_⟩zero
  ⟨ suc m ⟩⇓ = ⟨_⟩suc m ⟨ m ⟩⇓
  ⟨ ∞     ⟩⇓ = ⟨_⟩∞
  ⟨ inf i ⟩⇓ = ⟨_⟩inf i 
  ⟨ trunc k k′ p q i j ⟩⇓ =
    isOfHLevel→isOfHLevelDep 2 ⟨_⟩set ⟨ k ⟩⇓ ⟨ k′ ⟩⇓ (cong ⟨_⟩⇓ p) (cong ⟨_⟩⇓ q) (trunc k k′ p q) i j
    
open ℕ∞⟶_ public
elim-set-syntax : (ℕ∞ → Type ℓᵇ) → Type ℓᵇ
elim-set-syntax = ℕ∞⟶_
syntax elim-set-syntax (λ m → Bm) = ⟨ m ∈ ℕ∞ ⟶ Bm ⟩

record ℕ∞⇒_ (B : ℕ∞ → Type ℓᵇ) : Type ℓᵇ where
  constructor elim-prop
  field
    ⟪_⟫zero : B zero
    ⟪_⟫suc  : (m : ℕ∞) → B m → B (suc m)
    ⟪_⟫∞    : B ∞
    @0 ⟪_⟫prop : (m : ℕ∞) → isProp (B m)

  ⟪_⟫⇑ = elim-set ⟪_⟫zero ⟪_⟫suc ⟪_⟫∞ (toPathP (⟪_⟫prop _ _ _)) (λ m → isProp→isSet (⟪_⟫prop m))
  ⟪_⟫⇓ = ⟨ ⟪_⟫⇑ ⟩⇓ 

open ℕ∞⇒_ public
elim-prop-syntax : (ℕ∞ → Type ℓᵇ) → Type ℓᵇ
elim-prop-syntax = ℕ∞⇒_
syntax elim-prop-syntax (λ m → Bm) = ⟪ m ∈ ℕ∞ ⇒ Bm ⟫

record ℕ∞↦_ (B : Type ℓᵇ) : Type ℓᵇ where
  constructor rec-set
  field
    <_>zero : B
    <_>suc  : B → B
    <_>∞    : B
    @0 <_>inf : <_>suc <_>∞ ≡ <_>∞
    @0 <_>set : isSet B

  <_>⇑ = elim-set <_>zero (λ _ → <_>suc) <_>∞ <_>inf (λ _ → <_>set)
  <_>⇓ = ⟨ <_>⇑ ⟩⇓

open ℕ∞↦_ public

pred : ℕ∞ → ℕ∞
pred = ⟨ pred′ ⟩⇓
  module Pred where
  pred′ : ℕ∞⟶ (λ _ → ℕ∞)
  ⟨ pred′ ⟩zero    = zero
  ⟨ pred′ ⟩suc m _ = m
  ⟨ pred′ ⟩∞       = ∞
  ⟨ pred′ ⟩inf     = refl
  ⟨ pred′ ⟩set _   = trunc

_+_ : ℕ∞ → ℕ∞ → ℕ∞
m + n = ⟨ plus′ ⟩⇓ m
  module Plus where
  plus′ : ℕ∞⟶ (λ _ → ℕ∞)
  ⟨ plus′ ⟩zero    = n
  ⟨ plus′ ⟩suc m p = suc p
  ⟨ plus′ ⟩∞       = ∞
  ⟨ plus′ ⟩inf     = inf
  ⟨ plus′ ⟩set _   = trunc
