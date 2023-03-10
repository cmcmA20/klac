{-# OPTIONS --guardedness #-}
module Teaser.App where

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Foundations.Prelude
open import Cubical.IO
open import Cubical.Relation.Nullary using (Dec; yes; no; ¬_; Discrete)

open import Teaser.Prelude
open import Teaser.Erased

_≤″_ : ℕ → ℕ → Type₀
m ≤″ n = ∥ m ≤ n ∥₁

open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥-rec)
module _ where
  injSuc′ : {m n : ℕ} → suc m ≡ suc n → m ≡ n
  injSuc′ p = cong predℕ′ p
    where
      predℕ′ : ℕ → ℕ
      predℕ′ zero = zero
      predℕ′ (suc n) = n

  +-suc′ : ∀ m n → m + suc n ≡ suc (m + n)
  +-suc′ zero    n = refl
  +-suc′ (suc m) n = cong suc (+-suc′ m n)

  +-zero′ : ∀ m → m + 0 ≡ m
  +-zero′ zero = refl
  +-zero′ (suc m) = cong suc (+-zero′ m)

  caseNat′ : ∀ {ℓ} → {A : Type ℓ} → (a0 aS : A) → ℕ → A
  caseNat′ a0 aS zero    = a0
  caseNat′ a0 aS (suc n) = aS

  snotz′ : {n : ℕ} → ¬ (suc n ≡ 0)
  snotz′ e = subst (caseNat′ ⊥ ℕ) e zero

  ¬-<-zero′ : {m : ℕ} → ¬ m < 0
  ¬-<-zero′ (k , p) = snotz′ ((sym (+-suc′ k _)) ∙ p)

discreteℕ′ : Discrete ℕ
discreteℕ′ zero zero = yes refl
discreteℕ′ zero (suc n) = no λ p → snotz′ (sym p)
discreteℕ′ (suc m) zero = no snotz′
discreteℕ′ (suc m) (suc n) with discreteℕ′ m n
... | yes p = yes (cong suc p)
... | no p = no (λ x → p (injSuc′ x))

_≤?_ : (x y : ℕ) → Dec (x ≤″ y)
zero  ≤? y     = yes ∣ y , +-zero′ _ ∣₁
suc x ≤? zero  = no λ p → ∥∥₁-rec (λ _ ()) (λ x → x) (∥∥₁-map ¬-<-zero′ p)
suc x ≤? suc y with x ≤? y
... | yes ∣x≤y∣₁ = yes (∥∥₁-map (λ (k , p) → k , +-suc′ _ _ ∙ cong suc p) ∣x≤y∣₁)
... | no  ∣x≰y∣₁ = no λ p → ∣x≰y∣₁ (∥∥₁-map (λ (k , q) → k , injSuc′ (sym (+-suc′ _ _) ∙ q)) p)

module _ where
  open import Cubical.Relation.Binary.Poset
  open IsPoset
  open import Teaser.Relation.Binary.Toset
  open IsToset

  open import Cubical.Data.Sum using (inl; inr)
  @0 ℕ-is-toset : IsToset _≤″_
  is-set (isPoset ℕ-is-toset)             = isSetℕ
  is-prop-valued (isPoset ℕ-is-toset) _ _ = squash₁
  is-refl (isPoset ℕ-is-toset) _          = ∣ ≤-refl ∣₁
  is-trans (isPoset ℕ-is-toset) _ _ _     = ∥∥₁-map2 ≤-trans
  is-antisym (isPoset ℕ-is-toset) _ _ p q = ∥∥₁-rec (isSetℕ _ _) (λ x → x) (∥∥₁-map2 ≤-antisym p q)
  total ℕ-is-toset x y with x ≟ y
  ... | lt (k , p) = inl ∣ suc k , sym (+-suc _ _) ∙ p ∣₁
  ... | eq p       = inl ∣ 0 , p ∣₁
  ... | gt (k , p) = inr ∣ suc k , sym (+-suc _ _) ∙ p ∣₁

  ℕ-toset : Toset ℓ-zero ℓ-zero
  ℕ-toset = toset ℕ _≤″_ ℕ-is-toset

main : Main
main = run do
  s ← getLine
  let
    xs = 4 ∷ 2 ∷ 0 ∷ 1 ∷ 3 ∷ 3 ∷ 7 ∷ []
    result = insertSort _≤?_ discreteℕ′ (List→List↭ xs)
  putStrLn $ show-Listₛ $ result .fst
  where
  open import Cubical.Foundations.Function using (_$_)
  open import Cubical.Data.List using ([]; _∷_)
  open import Teaser.Permutation using (List→List↭)
  open import Teaser.Sorting ℕ-toset using (Listₛ; []; _∷_; module Insertion)
  open Insertion using (insertSort)
  open import Agda.Builtin.String using (String; primShowNat) renaming (primStringAppend to _++_)
  show-Listₛ : Listₛ → String
  show-Listₛ [] = "[]"
  show-Listₛ (x ∷ xs) = primShowNat x ++ (" ∷ " ++ show-Listₛ xs)
