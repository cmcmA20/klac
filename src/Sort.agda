{-# OPTIONS --guardedness #-}
module Sort where

open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_; swap; prep) renaming (refl to ■; trans to _∙_)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (All-resp-↭; ↭-empty-inv)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Sort using ()
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.String using (String; _≤_; unwords; words) renaming (_≈_ to _str-≈_)
open import Data.String.Properties using (≤-isDecTotalOrder-≈)
open import Data.Sum using (inj₁; inj₂)
open import Function.Base using (_$_)
open import IO
open import Level using (Level; 0ℓ)
open import Relation.Binary using (IsDecTotalOrder; IsEquivalence; IsTotalPreorder; Rel)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

record Ord' (A : Set) : Set₁ where
  field
    _≈_ : Rel A 0ℓ
    _≲_ : Rel A 0ℓ
    itp : IsTotalPreorder _≈_ _≲_
open Ord' ⦃ ... ⦄

data IsSorted {A : Set} ⦃ @0 oi : Ord' A ⦄ : (@0 xs : List A) → Set where
  ISEmpty     :                                                                          IsSorted []
  ISSingleton : {@0 x : A}                                                             → IsSorted (x ∷ [])
  ISMany      : {@0 x₁ x₂ : A} {@0 xs : List A} (p : x₁ ≲ x₂) (_ : IsSorted (x₂ ∷ xs)) → IsSorted (x₁ ∷ x₂ ∷ xs)

sortedSuffix : {A : Set} ⦃ @0 oi : Ord' A ⦄ {@0 x : A} {xs : List A} (_ : IsSorted (x ∷ xs)) → IsSorted xs
sortedSuffix {xs = []    } ISSingleton             = ISEmpty
sortedSuffix {xs = _ ∷ []} (ISMany _ ISSingleton ) = ISSingleton
sortedSuffix {xs = _ ∷ _ } (ISMany _ (ISMany p q)) = ISMany p q

-- "is dominated by"
_◃_ : {A : Set} ⦃ oi : Ord' A ⦄ (u : A) (xs : List A) → Set
u ◃ xs = All (u ≲_) xs

strengthenDomination : {A : Set} ⦃ oi : Ord' A ⦄ {t x : A} {xs : List A} (p : t ≲ x) (_ : x ◃ xs) → t ◃ xs
strengthenDomination _ []       = []
strengthenDomination p (q ∷ qs) = trans p q ∷ strengthenDomination p qs
  where open IsTotalPreorder itp

headIsDominated : {A : Set} ⦃ oi : Ord' A ⦄ {x : A} {xs : List A} (s : IsSorted (x ∷ xs)) → x ◃ xs
headIsDominated {xs = []   } _            = []
headIsDominated {xs = _ ∷ _} (ISMany p q) = p ∷ strengthenDomination p (headIsDominated q)

Sorting : Set → Set₁
Sorting A = ⦃ oi : Ord' A ⦄ → (xs : List A) → Σ[ res ∈ List A ] (IsSorted res × xs ↭ res)

module Insert where

  insert : {A : Set} ⦃ oi : Ord' A ⦄
           (t : A)
           (xs : List A)
           (s : IsSorted xs) →
           Σ[ res ∈ List A ] (IsSorted res × (t ∷ xs) ↭ res)
  insert t []       _ = t ∷ [] , ISSingleton , ■
  insert t (x ∷ xs) s with total t x where open IsTotalPreorder itp
  ... | inj₁ p = t ∷ x ∷ xs , ISMany p s , ■
  ... | inj₂ p with insert t xs $ sortedSuffix s
  ... | [] , _ , v = ⊥-elim $ cons≠nil $ ↭-empty-inv v
    where
    cons≠nil : t ∷ xs ≡ [] → ⊥
    cons≠nil ()
  ... | y ∷ ys , u , v with All-resp-↭ v $ p ∷ headIsDominated s
  ... | q ∷ _ = x ∷ y ∷ ys , ISMany q u , (swap t x ■) ∙ (prep x v)

  insertionSort : {A : Set} → Sorting A
  insertionSort []       = [] , ISEmpty , ■
  insertionSort (x ∷ xs) with insertionSort xs
  ... | r  , p  , q with insert x r p
  ... | r' , p' , q' = r' , p' , (prep x q) ∙ q'

open Insert public


module Main where

  instance
    StringOrd' : Ord' String
    StringOrd' = record
      { _≈_ = _str-≈_
      ; _≲_ = _≤_
      ; itp = let open IsDecTotalOrder ≤-isDecTotalOrder-≈ in record
        { isPreorder = isPreorder
        ; total = total
        }
      }

  main : Main
  main = run do
    s ← getLine
    let s' , _ = insertionSort $ words s
    putStrLn $ unwords s'
