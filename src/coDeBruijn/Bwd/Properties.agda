{-# OPTIONS --safe #-}
module coDeBruijn.Bwd.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

open import Cubical.Data.Nat.Base
open import Cubical.Data.List using (List; []; _∷_; isOfHLevelList)

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Instances.Sets

open import coDeBruijn.Bwd.Base

private variable
  ℓ ℓ′ ℓ″ : Level
  A : Type ℓ
  B : Type ℓ′
  C : Type ℓ″

module _ where

  private
    Bwd→List : Bwd A → List A
    Bwd→List []        = []
    Bwd→List (xs -, x) = x ∷ Bwd→List xs

    List→Bwd : List A → Bwd A
    List→Bwd []       = []
    List→Bwd (x ∷ xs) = List→Bwd xs -, x

    toFrom :  (xs : List A) → Bwd→List (List→Bwd xs) ≡ xs
    toFrom []       = refl
    toFrom (x ∷ xs) = cong (x ∷_) (toFrom xs)

    fromTo : (xs : Bwd A) → List→Bwd (Bwd→List xs) ≡ xs
    fromTo []        = refl
    fromTo (xs -, x) = fromTo xs |> cong (_-, x) 

  BwdListIso : Iso (Bwd A) (List A)
  Iso.fun BwdListIso = Bwd→List
  Iso.inv BwdListIso = List→Bwd
  Iso.rightInv BwdListIso = toFrom
  Iso.leftInv BwdListIso = fromTo

  BwdListEquiv : Bwd A ≃ List A
  BwdListEquiv = isoToEquiv BwdListIso

  @0 BwdList≡ : Bwd {ℓ} ≡ List
  BwdList≡ = funExt λ _ → ua BwdListEquiv

@0 isOfHLevelBwd : (h : HLevel)
     → isOfHLevel (suc (suc h)) A → isOfHLevel (suc (suc h)) (Bwd A)
isOfHLevelBwd h p = subst (isOfHLevel (suc (suc _))) (sym (cong (_$ _) BwdList≡)) $ isOfHLevelList h p

@0 Bwd′ : hSet ℓ → hSet ℓ
Bwd′ (A , A-set) = Bwd A , isOfHLevelBwd 0 A-set

map-id : (xs : Bwd A) → map (λ x → x) xs ≡ xs
map-id []        = refl
map-id (xs -, x) = map-id xs |> cong (_-, x)

map-comp : {f : A → B} {g : B → C} (xs : Bwd A) → map (g ∘ f) xs ≡ map g (map f xs)
map-comp []        = refl
map-comp (xs -, x) = map-comp xs |> cong (_-, _)

@0 FunctorBwd : Functor (SET ℓ) (SET ℓ)
Functor.F-ob FunctorBwd  = Bwd′
Functor.F-hom FunctorBwd = map
Functor.F-id FunctorBwd  = funExt map-id
Functor.F-seq FunctorBwd _ _ = funExt map-comp
