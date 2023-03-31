{-# OPTIONS --safe --overlapping-instances --instance-search-depth=2 #-}
open import Cubical.Relation.Binary.Toset using (Toset)

module Teaser.Sorting {ℓᵃ ℓ} (Â : Toset ℓᵃ ℓ) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Erased

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Bool using (Bool; true; false; true≢false)
open import Cubical.Data.Maybe using (Maybe; just; nothing; just-inj)
open import Cubical.Data.Sigma
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Truncation.Propositional as ∥∥₁

open import Cubical.Relation.Nullary

open import Cubical.Instances.DecEq
open import Cubical.Instances.HLevels
open import Cubical.Instances.Show

open import Teaser.Permutation using (List↭; []; _∷_; swap; trunc; List→List↭) renaming (elim-set to ↭-elim)

private module _ where
  open import Cubical.Relation.Binary.Toset using (TosetStr)
  open TosetStr (Â .snd) public
  A = Â .fst

data Listₛ : Type (ℓ-max ℓᵃ ℓ)
data @0 _≤ᴴ_ (a : A) : Listₛ → Type (ℓ-max ℓᵃ ℓ)

private
  variable
    a a′ x y : A
    as xs ys : Listₛ

data Listₛ where
  []  : Listₛ
  _∷_ : (a : A) (as : Listₛ) {@0 _ : a ≤ᴴ as} → Listₛ

data _≤ᴴ_ a where
  _≤ᴴ∷_ : (p : a ≤ a′) (ps : a′ ≤ᴴ as) → a ≤ᴴ (_∷_ a′ as {ps})
  ≤ᴴ[]  : a ≤ᴴ []

@0 ≤ᴴ-is-prop-valued : isProp (x ≤ᴴ xs)
≤ᴴ-is-prop-valued ≤ᴴ[]               ≤ᴴ[]   = refl    
≤ᴴ-is-prop-valued (x≤y ≤ᴴ∷ ps) (x≤y′ ≤ᴴ∷ _) = cong (_≤ᴴ∷ ps) (is-prop-valued _ _ x≤y x≤y′)

@0 cons≡ : {pˣ : x ≤ᴴ xs} {pʸ : y ≤ᴴ ys} →
           x ≡ y → xs ≡ ys →
           _∷_ x xs {pˣ} ≡ _∷_ y ys {pʸ}
cons≡ {x} p = subst P p d
  where    
   P : A → Type _
   P y′ = {xs′ ys′ : Listₛ} {pˣ : x ≤ᴴ xs′} {pʸ : y′ ≤ᴴ ys′} → xs′ ≡ ys′ → _∷_ x xs′ {pˣ} ≡ _∷_ y′ ys′ {pʸ}
   d : P x
   d {xs′} q = subst Q q c
    where    
     Q : (ys′ : Listₛ) → Type _
     Q ys′ = {pˣ : x ≤ᴴ xs′} {pʸ : x ≤ᴴ ys′} → _∷_ x xs′ {pˣ} ≡ _∷_ x ys′ {pʸ}
     c : Q xs′
     c {pˣ} {pʸ} = cong (λ _ → x ∷ xs′) (≤ᴴ-is-prop-valued pˣ pʸ)

Listₛ→List : Listₛ → List A
Listₛ→List []       = []
Listₛ→List (a ∷ as) = a ∷ Listₛ→List as

instance
  ShowListₛ : ⦃ Show A ⦄ → Show Listₛ
  Show.show ShowListₛ xs = show (Listₛ→List xs)

Listₛ→List↭ : Listₛ → List↭ A
Listₛ→List↭ = List→List↭ ∘ Listₛ→List

Sorting = ⦃ da : DecEq A ⦄ (xs : List↭ A) → Σ[ res ꞉ Listₛ ] (Erased ∥ xs ≡ Listₛ→List↭ res ∥₁)

module _ where
  empty? : Listₛ → Bool
  empty? []      = true
  empty? (_ ∷ _) = false

  -- can be upgraded to non-erased
  @0 discrete-Listₛ : Discrete A → Discrete Listₛ
  discrete-Listₛ _   []       []      = yes refl
  discrete-Listₛ _   []       (_ ∷ _) = no λ p → ⊥.rec (true≢false (cong empty? p))
  discrete-Listₛ _   (_ ∷ _ ) []      = no λ p → ⊥.rec (true≢false (cong empty? (sym p)))
  discrete-Listₛ _≟_ (x ∷ xs) (y ∷ ys) with x ≟ y
  ... | no  x≢y = no λ p → x≢y (just-inj _ _ (cong head p))
    where
      head : Listₛ → Maybe A
      head []      = nothing
      head (x ∷ _) = just x
  ... | yes x≡y with discrete-Listₛ _≟_ xs ys
  ... | yes xs≡ys = yes (cons≡ x≡y xs≡ys)
  ... | no  xs≢ys = no λ p → ⊥.rec (xs≢ys (cong tail p))
    where
      tail : Listₛ → Listₛ
      tail []       = []
      tail (_ ∷ xs) = xs

module Insertion (_≤?_ : (x y : A) → Dec (x ≤ y)) where

  insert : A → Listₛ → Listₛ
  @0 ≤ᴴinsert : {x y : A} {as : Listₛ} {p : y ≤ᴴ as} → ¬ (x ≤ y) → y ≤ᴴ insert x as

  insert x [] = _∷_ x [] {≤ᴴ[]}
  insert x (_∷_ a as {p}) with x ≤? a
  ... | yes x≤a = _∷_ x (_∷_ a as {p}) {x≤a ≤ᴴ∷ _}
  ... | no  x≰a = _∷_ a (insert x as) {≤ᴴinsert {p = p} x≰a}

  ≤ᴴinsert                      {p = ≤ᴴ[]   } x≰y = total′ _ _ x≰y ≤ᴴ∷ _
  ≤ᴴinsert {x = x} {as = a ∷ _} {p = p ≤ᴴ∷ _} x≰y with x ≤? a
  ... | yes _ = total′ _ _ x≰y ≤ᴴ∷ _
  ... | no  _ = p ≤ᴴ∷ _

  @0 insertCons : (x : A) (as : Listₛ) → Listₛ→List↭ (insert x as) ≡ x ∷ Listₛ→List↭ as
  insertCons _ [] = refl
  insertCons x (a ∷ as) with x ≤? a
  ... | yes _ = refl
  ... | no  _ = cong (a ∷_) (insertCons _ _) ∙ swap _ _ _

  module _ where
    @0 insertSwap : (x y : A) (as : Listₛ) → insert x (insert y as) ≡ insert y (insert x as)
    insertSwap x y [] with x ≤? y
    insertSwap x y [] | yes x≤y with y ≤? x
    insertSwap x y [] | yes x≤y | yes y≤x = cons≡ (is-antisym _ _ x≤y y≤x) (cons≡ (is-antisym _ _ y≤x x≤y) refl)
    insertSwap x y [] | yes x≤y | no  y≰x = cons≡ refl (cons≡ refl refl)
    insertSwap x y [] | no  x≰y with y ≤? x
    insertSwap x y [] | no  x≰y | yes y≤x = cons≡ refl (cons≡ refl refl)
    insertSwap x y [] | no  x≰y | no  y≰x = ⊥.rec (x≰y (total′ _ _ y≰x))
    insertSwap x y (z ∷ u) with y ≤? z
    insertSwap x y (z ∷ u) | yes y≤z with x ≤? y
    insertSwap x y (z ∷ u) | yes y≤z | yes x≤y with x ≤? z
    insertSwap x y (z ∷ u) | yes y≤z | yes x≤y | yes x≤z with y ≤? x
    insertSwap x y (z ∷ u) | yes y≤z | yes x≤y | yes x≤z | yes y≤x = cons≡ (is-antisym _ _ x≤y y≤x) (cons≡ (is-antisym _ _ y≤x x≤y) refl)
    insertSwap x y (z ∷ u) | yes y≤z | yes x≤y | yes x≤z | no  y≰x with y ≤? z
    insertSwap x y (z ∷ u) | yes y≤z | yes x≤y | yes x≤z | no  y≰x | yes y≤z' = cons≡ refl (cons≡ refl refl)
    insertSwap x y (z ∷ u) | yes y≤z | yes x≤y | yes x≤z | no  y≰x | no  y≰z  = ⊥.rec (y≰z y≤z)
    insertSwap x y (z ∷ u) | yes y≤z | yes x≤y | no  x≰z = ⊥.rec (x≰z (is-trans _ _ _ x≤y y≤z))
    insertSwap x y (z ∷ u) | yes y≤z | no  x≰y with x ≤? z
    insertSwap x y (z ∷ u) | yes y≤z | no  x≰y | yes x≤z with y ≤? x
    insertSwap x y (z ∷ u) | yes y≤z | no  x≰y | yes x≤z | yes y≤x = cons≡ refl (cons≡ refl refl)
    insertSwap x y (z ∷ u) | yes y≤z | no  x≰y | yes x≤z | no  y≰x = ⊥.rec (x≰y (total′ _ _ y≰x))
    insertSwap x y (z ∷ u) | yes y≤z | no  x≰y | no  x≰z with y ≤? z
    insertSwap x y (z ∷ u) | yes y≤z | no  x≰y | no  x≰z | yes y≤z' = cons≡ refl (cons≡ refl refl)
    insertSwap x y (z ∷ u) | yes y≤z | no  x≰y | no  x≰z | no  y≰z  = ⊥.rec (y≰z y≤z)
    insertSwap x y (z ∷ u) | no  y≰z with x ≤? z
    insertSwap x y (z ∷ u) | no  y≰z | yes x≤z with y ≤? x
    insertSwap x y (z ∷ u) | no  y≰z | yes x≤z | yes y≤x = ⊥.rec (y≰z (is-trans _ _ _ y≤x x≤z))
    insertSwap x y (z ∷ u) | no  y≰z | yes x≤z | no  y≰x with y ≤? z
    insertSwap x y (z ∷ u) | no  y≰z | yes x≤z | no  y≰x | yes y≤z  = ⊥.rec (y≰z y≤z)
    insertSwap x y (z ∷ u) | no  y≰z | yes x≤z | no  y≰x | no  y≰z' = cons≡ refl (cons≡ refl refl)
    insertSwap x y (z ∷ u) | no  y≰z | no  x≰z with y ≤? z
    insertSwap x y (z ∷ u) | no  y≰z | no  x≰z | yes y≤z  = ⊥.rec (y≰z y≤z)
    insertSwap x y (z ∷ u) | no  y≰z | no  x≰z | no  y≰z' = cons≡ refl (insertSwap x y u)

  insertSort : Sorting
  insertSort = ↭-elim ([] , [ ∣ refl ∣₁ ])
                      (λ x (xs , [ p ]) → insert x xs , [ ∥∥₁.map (λ q → cong (x ∷_) q ∙ sym (insertCons x xs)) p ])
                      (λ x₁ x₂ (res , _) → ΣPathPProp (λ _ → erasedProp .iohl) (insertSwap _ _ res))
                      (λ _ → isSetΣSndProp (Discrete→isSet (discrete-Listₛ _≟_)) (λ _ → erasedProp .iohl))
    where erasedProp : {P : _} → IsProp (Erased ∥ P ∥₁)
          erasedProp = it
