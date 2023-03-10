{-# OPTIONS --safe #-}
module Teaser.FreeMonoid.Base where

open import Teaser.Prelude

data FreeMonoid {ℓ} (A : Type ℓ) : Type ℓ where
  ε   : FreeMonoid A
  [_] : A → FreeMonoid A
  _·_ : FreeMonoid A → FreeMonoid A → FreeMonoid A
  @0 leftId  : ∀ xs → ε  · xs ≡ xs
  @0 rightId : ∀ xs → xs · ε  ≡ xs
  @0 assoc   : ∀ xs ys zs → (xs · ys) · zs ≡ xs · (ys · zs)
  @0 trunc   : isSet (FreeMonoid A)

private variable
  ℓᵃ ℓᵇ : Level
  A : Type ℓᵃ
  B : Type ℓᵇ

module _ {B : FreeMonoid A → Type ℓᵇ}
         (ε*   : B ε)
         ([_]* : (x : A) → B [ x ])
         (_⋯_  : {xs ys : FreeMonoid A} → B xs → B ys → B (xs · ys)) where

  module _ (@0 leftId*  : {xs : FreeMonoid A} (xs* : B xs) → PathP (λ i → B (leftId xs i)) (ε* ⋯ xs*) xs*)
           (@0 rightId* : {xs : FreeMonoid A} (xs* : B xs) → PathP (λ i → B (rightId xs i)) (xs* ⋯ ε*) xs*)
           (@0 assoc*   : {xs ys zs : FreeMonoid A} (xs* : B xs) (ys* : B ys) (zs* : B zs) → PathP (λ i → B (assoc xs ys zs i)) ((xs* ⋯ ys*) ⋯ zs*) (xs* ⋯ (ys* ⋯ zs*)))
           (@0 trunc*   : (xs : FreeMonoid A) → isSet (B xs)) where
    elim-set : (xs : FreeMonoid A) → B xs
    elim-set ε = ε*
    elim-set [ x ] = [ x ]*
    elim-set (xs · ys) = elim-set xs ⋯ elim-set ys
    elim-set (leftId xs i) = leftId* (elim-set xs) i
    elim-set (rightId xs i) = rightId* (elim-set xs) i
    elim-set (assoc xs ys zs i) = assoc* (elim-set xs) (elim-set ys) (elim-set zs) i
    elim-set (trunc xs xs′ p q i j) =
      isOfHLevel→isOfHLevelDep 2 trunc* (elim-set xs) (elim-set xs′) (cong elim-set p) (cong elim-set q) (trunc xs xs′ p q) i j
      where open import Cubical.Foundations.HLevels using (isOfHLevel→isOfHLevelDep)


  module _ (@0 B-prop : {xs : FreeMonoid A} → isProp (B xs)) where
    elim-prop : (xs : FreeMonoid A) → B xs
    elim-prop = elim-set (λ _ → toPathP (B-prop _ _))
                         (λ _ → toPathP (B-prop _ _))
                         (λ _ _ _ → toPathP (B-prop _ _))
                         (λ _ → isProp→isSet B-prop)


module _ (ε*   : B)
         ([_]* : (x : A) → B)
         (_⋯_  : B → B → B)
         (@0 leftId*  : (xs* : B) → ε*  ⋯ xs* ≡ xs*)
         (@0 rightId* : (xs* : B) → xs* ⋯ ε*  ≡ xs*)
         (@0 assoc*   : (xs* ys* zs* : B) → (xs* ⋯ ys*) ⋯ zs* ≡ xs* ⋯ (ys* ⋯ zs*))
         (@0 B-set : isSet B) where
  rec-set : (xs : FreeMonoid A) → B
  rec-set = elim-set ε* [_]* _⋯_ leftId* rightId* assoc* (λ _ → B-set)


module _ ⦃ @0 A-set : IsSet A ⦄ where
  open import Cubical.Data.List.Base using (List; []; _∷_)

  -- ‶normalization″ procedure
  FreeMonoid→List : FreeMonoid A → List A
  FreeMonoid→List = rec-set [] (_∷ []) _++_ (λ _ → refl) ++-unit-r ++-assoc (isOfHLevelList 0 (A-set .iohl))
    where open import Cubical.Data.List.Properties using (++-unit-r; ++-assoc; isOfHLevelList)
          open import Cubical.Data.List.Base using (_++_)

  List→FreeMonoid : List A → FreeMonoid A
  List→FreeMonoid []       = ε
  List→FreeMonoid (x ∷ xs) = [ x ] · List→FreeMonoid xs

  open import Cubical.Data.Maybe.Base using (Maybe; nothing; just)

  first : Maybe A → Maybe A → Maybe A
  first nothing  my = my
  first (just x) _  = just x

  first-unit : (xs* : Maybe A) → first xs* nothing ≡ xs*
  first-unit nothing  = refl
  first-unit (just _) = refl

  first-assoc : (xs* ys* zs* : Maybe A) → first (first xs* ys*) zs* ≡ first xs* (first ys* zs*)
  first-assoc nothing  _ _ = refl
  first-assoc (just _) _ _ = refl

  open import Cubical.Data.Maybe.Properties using (isOfHLevelMaybe)

  head : FreeMonoid A → Maybe A
  head = rec-set nothing just first (λ _ → refl) first-unit first-assoc (isOfHLevelMaybe 0 (A-set .iohl))

  last : FreeMonoid A → Maybe A
  last = rec-set nothing just (flip first) first-unit (λ _ → refl) (λ _ _ zs* → sym (first-assoc zs* _ _)) (isOfHLevelMaybe 0 (A-set .iohl))

_∷_ : A → FreeMonoid A → FreeMonoid A
x ∷ xs = [ x ] · xs

map : (A → B) → FreeMonoid A → FreeMonoid B
map f = elim-set ε (λ x → [ f x ]) _·_ leftId rightId assoc (λ _ → trunc)
