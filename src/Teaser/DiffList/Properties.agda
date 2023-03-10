{-# OPTIONS --safe #-}
module Teaser.DiffList.Properties where

open import Teaser.Prelude
open import Teaser.DiffList.Base
open DiffList

private variable
  ℓᵃ ℓᵇ ℓᶜ ℓᵈ : Level
  A : Type ℓᵃ
  B : A → Type ℓᵇ
  C : (a : A) → B a → Type ℓᶜ

module @0 _ where
  open import Cubical.Reflection.RecordEquiv
  unquoteDecl DiffListIsoΣ = declareRecordIsoΣ DiffListIsoΣ (quote DiffList)

  open import Cubical.Data.Nat.Base using (ℕ; suc)
  instance
    @0 IsOfHLevelDiffList : {n : ℕ} → ⦃ IsOfHLevel (suc (suc n)) A ⦄ → IsOfHLevel (suc (suc n)) (DiffList A)
    IsOfHLevel.iohl (IsOfHLevelDiffList {n = n} ⦃ A-hl ⦄) =
      subst (isOfHLevel (suc (suc n)))
            (sym (ua (isoToEquiv DiffListIsoΣ)))
            $ isOfHLevelΣ (suc (suc n)) list-hl
            $ λ _ → isOfHLevelΣ (suc (suc n)) list-fun-hl
            $ λ _ → isOfHLevelSuc (suc n)
            $ isOfHLevelΩ→isOfHLevel _ (λ _ → list-fun-hl _ _) _ _
      where open import Cubical.Foundations.Univalence using (ua)
            open import Cubical.Foundations.Isomorphism using (isoToEquiv; Iso)
            open import Cubical.Data.List using (isOfHLevelList)
            list-hl = isOfHLevelList n (A-hl .iohl)
            list-fun-hl = isOfHLevelΠ (suc (suc n)) (λ _ → list-hl)

private
  cong₃′ : {D : (@0 a : A) → (b : B a) → (@0 c : C a b) → Type ℓᵈ}
           (f : (@0 a : A) → (b : B a) → (@0 c : C a b) → D a b c)
           {@0 x : A    } {@0 y : A    } (@0 p : x ≡ y)
           {@0 u : B x  } {@0 v : B y  } (q : PathP (λ i → B (p i)      ) u v)
           {@0 w : C x u} {@0 z : C y v} (@0 r : PathP (λ i → C (p i) (q i)) w z)
         → PathP (λ i → D (p i) (q i) (r i)) (f x u w) (f y v z)
  cong₃′ f p q r i = f (p i) (q i) (r i)
  {-# INLINE cong₃′ #-}

module _ ⦃ @0 A-set : IsSet A ⦄ where
  open import Cubical.Data.List using (List; isOfHLevelList) renaming ([] to []′; _++_ to _++′_; ++-unit-r to ++-unit-r′)
  open import Cubical.Foundations.Isomorphism
  open import Cubical.Foundations.Univalence

  dl≡ : {dxs dys : DiffList A} → (dxs .fun ≡ dys .fun) → dxs ≡ dys
  dl≡ {dxs = dxs} {dys = dys} r =
    let @0 h₁ : _
        h₁ = cong (_$ []′) (dxs .prf) ∙ ++-unit-r′ _
        @0 h₂ : _
        h₂ = cong (_$ []′) (dys .prf) ∙ ++-unit-r′ _
    in cong₃′ difflist (sym h₁ ∙ cong (_$ []′) r ∙ h₂) r (toPathP (isSet→ (isOfHLevelList 0 (A-set .iohl))  _ _ _ _))

  private instance
    myRefl : {ℓ : Level} {T : Type ℓ} {x : T} → x ≡ x
    myRefl = refl

    dlRefl : {dxs dys : DiffList A} → ⦃ dxs .fun ≡ dys .fun ⦄ → dxs ≡ dys
    dlRefl ⦃ p ⦄ = dl≡ p

  ++-assoc : (dxs dys dzs : DiffList A) → (dxs ++ dys) ++ dzs ≡ dxs ++ (dys ++ dzs)
  ++-assoc _ _ _ = dlRefl

  ++-unit-l : (dxs : DiffList A) → [] ++ dxs ≡ dxs
  ++-unit-l _ = dlRefl

  ++-unit-r : (dxs : DiffList A) → dxs ++ [] ≡ dxs
  ++-unit-r _ = dlRefl

  @0 observe : DiffList A ≡ List A
  observe = ua (isoToEquiv same)
    where
    open import Cubical.Foundations.Univalence using (ua)
    open import Cubical.Foundations.Isomorphism using (isoToEquiv; Iso)
    open Iso

    same : Iso (DiffList A) (List A)
    fun same = DiffList→List
    inv same = List→DiffList
    rightInv same = ++-unit-r′
    leftInv same dxs = dl≡ $ funExt λ k
      → dxs .fun []′ ++′ k ≡⟨ cong (_++′ k) $ cong (_$ []′) (dxs .prf) ∙ ++-unit-r′ _ ⟩
        dxs .list    ++′ k ≡⟨ cong (_$ k) $ sym (dxs .prf) ⟩
        dxs .fun         k ∎

  @0 DiffList-set : isSet (DiffList A)
  DiffList-set = IsOfHLevelDiffList .iohl


-- module Test where

--   open import Cubical.Data.Unit using (tt; isSetUnit) renaming (Unit to ⊤)

--   ℕᶜ : Type₀
--   ℕᶜ = DiffList ⊤

--   instance
--     @0 ⊤-set : IsSet ⊤
--     IsOfHLevel.iohl ⊤-set = isSetUnit

--   zero = []
--   suc : ℕᶜ → ℕᶜ
--   suc = tt ∷_

--   _+_ : ℕᶜ → ℕᶜ → ℕᶜ
--   _+_ = _++_

--   data Vec′ (A : Type ℓᵃ) : ℕᶜ → Type ℓᵃ where
--     emp  : Vec′ A zero
--     cons : {n : ℕᶜ} → A → Vec′ A n → Vec′ A (suc n)

  -- concat : {m n : ℕᶜ} → Vec′ A m → Vec′ A n → Vec′ A (m + n)
  -- concat emp         ys = subst (Vec′ _) (sym (++-unit-l _)) ys
  -- concat (cons x xs) ys = {!!}
