{-# OPTIONS --safe #-}
module Teaser.DiffList.Base where

open import Cubical.Data.List.Base using (List) renaming (_++_ to _++′_)

open import Teaser.Prelude

record DiffList {ℓ} (A : Type ℓ) : Type ℓ where
  constructor difflist
  field
    @0 list : List A
    fun : List A → List A
    @0 prf : fun ≡ list ++′_
open DiffList

private variable
  ℓᵃ : Level
  A : Type ℓᵃ

List→DiffList : List A → DiffList A
List→DiffList xs = difflist xs (xs ++′_) refl

module _ where
  open import Cubical.Data.List.Base using () renaming ([] to []′)

  [] : DiffList A
  [] = difflist []′ (idfun _) refl

  DiffList→List : DiffList A → List A
  DiffList→List dxs = dxs .fun []′

_∷_ : A → DiffList A → DiffList A
x ∷ dxs = difflist (x ∷′ dxs .list) ((x ∷′_) ∘ dxs .fun) (funExt (λ k → cong (λ z → ((x ∷′_) ∘ z) k) (dxs .prf)))
  where open import Cubical.Data.List.Base using () renaming (_∷_ to _∷′_)

_++_ : DiffList A → DiffList A → DiffList A
list (dxs ++ dys) = dxs .fun (dys .list)
fun  (dxs ++ dys) = dxs .fun ∘ dys .fun
prf  (dxs ++ dys) = funExt $ λ k
  → (dxs .fun   ∘   dys .fun)      k  ≡⟨ cong₂ (λ w z → (w ∘ z) k) (dxs .prf) (dys .prf) ⟩
     dxs .list ++′ (dys .list  ++′ k) ≡⟨ sym (++-assoc (dxs .list) (dys .list) k) ⟩
    (dxs .list ++′  dys .list) ++′ k  ≡⟨ cong (λ z → z (dys .list) ++′ k) (sym (dxs .prf)) ⟩
    (dxs .fun (dys .list))     ++′ k  ∎
    where open import Cubical.Data.List.Properties using (++-assoc)
