{-# OPTIONS --safe #-}
open import Cubical.Foundations.Prelude
module coDeBruijn.Thinning.Properties {𝑘} (K : Type 𝑘) where

open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit as ⊤
open import Cubical.Data.Sigma
open import Cubical.Data.Prod using ()
open import Cubical.Data.Sum.Base hiding (map)

open import Cubical.Relation.Nullary.Base

open import Cubical.Categories.Category.Base

open import coDeBruijn.Bwd
open import coDeBruijn.Thinning.Base K

private variable
  i j k : K
  iz jz kz : Bwd K

restrict : (iz -, i) ⊑ jz → iz ⊑ jz
restrict (θ o′) = restrict θ o′
restrict (θ os) = θ o′

too-big-for-itself : ¬ (iz -, i) ⊑ iz
too-big-for-itself (θ o′) = too-big-for-itself (restrict θ)
too-big-for-itself (θ os) = too-big-for-itself θ

module PathSpace where

  --   1 2 7 3 7
  --   1   7     

  cons-inj-left : (i ≡ j)
                → (iz -, i) ⊑ (jz -, j)
                → iz ⊑ jz
  cons-inj-left _ (θ o′) = restrict θ
  cons-inj-left _ (θ os) = θ

  oS : iz ⊑ jz → (p : i ≡ j) → (iz -, i) ⊑ (jz -, j)
  oS θ p = subst (λ focus → (_ -, _) ⊑ (_ -, focus)) p (θ os)

  keka : (p : i ≡ j)
       → (φ : (iz -, i) ⊑ (jz -, j))
       → φ ≡ cons-inj-left p (oS φ p)
  keka p φ = {!!}

  cons-inj-right : (iz ≡ jz)
                 → (iz -, i) ⊑ (jz -, j)
                 → i ≡ j
  cons-inj-right p (θ o′) = ⊥.rec (too-big-for-itself (subst (λ focus → (focus -, _) ⊑ _) p θ))
  cons-inj-right p (θ os) = refl

  Cover : (θ φ : iz ⊑ jz) → Type 𝑘
  Cover (θ o′) (φ o′) = Cover θ φ
  Cover (θ o′) (φ os) = ⊥*
  Cover (θ os) φ      = Cover θ (cons-inj-left refl φ)
  Cover oz     oz     = Unit*

  refl-code : (θ : iz ⊑ jz) → Cover θ θ
  refl-code (θ o′) = refl-code θ
  refl-code (θ os) = refl-code θ
  refl-code oz     = tt*

  encode : (θ φ : iz ⊑ jz) → (p : θ ≡ φ) → Cover θ φ
  encode θ _ = J (λ φ _ → Cover θ φ) (refl-code θ)

  encode-refl : (θ : iz ⊑ jz) → encode θ θ refl ≡ refl-code θ
  encode-refl θ = JRefl (λ φ _ → Cover θ φ) (refl-code θ)

  decode : (θ φ : iz ⊑ jz) → Cover θ φ → θ ≡ φ
  decode (θ os) φ       p =
    let z = restrict φ
        IH = decode θ {!!} p
    in {!!}
  decode (θ o′) (φ o′)  p = decode θ φ p |> cong _o′
  decode (θ o′) (φ os)  ()
  decode oz     oz      _ = refl

Cover⊑ : Bwd K → Bwd K → Type 𝑘
Cover⊑ []        _         = Unit*
Cover⊑ (_  -, _) []        = ⊥*
Cover⊑ (iz -, i) (jz -, j) = (Cover⊑ iz jz × (i ≡ j)) ⊎ Cover⊑ (iz -, i) jz

oi-code : ∀ iz → Cover⊑ iz iz
oi-code []        = _
oi-code (iz -, i) = inl (oi-code iz , refl)

encode⊑ : ∀ iz jz → (φ : iz ⊑ jz) → Cover⊑ iz jz
encode⊑ []        (_  -, _) (φ o′) = _
encode⊑ (iz -, i) (jz -, j) (φ o′) = inr $ encode⊑ _ _ φ
encode⊑ (_  -, _) (_  -, _) (φ os) = inl $ encode⊑ _ _ φ , refl
encode⊑ []        []        oz     = _

encode-oi : ∀ iz → encode⊑ iz iz oi ≡ oi-code iz
encode-oi []        = refl
encode-oi (iz -, i) = cong inl (ΣPathP (encode-oi iz , refl))

decode : ∀ iz jz → Cover⊑ iz jz → iz ⊑ jz
decode []        _         _             = oe
decode (iz -, i) (jz -, j) (inl (c , p)) = subst (λ z → (iz -, z) ⊑ (jz -, j)) (sym p) (decode _ _ c os)
decode (iz -, i) (jz -, j) (inr c)       = decode _ _ c o′

-- @0 decode-oi : ∀ iz → {K-set : isSet K} → decode iz iz (oi-code iz) ≡ oi
-- decode-oi []        = refl
-- decode-oi (iz -, i) {K-set} = let zz = isOfHLevelBwd 0 K-set in {!!}

-- kek : isProp (iz ⊑ jz)
-- kek {[]     } {[]     } oz oz = refl
-- kek {[]     } {jz -, j} (θ o′) (φ o′) = kek _ _ |> cong _o′
-- kek {iz -, i} {jz -, j} (θ o′) (q o′) = kek _ _ |> cong _o′
-- kek {iz -, i} {jz -, .i} (θ o′) (q os) = {!!}
-- kek {iz -, i} {jz -, .i} (θ os) q = {!!}

idl : (θ : iz ⊑ jz) → oi ⋆ θ ≡ θ
idl (θ o′) = idl θ |> cong _o′
idl (θ os) = idl θ |> cong _os
idl oz     = refl

idr : (θ : iz ⊑ jz) → θ ⋆ oi ≡ θ
idr (θ o′) = idr θ |> cong _o′
idr (θ os) = idr θ |> cong _os
idr oz     = refl

-- Δ₊ : Category 𝑘 𝑘
-- Category.ob Δ₊ = Bwd K
-- Category.Hom[_,_] Δ₊ = _⊑_
-- Category.id Δ₊ = oi
-- Category._⋆_ Δ₊ = _⋆_
-- Category.⋆IdL Δ₊ = idl
-- Category.⋆IdR Δ₊ = idr
-- Category.⋆Assoc Δ₊ = {!!}
-- Category.isSetHom Δ₊ = isProp→isSet kek
