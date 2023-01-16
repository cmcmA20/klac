{-# OPTIONS --guardedness #-}
module examples.Conats where

open import Axiom.Extensionality.Propositional using (Extensionality)
open import Codata.Guarded.Stream using (Stream; head; tail; _∷_; tabulate; repeat)
open import Codata.Guarded.Stream.Relation.Binary.Pointwise using (_≈_; head; tail; reflexive)
open import Data.Bool using (false; true; not) renaming (Bool to 𝟚)
open import Data.Nat using (ℕ; suc; z≤n; s≤s; pred) renaming (_≥_ to _≥ⁿ_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function.Base using (_∘_; _∘′_)

open import Prelude
open import examples.ListC using (module Helpers)
open Helpers using (Iso)

{-
Coinduction is not easy
https://groups.google.com/g/homotopytypetheory/c/tYRTcI2Opyo/m/PIrI6t5me-oJ

Higher coinductive types
https://akuklev.livejournal.com/1211554.html

Flexible coinduction in Agda
https://arxiv.org/abs/2002.06047
-}

postulate
  fun-ext : {ℓ₁ ℓ₂ : Level} → Extensionality ℓ₁ ℓ₂
  stream-ext : {A : Type ℓ} → {s₁ s₂ : Stream A} → s₁ ≈ s₂ → s₁ ≡ s₂

module RawStreams where

  untabulate : {A : Type ℓ} → Stream A → (ℕ → A)
  untabulate s 0       = s .head
  untabulate s (suc i) = untabulate (s .tail) i

  ft : {A : Type ℓ} → {y : Stream A} → tabulate (untabulate y) ≈ y
  head ft = refl
  tail ft = ft

  tf : {A : Type ℓ} {x : ℕ → A} (i : ℕ) → untabulate (tabulate (x ∘′ suc)) i ≡ x (suc i)
  tf 0               = refl
  tf {x = x} (suc i) = tf {x = x ∘′ suc} i

  fun-stream-iso : {A : Type₀} → Iso (ℕ → A) (Stream A)
  Iso.to fun-stream-iso = tabulate
  Iso.from fun-stream-iso = untabulate
  Iso.to-from fun-stream-iso {x} = fun-ext (tf {x = x ∘′ pred})
  Iso.from-to fun-stream-iso = stream-ext ft

  η : {A : Type₀} (s : Stream A) → s ≡ head s ∷ tail s
  η {A} s = stream-ext helper
    where
    helper : {s′ : Stream A} → s′ ≈ (head s′ ∷ tail s′)
    head helper = refl
    tail helper = reflexive refl

data _≥_ : 𝟚 → 𝟚 → Type₀ where
  b≥b : {b : 𝟚} → b ≥ b
  t≥f : true ≥ false

≥-prop : (b₁ b₂ : 𝟚) → isProp (b₁ ≥ b₂)
≥-prop false false b≥b b≥b = refl
≥-prop true  false t≥f t≥f = refl
≥-prop true  true  b≥b b≥b = refl

fa : {b₁ b₂ : 𝟚} → b₁ ≡ false → b₁ ≥ b₂ → b₂ ≡ false
fa refl b≥b = refl

module Conat₁ where

  is-decreasing : (ℕ → 𝟚) → Type₀
  is-decreasing α = (i : ℕ) → α i ≥ α (suc i)

  ℕ∞ : Type₀
  ℕ∞ = Σ (ℕ → 𝟚) is-decreasing

  decr-prop : {α : ℕ → 𝟚} → isProp (is-decreasing α)
  decr-prop x y = fun-ext λ j → ≥-prop _ _ _ _

  ℕ∞-≡ : {u₁ u₂ : ℕ∞} → fst u₁ ≡ fst u₂ → u₁ ≡ u₂
  ℕ∞-≡ p = Σ-≡ p (decr-prop _ _)

open Conat₁

module Conat₂ where

  record is-decreasingₛ (s : Stream 𝟚) : Type₀ where
    coinductive
    field
      head : head s ≥ head (tail s)
      tail : is-decreasingₛ (tail s)
  open is-decreasingₛ public

  record sim {s : Stream 𝟚} (a b : is-decreasingₛ s) : Type₀ where
    coinductive
    field
      head : head a ≡ head b
      tail : sim (tail a) (tail b)
  open sim public

  postulate
    sim-ext : {s : Stream 𝟚} → {a b : is-decreasingₛ s} → sim a b → a ≡ b

  ℕₛ∞ : Type₀
  ℕₛ∞ = Σ (Stream 𝟚) is-decreasingₛ

  predₛ : ℕₛ∞ → ℕₛ∞
  predₛ (s , p) = tail s , tail p

  any-sim : {s : Stream 𝟚} → (x y : is-decreasingₛ s) → sim x y
  head (any-sim x y) = ≥-prop _ _ _ _
  tail (any-sim x y) = any-sim _ _

  decrₛ-prop : {s : Stream 𝟚} → isProp (is-decreasingₛ s)
  decrₛ-prop x y = sim-ext (any-sim x y)

  ℕₛ∞-≡ : {w₁ w₂ : ℕₛ∞} → proj₁ w₁ ≡ proj₁ w₂ → w₁ ≡ w₂
  ℕₛ∞-≡ p = Σ-≡ p (decrₛ-prop _ _)

open Conat₂

toₛ : ℕ∞ → ℕₛ∞
head (proj₁ (toₛ (f , _))) = f 0
tail (proj₁ (toₛ (f , p))) = proj₁ (toₛ (f ∘′ suc , p ∘ suc))
is-decreasingₛ.head (proj₂ (toₛ (_ , p))) = p 0
is-decreasingₛ.tail (proj₂ (toₛ (f , p))) = proj₂ (toₛ (f ∘′ suc , p ∘ suc))

fromₛ : ℕₛ∞ → ℕ∞
proj₁ (fromₛ (s , _)) 0       = head s
proj₁ (fromₛ w)       (suc i) = proj₁ (fromₛ (predₛ w)) i
proj₂ (fromₛ w)       0       = head (proj₂ w)
proj₂ (fromₛ w)       (suc i) = proj₂ (fromₛ (predₛ w)) i

ftₛ : (u : ℕ∞) (i : ℕ) → proj₁ (fromₛ (toₛ u)) i ≡ proj₁ u i
ftₛ u 0       = refl
ftₛ u (suc i) = ftₛ _ i

tfₛ : (y : ℕₛ∞) → proj₁ (toₛ (fromₛ y)) ≈ proj₁ y
head (tfₛ _) = refl
tail (tfₛ y) = tfₛ (predₛ y)

conats-same : Iso ℕ∞ ℕₛ∞
Iso.to conats-same = toₛ
Iso.from conats-same = fromₛ
Iso.to-from conats-same = ℕ∞-≡ (fun-ext (ftₛ _))
Iso.from-to conats-same = ℕₛ∞-≡ (stream-ext (tfₛ _))

module Conats₃ where

  data Step (A : Type ℓ) : 𝟚 → Type ℓ where
    stop :     Step A true
    go   : A → Step A false

  record CoiBox : Type₀ where
    constructor mkBox
    coinductive
    field
      ready   : 𝟚
      content : Step CoiBox ready
  open CoiBox public

  ungo : {A : Type ℓ} → Step A false → A
  ungo (go x) = x

open Conats₃

toᵇ : ℕₛ∞ → CoiBox
ready   (toᵇ (s , _)) = not (head s)
content (toᵇ (s , p)) with head s
... | false = stop
... | true  = go (toᵇ (tail s , tail p))

rf-decrₛ : is-decreasingₛ (repeat false)
head rf-decrₛ = b≥b
tail rf-decrₛ = rf-decrₛ

fromᵇ : CoiBox → ℕₛ∞
head (proj₁ (fromᵇ b)) with ready b
... | true  = false
... | false = true
tail (proj₁ (fromᵇ b)) with ready b | content b
... | true  | stop = repeat false
... | false | go w = proj₁ (fromᵇ w)
head (proj₂ (fromᵇ b)) with ready b | content b
... | true  | stop = b≥b
... | false | go w with ready w
... | true  = t≥f
... | false = b≥b
tail (proj₂ (fromᵇ b)) with ready b | content b
... | true  | stop = rf-decrₛ
... | false | go w = proj₂ (fromᵇ w)

once-false-always-false : (x : ℕₛ∞) → head (proj₁ x) ≡ false → repeat false ≈ proj₁ x
head (once-false-always-false   (_ , _) q) = sym q
tail (once-false-always-false x@(s , p) q) = once-false-always-false (predₛ x) (fa q (head p))

tfᵇ : (x : ℕₛ∞) → proj₁ (fromᵇ (toᵇ x)) ≈ proj₁ x
head (tfᵇ (s , _)) with head s
... | false = refl
... | true  = refl
tail (tfᵇ x@(s , p)) with head s in eq
... | false = once-false-always-false (predₛ x) (fa eq (head p))
... | true  = tfᵇ _

record _≈ᵇ_ (a b : CoiBox) : Type₀

data _≈ˢ_ : {rˣ rʸ : 𝟚} (x : Step CoiBox rˣ) (y : Step CoiBox rʸ) → Type₀ where
  ϕ : {x′ y′ : CoiBox} → x′ ≈ᵇ y′ → go x′ ≈ˢ go y′

record _≈ᵇ_ a b where
  coinductive
  field
    c : (a .ready ≡ true × b .ready ≡ true) ⊎
        content a ≈ˢ content b
open _≈ᵇ_

postulate
  box-ext : {a b : CoiBox} → a ≈ᵇ b → a ≡ b

reflᵇ : (b : CoiBox) → b ≈ᵇ b
c (reflᵇ b) with ready b | content b
... | true  | stop = inj₁ (refl , refl)
... | false | go w = inj₂ (ϕ (reflᵇ w))

box-sim : {a b : CoiBox} → a ≡ b → a ≈ᵇ b
c (box-sim {a} refl) with ready a | content a
... | true | stop = inj₁ (refl , refl)
... | false | go w = inj₂ (ϕ (reflᵇ _))

ηᵇ : (b : CoiBox) → b ≡ mkBox (ready b) (content b)
ηᵇ b = box-ext helper
  where
  helper : b ≈ᵇ mkBox (ready b) (content b)
  c helper with ready b | content b
  ... | true  | stop = inj₁ (refl , refl)
  ... | false | go w = inj₂ (ϕ (reflᵇ w))

-- ftᵇ : (b : CoiBox) → b ≈ᵇ toᵇ (fromᵇ b)
-- c (ftᵇ b) with ready b in eq | content b
-- ... | true  | stop = inj₁ (refl , refl)
-- ... | false | go w with fromᵇ b in what
-- ... | s , p = {!!} -- inj₂ (ϕ (subst (w ≈ᵇ_) (what₂ (s , p) {!!}) (box-sim (trans ({!!}) (cong (toᵇ ∘ predₛ) what)))))
-- 
-- same-conats-again : Iso ℕₛ∞ CoiBox
-- Iso.to same-conats-again = toᵇ
-- Iso.from same-conats-again = fromᵇ
-- Iso.to-from same-conats-again = ℕₛ∞-≡ (stream-ext (tfᵇ _))
-- Iso.from-to same-conats-again = sym (box-ext (ftᵇ _))
