module Test where

open import Cubical.Foundations.Prelude

-- data Delay (A : Type) : Type where
--   done : A → Delay A
--   step : Delay A → Delay A

open import Cubical.Data.Sum
record Delay (A : Type) : Type where
  coinductive
  field
    step : A ⊎ (Delay A)

open Delay public

bad : {A : Type} → Delay A
bad .step = inr bad

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order

good : (m n : ℕ) → Delay ℕ
good zero    n .Delay.step = inl n
good (suc m) n .Delay.step = inr (good m (suc n))

test : Delay ℕ
test = good 2 2

open import Cubical.Data.Maybe
open import Cubical.Data.Sigma.Base
fueled-computer : {A : Type} (steps : ℕ) → (acc : ℕ) → Delay A → (Delay A ⊎ A) × ℕ
fueled-computer zero        acc x = inl x , acc
fueled-computer (suc steps) acc x with (x .step)
... | inl val = inr val , suc acc
... | inr x   = fueled-computer steps (suc acc) x

good-converges : (m n k l : ℕ) (prf : l > m) → fueled-computer l k (good m n) ≡ (inr (m + n) , suc m + k)
good-converges m n k zero    prf = {!!} -- absurd
good-converges m n k (suc l) prf with (step (good m n))
good-converges zero    n k (suc l) prf | inl x = {!!} -- decEq x n
good-converges (suc m) n k (suc l) prf | inl x = {!!} -- absurd

good-converges m n k (suc l) (zero  , p) | inr x = {!!} -- ?
good-converges zero    n k (suc l) (suc q , p) | inr x = let zz = good-converges 0 n (suc k) l (q , {!!}) in {!!}
good-converges (suc m) n k (suc l) (suc q , p) | inr x = {!!}
