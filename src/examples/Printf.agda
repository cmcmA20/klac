{-# OPTIONS --guardedness #-}
module examples.Printf where

open import Prelude

open import Data.Char using (Char)
open import Data.Integer.Base using (ℤ)
open import Data.Integer.Show using () renaming (show to show-ℤ)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; suc; zero)
open import Data.Nat.Show using (readMaybe) renaming (show to show-ℕ)
open import Data.String.Base using (String; _++_; toList; fromList; length)
open import Data.Unit using (⊤; tt)
open import Function.Base using (_$_)

open import IO

data Fmt : Type₀ where
  verbatim_ : String → Fmt
  %u        :          Fmt
  %s        :          Fmt

FmtString = List Fmt

types : FmtString → List Type₀
types []               = []
types (verbatim _ ∷ fs) =          types fs
types (%u         ∷ fs) = ℕ      ∷ types fs
types (%s         ∷ fs) = String ∷ types fs 
-- ⟦ %d         ∷ fs ⟧′ = ℤ      ∷ ⟦ fs ⟧′

fold-t : List Type₀ → Type₀
fold-t []       = String
fold-t (t ∷ ts) = t → fold-t ts

⟦_⟧ : FmtString → Type₀
⟦ fs ⟧ = fold-t (types fs)

sprintf : (acc : String) → (fs : FmtString) → ⟦ fs ⟧
sprintf acc []                  = acc
sprintf acc (verbatim str ∷ fs) =       sprintf (acc ++ str     ) fs
sprintf acc (%u           ∷ fs) = λ n → sprintf (acc ++ show-ℕ n) fs
sprintf acc (%s           ∷ fs) = λ s → sprintf (acc ++ s       ) fs

conv′ : (fuel : ℕ) (acc : String) → List Char → FmtString
helper : ℕ → Fmt → String → List Char → FmtString

helper fuel f acc cs = verbatim acc ∷ f ∷ conv′ fuel "" cs

conv′ 0 acc _ = []
conv′ (suc fuel) acc []               = verbatim acc ∷ []
conv′ (suc fuel) acc (c ∷ [])         = verbatim (acc ++ fromList (c ∷ [])) ∷ []
conv′ (suc fuel) acc ('%' ∷ 'u' ∷ cs) = helper fuel %u acc cs
conv′ (suc fuel) acc ('%' ∷ 's' ∷ cs) = helper fuel %s acc cs
conv′ (suc fuel) acc (c₁  ∷ c₂  ∷ cs) = conv′ fuel (acc ++ fromList (c₁ ∷ [])) (c₂ ∷ cs)

toFmtString : String → FmtString
toFmtString str = conv′ (length str) "" (toList str)

printf : (str : String) → ⟦ toFmtString str ⟧
printf str = sprintf "" (toFmtString str)

_ : printf "just a string"
    ≡ "just a string"
_ = refl

_ : printf "lol, x = %u"
    55
    ≡ "lol, x = 55"
_ = refl

_ : printf "hello, my name is %s and I'm %u years old"
    "Paul"
    420
    ≡ "hello, my name is Paul and I'm 420 years old"
_ = refl

fold-x : List Type₀ → Type₀
fold-x [] = ⊤
fold-x (t ∷ ts) = t × fold-x ts

⟦_⟧ᶜ : FmtString → Type₀
⟦ fs ⟧ᶜ = fold-x (types fs) → String

-- A₀ → A₁ → A₂ → ⋯ → Aₙ → R
-- becomes
-- A₀ × A₁ × A₂ × ⋯ × Aₙ → R
curryₙ : (fs : FmtString) → ⟦ fs ⟧ → ⟦ fs ⟧ᶜ
curryₙ [] s _ = s
curryₙ (verbatim _ ∷ fs) = curryₙ fs
curryₙ (%u         ∷ fs) g (n , ts) = curryₙ fs (g n) ts
curryₙ (%s         ∷ fs) g (s , ts) = curryₙ fs (g s) ts

getPrintfArgs : (fs : FmtString) → IO (fold-x (types fs))
getPrintfArgs [] = pure tt
getPrintfArgs (%u ∷ fs) = do
  n ← untilJust do
    putStrLn "Enter a natural number"
    s ← getLine
    pure $ readMaybe 10 s
  rest ← getPrintfArgs fs
  pure (n , rest)
getPrintfArgs (%s ∷ fs) = do
  putStrLn "Enter a string"
  s ← getLine
  rest ← getPrintfArgs fs
  pure (s , rest)
getPrintfArgs (verbatim _ ∷ fs) = getPrintfArgs fs

main : Main
main = run do
  putStrLn "Enter a format string"
  s ← getLine
  let f = toFmtString s
  as ← getPrintfArgs f
  putStrLn $ curryₙ f (printf s) as
