{-# OPTIONS --guardedness #-}
module examples.Printf where

open import Data.List using (List; []; _∷_)
open import Data.Nat.Show using (readMaybe)
open import Data.String.Base using (String)
open import Data.Unit using (⊤; tt)
open import Function.Base using (_$_)
open import IO

open import Prelude
open import Day5

fold-x : List Type₀ → Type₀
fold-x [] = ⊤
fold-x (t ∷ ts) = t × fold-x ts

⟦_⟧ᶜ : FmtString → Type₀
⟦ fs ⟧ᶜ = fold-x (types fs) → String

-- A₀ → A₁ → A₂ → ⋯ → Aₙ → R
-- becomes
-- A₀ × A₁ × A₂ × ⋯ × Aₙ → R
uncurryₙ : (fs : FmtString) → ⟦ fs ⟧ → ⟦ fs ⟧ᶜ
uncurryₙ [] s _ = s
uncurryₙ (verbatim _ ∷ fs) = uncurryₙ fs
uncurryₙ (%u         ∷ fs) g (n , ts) = uncurryₙ fs (g n) ts
uncurryₙ (%s         ∷ fs) g (s , ts) = uncurryₙ fs (g s) ts

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
  putStrLn $ uncurryₙ f (printf s) as
