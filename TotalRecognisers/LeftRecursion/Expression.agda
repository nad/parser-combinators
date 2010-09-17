------------------------------------------------------------------------
-- Example: Left recursive expression grammar
------------------------------------------------------------------------

module TotalRecognisers.LeftRecursion.Expression where

open import Coinduction
open import Data.Bool hiding (_∧_)
open import Data.Char as Char using (Char)
open import Data.Nat using (ℕ; _≤?_)
open import Data.String as String using (String)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable

import TotalRecognisers.LeftRecursion as P
import TotalRecognisers.LeftRecursion.Lib as Lib

open P Char
open Lib Char
open KleeneStar₁
open Tok Char._≟_

------------------------------------------------------------------------
-- Recognisers for digits and numbers

-- Digits.

digit : P _
digit = sat in-range
  where
  in-range : Char → Bool
  in-range t = ⌊ Char.toNat '0' ≤? Char.toNat  t  ⌋ ∧
               ⌊ Char.toNat  t  ≤? Char.toNat '9' ⌋

-- Numbers.

number : P _
number = digit +

------------------------------------------------------------------------
-- An expression grammar

-- t ∷= t '+' f ∣ f
-- f ∷= f '*' a ∣ a
-- a ∷= '(' t ')' ∣ n

mutual

  term   = ♯ (♯ term · ♯ tok '+') · ♯ factor
         ∣ factor

  factor = ♯ (♯ factor · ♯ tok '*') · ♯ atom
         ∣ atom

  atom   = ♯ (♯ tok '(' · ♯ term) · ♯ tok ')'
         ∣ number

------------------------------------------------------------------------
-- Unit tests

module Tests where

  test : ∀ {n} → P n → String → Bool
  test p s = ⌊ String.toList s ∈? p ⌋

  ex₁ : test term "1*(2+3)" ≡ true
  ex₁ = refl

  ex₂ : test term "1*(2+3" ≡ false
  ex₂ = refl
