------------------------------------------------------------------------
-- Example: Right recursive expression grammar
------------------------------------------------------------------------

module TotalRecognisers.Simple.Expression where

open import Coinduction
open import Data.Bool
open import Data.Char as Char using (Char)
open import Data.String as String using (String)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable

import TotalRecognisers.Simple as P

private
  open module PC = P Char Char._≟_ hiding (_·_)
  open PC.P using (_·_)

------------------------------------------------------------------------
-- Recognisers for bits and binary numbers

-- Bits.

bit = tok '0' ∣ tok '1'

-- Numbers.

number = bit · ♯ (empty ∣ number)

------------------------------------------------------------------------
-- An expression grammar

-- t ∷= f '+' t ∣ f
-- f ∷= a '*' f ∣ a
-- a ∷= '(' t ')' ∣ n

mutual

  term   = factor · ♯ (tok '+' · ♯ term)
         ∣ factor

  factor = atom · ♯ (tok '*' · ♯ factor)
         ∣ atom

  atom   = tok '(' · ♯ term · ♯ tok ')'
         ∣ number

------------------------------------------------------------------------
-- Unit tests

module Tests where

  test : ∀ {n} → P n → String → Bool
  test p s = ⌊ String.toList s ∈? p ⌋

  ex₁ : test term "0*(0+0)" ≡ true
  ex₁ = refl

  ex₂ : test term "0*(0+0" ≡ false
  ex₂ = refl
