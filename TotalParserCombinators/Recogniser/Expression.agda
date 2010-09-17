------------------------------------------------------------------------
-- Example: Left recursive expression grammar
------------------------------------------------------------------------

module TotalParserCombinators.Recogniser.Expression where

open import Coinduction
open import Data.Bool
open import Data.Char as Char using (Char)
open import Data.List
open import Data.String as String using (String)
open import Function
open import Relation.Binary.PropositionalEquality

open import TotalParserCombinators.BreadthFirst
import TotalParserCombinators.Lib as Lib
open import TotalParserCombinators.Recogniser

------------------------------------------------------------------------
-- Lifted versions of some parsers

-- Specific tokens.

tok : Char → P Char []
tok c = lift $ Lib.Token.tok Char Char._≟_ c

-- Numbers.

number : P Char []
number = lift Lib.number

------------------------------------------------------------------------
-- An expression grammar

-- t ∷= t '+' f ∣ f
-- f ∷= f '*' a ∣ a
-- a ∷= '(' t ')' ∣ n

mutual

  term   = ♯ term · tok '+' · factor
         ∣ factor

  factor = ♯ factor · tok '*' · atom
         ∣ atom

  atom   = tok '(' · ♯ term · tok ')'
         ∣ number

------------------------------------------------------------------------
-- Unit tests

module Tests where

  test : ∀ {n} → P Char n → String → Bool
  test p s = not $ null $ parse ⟦ p ⟧ (String.toList s)

  ex₁ : test term "1*(2+3)" ≡ true
  ex₁ = refl

  ex₂ : test term "1*(2+3" ≡ false
  ex₂ = refl
