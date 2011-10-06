------------------------------------------------------------------------
-- Example: Left recursive expression grammar
------------------------------------------------------------------------

module TotalParserCombinators.Examples.Expression where

open import Coinduction
open import Data.Char as Char using (Char)
open import Data.List
open import Data.Nat
open import Data.String as String using (String)
open import Function
open import Relation.Binary.PropositionalEquality as P using (_≡_)

open import TotalParserCombinators.BreadthFirst
open import TotalParserCombinators.Lib
open import TotalParserCombinators.Parser

open Token Char Char._≟_

------------------------------------------------------------------------
-- An expression grammar

-- t ∷= t '+' f ∣ f
-- f ∷= f '*' a ∣ a
-- a ∷= '(' t ')' ∣ n

-- Applicative implementation of the grammar.

module Applicative where

  mutual

    term   = ♯ (return (λ e₁ _ e₂ → e₁ + e₂) ⊛ term) ⊛ tok '+' ⊛ factor
           ∣ factor

    factor = ♯ (return (λ e₁ _ e₂ → e₁ * e₂) ⊛ factor) ⊛ tok '*' ⊛ atom
           ∣ atom

    atom   = return (λ _ e _ → e) ⊛ tok '(' ⊛ ♯ term ⊛ tok ')'
           ∣ number

-- Monadic implementation of the grammar.

module Monadic where

  mutual

    term   = factor
           ∣ ♯ term            >>= λ e₁ →
             tok '+'           >>= λ _  →
             factor            >>= λ e₂ →
             return (e₁ + e₂)

    factor = atom
           ∣ ♯ factor          >>= λ e₁ →
             tok '*'           >>= λ _  →
             atom              >>= λ e₂ →
             return (e₁ * e₂)

    atom   = number
           ∣ tok '('           >>= λ _  →
             ♯ term            >>= λ e  →
             tok ')'           >>= λ _  →
             return e

------------------------------------------------------------------------
-- Unit tests

module Tests where

  test : ∀ {R xs} → Parser Char R xs → String → List R
  test p = parse p ∘ String.toList

  -- Some examples have been commented out in order to reduce
  -- type-checking times.

  -- ex₁ : test Applicative.term "1*(2+3)" ≡ [ 5 ]
  -- ex₁ = P.refl

  -- ex₂ : test Applicative.term "1*(2+3" ≡ []
  -- ex₂ = P.refl

  ex₃ : test Monadic.term "1+2+3" ≡ [ 6 ]
  ex₃ = P.refl

  ex₄ : test Monadic.term "+32" ≡ []
  ex₄ = P.refl
