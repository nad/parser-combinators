------------------------------------------------------------------------
-- Some small examples, using the "less noisy" combinators
------------------------------------------------------------------------

module TotalParserCombinators.Examples.LessNoisy where

open import Coinduction
open import Data.Char as Char using (Char)
open import Data.List
open import Data.Nat
open import Data.String as String using (String)
open import Function
open import Relation.Binary.PropositionalEquality

open import TotalParserCombinators.Applicative using (_⊛′_)
open import TotalParserCombinators.BreadthFirst
open import TotalParserCombinators.Examples.Noisy
  using (Expr; num; plus; times)
open import TotalParserCombinators.LessNoisy
import TotalParserCombinators.Lib as Lib

------------------------------------------------------------------------
-- Liftings of some noisy parser combinators

-- Tokens.

tok : Char → Parser Char Char []
tok t = ⟦ Lib.Token.tok Char Char._≟_ t ⟧⁻¹

-- Sequencing.

infixl 10 _⊙_

_⊙_ : ∀ {Tok R₁ R₂ fs xs} →
      Parser Tok (R₁ → R₂) fs → Parser Tok R₁ xs →
      Parser Tok R₂ (fs ⊛′ xs)
p₁ ⊙ p₂ = ⟦ Lib._⊙_ ⟦ p₁ ⟧ ⟦ p₂ ⟧ ⟧⁻¹

-- Numbers.

number : Parser Char ℕ _
number = ⟦ Lib.number ⟧⁻¹

------------------------------------------------------------------------
-- An expression grammar

-- t ∷= t '+' f ∣ f
-- f ∷= f '*' a ∣ a
-- a ∷= '(' t ')' ∣ n

-- Applicative implementation of the grammar.

module Applicative where

 mutual

    term   = ♯ (♯ (♯ return (λ e₁ _ e₂ → plus e₁ e₂) ⊛
                     term) ⊛ ♯ tok '+') ⊛ ♯ factor
           ∣ factor

    factor = ♯ (♯ (♯ return (λ e₁ _ e₂ → times e₁ e₂) ⊛
                     factor) ⊛ ♯ tok '*') ⊛ ♯ atom
           ∣ atom

    atom   = ♯ (♯ (return (λ _ e _ → e) ⊙
                   tok '(') ⊛ ♯ term) ⊛ ♯ tok ')'
           ∣ return num ⊙ number

-- Monadic implementation of the grammar.

module Monadic where

 mutual

    term   = factor
           ∣ ♯ term               >>= λ e₁ → ♯ (
             tok '+'              >>= λ _  → ♯ (
             factor               >>= λ e₂ → ♯
             return (plus e₁ e₂)             ))

    factor = atom
           ∣ ♯ factor             >>= λ e₁ → ♯ (
             tok '*'              >>= λ _  → ♯ (
             atom                 >>= λ e₂ → ♯
             return (times e₁ e₂)            ))

    atom   = return num ⊙ number
           ∣ tok '('              >>= λ _  → ♯ (
             term                 >>= λ e  → ♯ (
             tok ')'              >>= λ _  → ♯
             return e                        ))

------------------------------------------------------------------------
-- Unit tests

module Tests where

  test : ∀ {R xs} → Parser Char R xs → String → List R
  test p = parseComplete ⟦ p ⟧ ∘ String.toList

  ex₁ : test Applicative.term "1*(2+3)" ≡
          [ times (num 1) (plus (num 2) (num 3)) ]
  ex₁ = refl

  ex₂ : test Applicative.term "1*(2+3" ≡ []
  ex₂ = refl

  ex₃ : test Monadic.term "1+2+3" ≡
          [ plus (plus (num 1) (num 2)) (num 3) ]
  ex₃ = refl

  ex₄ : test Monadic.term "+32" ≡ []
  ex₄ = refl
