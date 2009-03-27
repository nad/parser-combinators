------------------------------------------------------------------------
-- The parser type
------------------------------------------------------------------------

module StructurallyRecursiveDescentParsing.Type where

open import Coinduction
open import Data.Bool

infixl 10 _!>>=_ _?>>=_
infixl  5 _∣_

------------------------------------------------------------------------
-- Parsers

-- A type for parsers which can be implemented using recursive
-- descent. The types used ensure that the implemented backends are
-- structurally recursive.
--
-- The boolean index is true iff the parser accepts the empty string.

data Parser (Tok : Set) : Bool → Set → Set1 where
  return : ∀ {R} (x : R) → Parser Tok true R

  fail   : ∀ {R} → Parser Tok false R

  token  : Parser Tok false Tok

  _∣_    : ∀ {e₁ e₂ R}
           (p₁ : Parser Tok  e₁       R)
           (p₂ : Parser Tok       e₂  R) →
                 Parser Tok (e₁ ∨ e₂) R

  -- The second parser's index cannot depend on the result of the
  -- first parser, because (in general) the result depends on the
  -- input string, and the index of p₁ ?>>= p₂, for which the result
  -- is not in scope, is the same as that of p₂.
  _?>>=_ : ∀ {e₂ R₁ R₂}
           (p₁ :      Parser Tok true R₁)
           (p₂ : R₁ → Parser Tok e₂   R₂) →
                      Parser Tok e₂   R₂

  -- If the first parser is guaranteed to consume something, then the
  -- second parser's index can depend on the result of the first
  -- parser, because the resulting index is already known to be false.
  _!>>=_ : ∀ {R₁ R₂} {e₂ : R₁ → Bool}
           (p₁ :                Parser Tok false  R₁)
           (p₂ : (x : R₁) → ∞₁ (Parser Tok (e₂ x) R₂)) →
                                Parser Tok false  R₂

-- Note that there is only one coinductive recursive component
-- (annotated with ∞₁). Making any other recursive component
-- coinductive would allow left recursive grammars to be formed, but
-- it is safe to use coinduction in _!>>=_ because we know that a
-- token has been consumed, so for every successive use of coinduction
-- we are at least one step closer to the end of the input.
