------------------------------------------------------------------------
-- A simplified parser type
------------------------------------------------------------------------

{-# OPTIONS --no-termination-check #-}

-- Less general, but sometimes easier to use.

module StructurallyRecursiveDescentParsing.Simplified where

open import Coinduction
open import Data.Bool

import StructurallyRecursiveDescentParsing.Parser as Parser
open Parser hiding (Parser)
import StructurallyRecursiveDescentParsing.Parser.Semantics
  as Semantics

infixl 10 _!>>=_ _?>>=_
infixl  5 _∣_

-- A type for parsers which are not left recursive.
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

  _?>>=_ : ∀ {e₂ R₁ R₂}
           (p₁ :      Parser Tok true R₁)
           (p₂ : R₁ → Parser Tok e₂   R₂) →
                      Parser Tok e₂   R₂

  _!>>=_ : ∀ {R₁ R₂} {e₂ : R₁ → Bool}
           (p₁ :                Parser Tok false  R₁)
           (p₂ : (x : R₁) → ∞₁ (Parser Tok (e₂ x) R₂)) →
                                Parser Tok false  R₂

-- The semantics of simplified parsers is defined by translation.
-- TODO: Currently not accepted by the termination checker.

⟦_⟧ : ∀ {Tok e R} → Parser Tok e R → Parser.Parser Tok e R
⟦ return x   ⟧ = return x
⟦ fail       ⟧ = fail
⟦ token      ⟧ = token
⟦ p₁ ∣ p₂    ⟧ = ⟦ p₁ ⟧ ∣ ⟦ p₂ ⟧
⟦ p₁ !>>= p₂ ⟧ =           ⟦ p₁ ⟧ >>= λ x → ♯₁ ⟦ ♭₁ (p₂ x) ⟧
⟦ p₁ ?>>= p₂ ⟧ = cast lem (⟦ p₁ ⟧ >>= λ x →    ⟦     p₂ x  ⟧)
  where lem = Semantics.any-initial-true ⟦ p₁ ⟧
