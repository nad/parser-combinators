------------------------------------------------------------------------
-- The parser type
------------------------------------------------------------------------

module StructurallyRecursiveDescentParsing.Parser where

open import Data.Bool
open import Data.List
open import Data.Function
open import Relation.Binary.PropositionalEquality

open import StructurallyRecursiveDescentParsing.Coinduction

infixl 10 _>>=_
infixl  5 _∣_

mutual

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
    _>>=_  : ∀ {e₁ R₁ R₂} {e₂ : R₁ → Bool}
             (p₁ :                   Parser Tok  e₁                        R₁)
             (p₂ : (x : R₁) → ∞? e₁ (Parser Tok (         e₂ x           ) R₂)) →
                                     Parser Tok (e₁ ∧ any e₂ (initial p₁)) R₂
    cast   : ∀ {e₁ e₂ R}
             (eq : e₁ ≡ e₂) (p : Parser Tok e₁ R) → Parser Tok e₂ R

  -- The results which can be emitted without consuming any input:
  --   x ∈ initial p  iff  x ∈ p · []
  -- (see StructurallyRecursiveDescentParsing.Parser.Semantics).

  initial : ∀ {Tok e R} → Parser Tok e R → List R
  initial (return x)            = [ x ]
  initial fail                  = []
  initial token                 = []
  initial (p₁ ∣ p₂)             = initial p₁ ++ initial p₂
  initial (_>>=_ {true}  p₁ p₂) = concat $ map (λ x → initial (p₂ x)) (initial p₁)
  initial (_>>=_ {false} p₁ p₂) = []
  initial (cast _ p)            = initial p

-- Note that Parser has only one coinductive recursive component.
-- Making any other recursive component coinductive would allow left
-- recursive grammars to be formed, but it is safe to use coinduction
-- in _>>=_ when we know that a token has been consumed, because for
-- every successive use of coinduction we are at least one step closer
-- to the end of the input.
