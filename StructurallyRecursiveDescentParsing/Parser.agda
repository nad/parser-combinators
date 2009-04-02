------------------------------------------------------------------------
-- The parser type
------------------------------------------------------------------------

module StructurallyRecursiveDescentParsing.Parser where

open import Category.Monad
open import Data.Bool
open import Data.List as List
open RawMonadPlus List.monadPlus
  using ()
  renaming ( return to return′
           ; ∅      to fail′
           ; _∣_    to _∣′_
           ; _>>=_  to _>>=′_
           )
open import Data.Function
open import Relation.Binary.PropositionalEquality

open import StructurallyRecursiveDescentParsing.Coinduction

infixl 10 _>>=_
infixl  5 _∣_

-- A type for parsers which are not left recursive.
--
-- The list index is the "initial set"; it contains the results which
-- can be emitted without consuming any input. For
--   p : Parser Tok R xs
-- we have
--   x ∈ xs  iff  x ∈ p · []
-- (see StructurallyRecursiveDescentParsing.Parser.Semantics).

data Parser (Tok : Set) : (R : Set) → List R → Set1 where
  return : ∀ {R} (x : R) → Parser Tok R (return′ x)
  fail   : ∀ {R} → Parser Tok R fail′
  token  : Parser Tok Tok fail′
  _∣_    : ∀ {R xs₁ xs₂}
           (p₁ : Parser Tok R  xs₁       )
           (p₂ : Parser Tok R         xs₂) →
                 Parser Tok R (xs₁ ∣′ xs₂)
  _>>=_  : ∀ {R₁ R₂} {xs} {f : R₁ → List R₂}
           (p₁ :                          Parser Tok R₁  xs)
           (p₂ : (x : R₁) → ∞? (null xs) (Parser Tok R₂         (f x))) →
                                          Parser Tok R₂ (xs >>=′ f)
  cast   : ∀ {R xs₁ xs₂}
           (eq : xs₁ ≡ xs₂) (p : Parser Tok R xs₁) → Parser Tok R xs₂

-- Note that Parser has only one coinductive recursive component.
-- Making any other recursive component coinductive would allow left
-- recursive grammars to be formed, but it is safe to use coinduction
-- in _>>=_ when we know that a token has been consumed, because for
-- every successive use of coinduction we are at least one step closer
-- to the end of the input.

-- Note also that it would be reasonable to generalise the casts to
-- accept /set/ equality instead of just list equality. However, I
-- have not yet found a use for this generalisation.
