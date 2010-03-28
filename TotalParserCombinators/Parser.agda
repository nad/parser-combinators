------------------------------------------------------------------------
-- The parser type
------------------------------------------------------------------------

module TotalParserCombinators.Parser where

open import Category.Monad
open import Coinduction
open import Data.List as List
import Data.List.Any as Any
open import Function

open Any.Membership-≡
open RawMonadPlus List.monadPlus
  using ()
  renaming ( return to return′
           ; ∅      to fail′
           ; _∣_    to _∣′_
           ; _>>=_  to _>>=′_
           )

open import TotalParserCombinators.Applicative using (_⊛′_)
open import TotalParserCombinators.Coinduction

------------------------------------------------------------------------
-- Parsers

infixl 50 _⊛_ _<$>_
infixl 10 _>>=_ _>>=!_
infixl  5 _∣_

-- The list index is the "initial bag"; it contains the results which
-- can be emitted without consuming any input. For
--   p : Parser Tok R xs
-- we have
--   x ∈ xs  iff  x ∈ p · []
-- (see TotalParserCombinators.InitialBag).

data Parser (Tok : Set) : (R : Set) → List R → Set₁ where
  return   : ∀ {R} (x : R) → Parser Tok R (return′ x)
  fail     : ∀ {R} → Parser Tok R fail′
  token    : Parser Tok Tok fail′
  _∣_      : ∀ {R xs₁ xs₂}
             (p₁ : Parser Tok R  xs₁       )
             (p₂ : Parser Tok R         xs₂) →
                   Parser Tok R (xs₁ ∣′ xs₂)
  _<$>_    : ∀ {R₁ R₂ xs}
             (f : R₁ → R₂)
             (p : Parser Tok R₁        xs) →
                  Parser Tok R₂ (map f xs)
  _⊛_      : ∀ {R₁ R₂ fs xs}
             (p₁ : ∞? (Parser Tok (R₁ → R₂)  fs      ) xs)
             (p₂ : ∞? (Parser Tok  R₁              xs) fs) →
                       Parser Tok       R₂  (fs ⊛′ xs)
  _>>=_    : ∀ {R₁ R₂ xs} {f : R₁ → List R₂}
             (p₁ :                Parser Tok R₁  xs              )
             (p₂ : (x : R₁) → ∞? (Parser Tok R₂         (f x)) xs) →
                                  Parser Tok R₂ (xs >>=′ f)
  _>>=!_   : ∀ {R₁ R₂ xs}
             (p₁ :      ∞  (Parser Tok R₁ xs))
             (p₂ : R₁ → ∞? (Parser Tok R₂ fail′) xs) →
                            Parser Tok R₂ fail′
  nonempty : ∀ {R xs} (p : Parser Tok R xs) → Parser Tok R []
  cast     : ∀ {R xs₁ xs₂} (xs₁≈xs₂ : xs₁ ≈[ bag ] xs₂)
             (p : Parser Tok R xs₁) → Parser Tok R xs₂

-- The difference between the _>>=_ and _>>=!_ combinators is that the
-- latter one accepts a delayed left parser, but requires the index of
-- the right parser to be fail′ ([]). Another option would perhaps be
-- to require the index to be a function f such that f x ≡ [] for all
-- x in xs, but this seems complicated.

-- The initial bag of a parser:

initial-bag : ∀ {R Tok xs} → Parser Tok R xs → List R
initial-bag {xs = xs} _ = xs

-- Note that these parsers can be both left and right recursive:

private

  leftRight : ∀ {R Tok} → Parser Tok R []
  leftRight {R} = ⟪ ♯ (const <$> leftRight) ⟫ ⊛ ⟪ ♯ leftRight {R} ⟫
