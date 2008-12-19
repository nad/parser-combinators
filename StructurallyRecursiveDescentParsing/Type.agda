------------------------------------------------------------------------
-- The parser type
------------------------------------------------------------------------

module StructurallyRecursiveDescentParsing.Type where

open import Data.Bool
open import Relation.Binary.PropositionalEquality

open import StructurallyRecursiveDescentParsing.Index

infix  60 !_
infixl 40 _∣_
infixl 10 _!>>=_ _?>>=_

-- A type for parsers which can be implemented using recursive
-- descent. The types used ensure that the implemented backends are
-- structurally recursive.

-- The parsers are indexed on a type of nonterminals.

codata Parser (Tok : Set) (NT : NonTerminalType) :
              NonTerminalType where
  return : ∀ {R} (x : R) → Parser Tok NT (true ◇ leaf) R

  fail   : ∀ {R} → Parser Tok NT (false ◇ leaf) R

  token  : Parser Tok NT (false ◇ leaf) Tok

  _∣_    : ∀ {e₁ e₂ c₁ c₂ R}
           (p₁ : Parser Tok NT (e₁      ◇ c₁)         R)
           (p₂ : Parser Tok NT (e₂      ◇ c₂)         R) →
                 Parser Tok NT (e₁ ∨ e₂ ◇ node c₁ c₂) R

  _?>>=_ : ∀ {c₁ e₂ c₂ R₁ R₂}
           (p₁ : Parser Tok NT (true ◇ c₁) R₁)
           (p₂ : R₁ → Parser Tok NT (e₂ ◇ c₂) R₂) →
           Parser Tok NT (e₂ ◇ node c₁ c₂) R₂

  -- If the first parser is guaranteed to consume something, then the
  -- second parser's index can depend on the result of the first
  -- parser.
  _!>>=_ : ∀ {c₁ R₁ R₂} {i₂ : R₁ → Index}
           (p₁ : Parser Tok NT (false ◇ c₁) R₁)
           (p₂ : (x : R₁) → Parser Tok NT (i₂ x) R₂) →
           Parser Tok NT (false ◇ step c₁) R₂

  !_     : ∀ {e c R} (nt : NT (e ◇ c) R) → Parser Tok NT (e ◇ step c) R

-- Grammars.

Grammar : Set → NonTerminalType → Set1
Grammar Tok NT = ∀ {i R} → NT i R → Parser Tok NT i R

-- A map function which is useful when combining grammars.

mapNT : ∀ {Tok NT₁ NT₂ i R} →
        (∀ {i R} → NT₁ i R → NT₂ i R) →
        Parser Tok NT₁ i R → Parser Tok NT₂ i R
mapNT f (return x)   ~ return x
mapNT f fail         ~ fail
mapNT f token        ~ token
mapNT f (p₁ ∣ p₂)    ~ mapNT f p₁ ∣ mapNT f p₂
mapNT f (p₁ ?>>= p₂) ~ mapNT f p₁ ?>>= λ x → mapNT f (p₂ x)
mapNT f (p₁ !>>= p₂) ~ mapNT f p₁ !>>= λ x → mapNT f (p₂ x)
mapNT f (! nt)       ~ ! f nt
