------------------------------------------------------------------------
-- The parser type
------------------------------------------------------------------------

module StructurallyRecursiveDescentParsing.Parser where

open import Category.Monad
open import Coinduction
open import Data.Bool
open import Data.List as List
open RawMonadPlus List.monadPlus
  using ()
  renaming ( return to return′
           ; ∅      to fail′
           ; _∣_    to _∣′_
           ; _>>=_  to _>>=′_
           ; _<$>_  to _<$>′_
           )
open import Data.Function
open import Relation.Binary.PropositionalEquality

open import StructurallyRecursiveDescentParsing.Coinduction

------------------------------------------------------------------------
-- A variant of _⊛_ (for lists)

-- This function has the property that fs ⊛′ [] evaluates to [].

infixl 50 _⊛′_

_⊛′_ : ∀ {A B} → List (A → B) → List A → List B
fs ⊛′ xs = xs >>=′ λ x → map (λ f → f x) fs

------------------------------------------------------------------------
-- Parsers

infixl 50 _⊛_
infixl 10 _>>=_
infixl  5 _∣_

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
  _⊛_    : ∀ {R₁ R₂ fs xs}
           (p₁ : ∞? (null xs) (Parser Tok (R₁ → R₂)  fs      ))
           (p₂ :               Parser Tok  R₁              xs) →
                               Parser Tok       R₂  (fs ⊛′ xs)
  _>>=_  : ∀ {R₁ R₂} {xs} {f : R₁ → List R₂}
           (p₁ :                          Parser Tok R₁  xs)
           (p₂ : (x : R₁) → ∞? (null xs) (Parser Tok R₂         (f x))) →
                                          Parser Tok R₂ (xs >>=′ f)
  cast   : ∀ {R xs₁ xs₂}
           (eq : xs₁ ≡ xs₂) (p : Parser Tok R xs₁) → Parser Tok R xs₂

-- Note that it would be reasonable to generalise the casts to accept
-- /set/ equality instead of just list equality. However, I have not
-- yet found a use for this generalisation.

-- Note also that these parsers can be both left and right recursive:

private

  leftRight : ∀ {Tok} → Parser Tok (Tok → Tok) _
  leftRight = (♯₁ leftRight) ⊛ token >>= λ _ → ♯₁ leftRight
