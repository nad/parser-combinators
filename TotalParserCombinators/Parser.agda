------------------------------------------------------------------------
-- The parser type
------------------------------------------------------------------------

module TotalParserCombinators.Parser where

open import Category.Monad
open import Coinduction
open import Data.List as List
open import Data.Maybe as Maybe using (Maybe)
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
-- Some helper functions

-- Applies the function to the value, returning the empty list if
-- there is no function.

app : {A B : Set} → Maybe (A → List B) → A → List B
app = Maybe.maybe id (const [])

-- xs >>=app f is a variant of xs >>=′ app f, with the property that
-- xs >>=app nothing evaluates to [].

_>>=app_ : {A B : Set} → List A → Maybe (A → List B) → List B
xs >>=app f = Maybe.maybe (_>>=′_ xs) [] f

------------------------------------------------------------------------
-- Parsers

infixl 50 _⊛_ _<$>_
infixl 10 _>>=_
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
  _>>=_    : ∀ {R₁ R₂ xs} {f : Maybe (R₁ → List R₂)}
             (p₁ :            ∞? (Parser Tok R₁  xs            ) f)
             (p₂ : (x : R₁) → ∞? (Parser Tok R₂       (app f x)) xs) →
                                  Parser Tok R₂ (xs >>=app f)
  nonempty : ∀ {R xs} (p : Parser Tok R xs) → Parser Tok R []
  cast     : ∀ {R xs₁ xs₂} (xs₁≈xs₂ : xs₁ ≈[ bag ] xs₂)
             (p : Parser Tok R xs₁) → Parser Tok R xs₂

-- Comment related to _>>=_: It is safe to make the first argument
-- coinductive if f x ≡_[] for all x in xs. I suspect that this
-- criterion would be awkward to work with, though. Instead I have
-- added an extra element to the function space, using Maybe. This
-- element (nothing) represents const [], and the first argument is
-- only coinductive if f ≡ nothing.

-- The initial bag of a parser:

initial-bag : ∀ {R Tok xs} → Parser Tok R xs → List R
initial-bag {xs = xs} _ = xs

-- Note that these parsers can be both left and right recursive:

private

  leftRight : ∀ {R Tok} → Parser Tok R []
  leftRight {R} = ⟪ ♯ (const <$> leftRight) ⟫ ⊛ ⟪ ♯ leftRight {R} ⟫

  leftRight′ : ∀ {R Tok} → Parser Tok R []
  leftRight′ {R} = ⟪ ♯ leftRight′ {R} ⟫ >>= λ _ → ⟪ ♯ leftRight′ ⟫
