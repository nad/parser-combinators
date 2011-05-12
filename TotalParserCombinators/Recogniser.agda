------------------------------------------------------------------------
-- Recognisers built on top of the parsers
------------------------------------------------------------------------

-- Note that these recognisers are different from the ones in
-- TotalRecognisers.LeftRecursion: these allow the use of fewer sharps.
-- (Compare the examples in TotalRecognisers.LeftRecursion.Expression
-- and TotalParserCombinators.Recogniser.Expression.)

module TotalParserCombinators.Recogniser where

open import Category.Monad
open import Coinduction
open import Data.Bool
open import Data.List as List
open import Data.Maybe
open import Data.Unit
open import Level

open RawMonadPlus {f = zero} List.monadPlus
  using () renaming (_⊛_ to _⊛′_)

open import TotalParserCombinators.Parser as Parser
  using (Parser; flatten); open Parser.Parser
import TotalParserCombinators.Lib as Lib

------------------------------------------------------------------------
-- Helper function

infixl 4 _·′_

_·′_ : (mb₁ mb₂ : Maybe (List ⊤)) → List ⊤
mb₁ ·′ nothing = []
mb₁ ·′ just b₂ = List.map _ (flatten mb₁) ⊛′ b₂

------------------------------------------------------------------------
-- Recognisers

infixl 50 _·_
infixl  5 _∣_

-- Recognisers.

mutual

  -- The index is non-empty if the corresponding language contains the
  -- empty string (is nullable).

  data P (Tok : Set) : List ⊤ → Set₁ where
    -- Parsers can be turned into recognisers.
    lift  : ∀ {R n} (p : Parser Tok R n) → P Tok (List.map _ n)

    -- Symmetric choice.
    _∣_   : ∀ {n₁ n₂}
            (p₁ : P Tok n₁) (p₂ : P Tok n₂) → P Tok (n₁ ++ n₂)

    -- Sequencing.
    _·_   : ∀ {n₁ n₂}
            (p₁ : ∞⟨ n₂ ⟩P Tok (flatten n₁))
            (p₂ : ∞⟨ n₁ ⟩P Tok (flatten n₂)) →
            P Tok (n₁ ·′ n₂)

  -- Delayed if the index is /nothing/.

  ∞⟨_⟩P : Maybe (List ⊤) → Set → List ⊤ → Set₁
  ∞⟨ nothing ⟩P Tok n = ∞ (P Tok n)
  ∞⟨ just _  ⟩P Tok n =    P Tok n

------------------------------------------------------------------------
-- Helper function related to ∞⟨_⟩P

-- Is the argument parser forced? If the result is just something,
-- then it is.

forced? : ∀ {Tok m n} → ∞⟨ m ⟩P Tok n → Maybe (List ⊤)
forced? {m = m} _ = m

------------------------------------------------------------------------
-- The semantics of the recognisers is defined by translation

⟦_⟧ : ∀ {Tok n} (p : P Tok n) → Parser Tok ⊤ n
⟦ lift p ⟧  = _ <$> p
⟦ p₁ ∣ p₂ ⟧ = ⟦ p₁ ⟧ ∣ ⟦ p₂ ⟧
⟦ p₁ · p₂ ⟧ with forced? p₁ | forced? p₂
... | just xs | nothing =    _ <$> ⟦   p₁ ⟧  ⊛ ♯ ⟦ ♭ p₂ ⟧
... | just xs | just ys =    _ <$> ⟦   p₁ ⟧  ⊛   ⟦   p₂ ⟧
... | nothing | nothing = ♯ (_ <$> ⟦ ♭ p₁ ⟧) ⊛ ♯ ⟦ ♭ p₂ ⟧
... | nothing | just ys = ♯ (_ <$> ⟦ ♭ p₁ ⟧) ⊛   ⟦   p₂ ⟧
