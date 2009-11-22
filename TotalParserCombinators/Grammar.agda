------------------------------------------------------------------------
-- Parsers containing non-terminals, and grammars using such parsers
------------------------------------------------------------------------

module TotalParserCombinators.Grammar where

open import Data.Bool
open import Data.Empty1
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Coinduction

open import TotalParserCombinators.Index
import TotalParserCombinators.Simplified as Simplified
open Simplified hiding (Parser; ⟦_⟧)

infixl 10 _!>>=_ _?>>=_
infixl  5 _∣_

-- The parsers are parameterised on a type of nonterminals.

data Parser (NT : NonTerminalType) (Tok : Set) : NonTerminalType where
  return : ∀ {R} (x : R) → Parser NT Tok (true ◇ ε) R

  fail   : ∀ {R} → Parser NT Tok (false ◇ ε) R

  token  : Parser NT Tok (false ◇ ε) Tok

  _∣_    : ∀ {e₁ e₂ c₁ c₂ R}
           (p₁ : Parser NT Tok (e₁      ◇ c₁     ) R)
           (p₂ : Parser NT Tok (     e₂ ◇      c₂) R) →
                 Parser NT Tok (e₁ ∨ e₂ ◇ c₁ ∪ c₂) R

  _?>>=_ : ∀ {e₂ c₁ c₂ R₁ R₂}
           (p₁ :      Parser NT Tok (true ◇ c₁     ) R₁)
           (p₂ : R₁ → Parser NT Tok (e₂   ◇      c₂) R₂) →
                      Parser NT Tok (e₂   ◇ c₁ ∪ c₂) R₂

  _!>>=_ : ∀ {c₁ R₁ R₂} {i₂ : R₁ → Index}
           (p₁ :               Parser NT Tok (false ◇ c₁) R₁)
           (p₂ : ∞ ((x : R₁) → Parser NT Tok (i₂ x)       R₂)) →
                               Parser NT Tok (false ◇ c₁) R₂

  !      : ∀ {e c R} (nt : NT (e ◇ c) R) → Parser NT Tok (e ◇ c ∪ ε) R

-- Grammars.

Grammar : NonTerminalType → Set → Set1
Grammar NT Tok = ∀ {i R} → NT i R → Parser NT Tok i R

-- An empty non-terminal type.

EmptyNT : NonTerminalType
EmptyNT _ _ = ⊥₁

-- An empty grammar.

emptyGrammar : ∀ {Tok} → Grammar EmptyNT Tok
emptyGrammar ()

-- The semantics of grammar-based parsers is defined in terms of their
-- translation into "plain" parsers. The translation instantiates all
-- non-terminals corecursively.

⟦_⟧ : ∀ {Tok NT e c R} →
      Parser NT Tok (e ◇ c) R → Grammar NT Tok →
      Simplified.Parser Tok e R
⟦ return x   ⟧ g = return x
⟦ fail       ⟧ g = fail
⟦ token      ⟧ g = token
⟦ p₁ ∣ p₂    ⟧ g = ⟦ p₁ ⟧ g ∣ ⟦ p₂ ⟧ g
⟦ p₁ ?>>= p₂ ⟧ g = ⟦ p₁ ⟧ g ?>>=   λ x → ⟦   p₂ x ⟧ g
⟦ p₁ !>>= p₂ ⟧ g = ⟦ p₁ ⟧ g !>>= ♯ λ x → ⟦ ♭ p₂ x ⟧ g
⟦ ! nt       ⟧ g = ⟦ g nt ⟧ g

-- Note that some "plain" parsers cannot be directly rewritten using
-- the parser type in this module (although there may be /equivalent/
-- parsers):

private

  only-plain : Simplified.Parser Bool false Bool
  only-plain = return true ?>>= λ x →
               if x then token else token ∣ token

  -- The following code does not type-check.

  -- doesnt-work : Parser EmptyNT Bool (false ◇ _) Bool
  -- doesnt-work = return true ?>>= λ x →
  --               if x then token else token ∣ token

-- A map function which can be useful when combining grammars.

mapNT : ∀ {NT₁ NT₂ Tok i R} →
        (∀ {i R} → NT₁ i R → NT₂ i R) →
        Parser NT₁ Tok i R → Parser NT₂ Tok i R
mapNT f (return x)   = return x
mapNT f fail         = fail
mapNT f token        = token
mapNT f (p₁ ∣ p₂)    = mapNT f p₁ ∣ mapNT f p₂
mapNT f (p₁ ?>>= p₂) = mapNT f p₁ ?>>=   λ x → mapNT f   (p₂ x)
mapNT f (p₁ !>>= p₂) = mapNT f p₁ !>>= ♯ λ x → mapNT f (♭ p₂ x)
mapNT f (! nt)       = ! (f nt)
