------------------------------------------------------------------------
-- The parser type
------------------------------------------------------------------------

module StructurallyRecursiveDescentParsing.Type where

open import Data.Bool
open import Data.Empty1
open import Relation.Binary.PropositionalEquality
open import Coinduction

open import StructurallyRecursiveDescentParsing.Index

infixl 10 _!>>=_ _?>>=_
infixl  5 _∣_

-- A type for parsers which can be implemented using recursive
-- descent. The types used ensure that the implemented backends are
-- structurally recursive.

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

  -- If the first parser is guaranteed to consume something, then the
  -- second parser's index can depend on the result of the first
  -- parser.
  _!>>=_ : ∀ {c₁ R₁ R₂} {i₂ : R₁ → Index}
           (p₁ :                Parser NT Tok (false ◇ c₁    ) R₁)
           (p₂ : (x : R₁) → ∞₁ (Parser NT Tok (i₂ x)           R₂)) →
                                Parser NT Tok (false ◇ c₁ ∪ ε) R₂

  !      : ∀ {e c R} (nt : NT (e ◇ c) R) → Parser NT Tok (e ◇ step c) R

-- Note that the definition is almost entirely inductive, only the
-- second argument of _!>>=_ uses coinduction. The reason is that
-- without the use of _!>>=_ it is impossible to create infinite
-- parsers: the Corners type is inductive, and every constructor
-- except for _!>>=_ includes the corners of all its recursive
-- arguments in its own Corners index.

-- Grammars.

Grammar : NonTerminalType → Set → Set1
Grammar NT Tok = ∀ {i R} → NT i R → Parser NT Tok i R

-- An empty non-terminal type.

EmptyNT : NonTerminalType
EmptyNT _ _ = ⊥₁

-- An empty grammar.

emptyGrammar : ∀ {Tok} → Grammar EmptyNT Tok
emptyGrammar ()

-- Instantiates all non-terminals in a parser. Note that the resulting
-- parser does not contain any non-terminals; NT₂ can be instantiated
-- to EmptyNT.

⟦_⟧ : ∀ {Tok NT₁ NT₂ e c R} →
      Parser NT₁ Tok (e ◇ c)            R → Grammar NT₁ Tok →
      Parser NT₂ Tok (e ◇ drop-steps c) R
⟦ return x   ⟧ g = return x
⟦ fail       ⟧ g = fail
⟦ token      ⟧ g = token
⟦ p₁ ∣ p₂    ⟧ g = ⟦ p₁ ⟧ g ∣ ⟦ p₂ ⟧ g
⟦ p₁ ?>>= p₂ ⟧ g = ⟦ p₁ ⟧ g ?>>= λ x →    ⟦     p₂ x  ⟧ g
⟦ p₁ !>>= p₂ ⟧ g = ⟦ p₁ ⟧ g !>>= λ x → ♯₁ ⟦ ♭₁ (p₂ x) ⟧ g
⟦ ! nt       ⟧ g = ⟦ g nt ⟧ g

-- A map function which can be useful when combining grammars.

mapNT : ∀ {NT₁ NT₂ Tok i R} →
        (∀ {i R} → NT₁ i R → NT₂ i R) →
        Parser NT₁ Tok i R → Parser NT₂ Tok i R
mapNT f (return x)   = return x
mapNT f fail         = fail
mapNT f token        = token
mapNT f (p₁ ∣ p₂)    = mapNT f p₁ ∣ mapNT f p₂
mapNT f (p₁ ?>>= p₂) = mapNT f p₁ ?>>= λ x →    mapNT f     (p₂ x)
mapNT f (p₁ !>>= p₂) = mapNT f p₁ !>>= λ x → ♯₁ mapNT f (♭₁ (p₂ x))
mapNT f (! nt)       = ! (f nt)
