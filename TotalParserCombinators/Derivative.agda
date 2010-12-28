------------------------------------------------------------------------
-- A derivative operator for parsers
------------------------------------------------------------------------

-- Similar to the derivative operator in Brzozowski's "Derivatives of
-- Regular Expressions".

module TotalParserCombinators.Derivative where

-- Definition of the derivative.

open import TotalParserCombinators.Derivative.Definition public

-- The derivative operator is sound and complete with respect to the
-- semantics.

open import TotalParserCombinators.Derivative.SoundComplete public
  hiding (complete′)

-- A proof showing that the derivative operator does not introduce any
-- unneeded ambiguity.

open import TotalParserCombinators.Derivative.LeftInverse public

-- A proof showing that the derivative operator does not remove any
-- ambiguity.

open import TotalParserCombinators.Derivative.RightInverse public
  hiding (sound∘complete′)

-- Some corollaries.

open import TotalParserCombinators.Derivative.Corollaries public
