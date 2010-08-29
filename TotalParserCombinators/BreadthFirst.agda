------------------------------------------------------------------------
-- A breadth-first backend
------------------------------------------------------------------------

-- Similar to Brzozowski's "Derivatives of Regular Expressions".

module TotalParserCombinators.BreadthFirst where

-- Definition of the derivative and the parser backend.

open import TotalParserCombinators.BreadthFirst.Derivative public
  using (D; D-bag; parse)

-- The parser is sound and complete with respect to the semantics.

open import TotalParserCombinators.BreadthFirst.SoundComplete public
  using (sound; complete; D-sound; D-complete)

-- A proof showing that the breadth-first backend does not introduce
-- any unneeded ambiguity.

open import TotalParserCombinators.BreadthFirst.LeftInverse public
  using (complete∘sound)

-- A proof showing that the breadth-first backend does not remove any
-- ambiguity.

open import TotalParserCombinators.BreadthFirst.RightInverse public
  using (sound∘complete)

-- Some additional lemmas.

open import TotalParserCombinators.BreadthFirst.Lemmas public
