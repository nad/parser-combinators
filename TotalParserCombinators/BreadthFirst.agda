------------------------------------------------------------------------
-- A breadth-first backend
------------------------------------------------------------------------

-- Similar to Brzozowski's "Derivatives of Regular Expressions".

module TotalParserCombinators.BreadthFirst where

open import TotalParserCombinators.Parser
open import TotalParserCombinators.Congruence as C
open import TotalParserCombinators.Congruence.Sound as CS

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

-- A variant of D-cong.

D-congP : ∀ {k Tok R xs₁ xs₂}
            {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
          p₁ ≈[ k ]P p₂ → ∀ {t} → D t p₁ ≈[ k ]P D t p₂
D-congP p₁≈p₂ = C.complete (D-cong (CS.sound p₁≈p₂))
