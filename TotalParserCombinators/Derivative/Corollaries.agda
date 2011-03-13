------------------------------------------------------------------------
-- Some corollaries
------------------------------------------------------------------------

module TotalParserCombinators.Derivative.Corollaries where

open import Data.List
open import Function
open import Function.Inverse using (_↔_)
import Function.Related as Related
import Relation.Binary.PropositionalEquality as P

open import TotalParserCombinators.Derivative.Definition
open import TotalParserCombinators.Derivative.LeftInverse
open import TotalParserCombinators.Derivative.RightInverse
open import TotalParserCombinators.Derivative.SoundComplete
open import TotalParserCombinators.Parser
open import TotalParserCombinators.Semantics

-- D is correct.

correct : ∀ {Tok R xs x s} {t} {p : Parser Tok R xs} →
          x ∈ D t p · s ↔ x ∈ p · t ∷ s
correct {p = p} = record
  { to         = P.→-to-⟶ $ sound p
  ; from       = P.→-to-⟶ complete
  ; inverse-of = record
    { left-inverse-of  = complete∘sound p
    ; right-inverse-of = sound∘complete
    }
  }

-- D is monotone.

mono : ∀ {Tok R xs₁ xs₂ t}
         {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
       p₁ ≲ p₂ → D t p₁ ≲ D t p₂
mono p₁≲p₂ = complete ∘ p₁≲p₂ ∘ sound _

-- D preserves parser and language equivalence.

cong : ∀ {k Tok R xs₁ xs₂}
         {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
       p₁ ≈[ k ] p₂ → ∀ {t} → D t p₁ ≈[ k ] D t p₂
cong {p₁ = p₁} {p₂} p₁≈p₂ {t} {x} {s} =
  x ∈ D t p₁ · s  ↔⟨ correct ⟩
  x ∈ p₁ · t ∷ s  ≈⟨ p₁≈p₂ ⟩
  x ∈ p₂ · t ∷ s  ↔⟨ sym correct ⟩
  x ∈ D t p₂ · s  ∎
  where open Related.EquationalReasoning
