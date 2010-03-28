------------------------------------------------------------------------
-- Some additional lemmas
------------------------------------------------------------------------

module TotalParserCombinators.BreadthFirst.Lemmas where

open import Data.List
import Data.List.Any as Any
open import Data.Product as Prod
open import Function
open import Function.Inverse as Inv using (_⇿_)
import Relation.Binary.PropositionalEquality as P

open Any.Membership-≡ using (_∈_)

open import TotalParserCombinators.Parser
open import TotalParserCombinators.Semantics
open import TotalParserCombinators.BreadthFirst.Derivative
open import TotalParserCombinators.BreadthFirst.SoundComplete
open import TotalParserCombinators.BreadthFirst.LeftInverse
open import TotalParserCombinators.BreadthFirst.RightInverse

------------------------------------------------------------------------
-- Lemmas about the backend

-- The backend is correct.

correct : ∀ {Tok R xs x s} {p : Parser Tok R xs} →
          x ∈ p · s ⇿ x ∈ parseComplete p s
correct {s = s} {p} = record
  { to         = P.→-to-⟶ $ complete s
  ; from       = P.→-to-⟶ $ sound s
  ; inverse-of = record
    { left-inverse-of  = sound∘complete s
    ; right-inverse-of = complete∘sound s p
    }
  }

------------------------------------------------------------------------
-- Lemmas about the derivative

-- ∂ is correct.

∂-correct : ∀ {Tok R xs x s} {t} {p : Parser Tok R xs} →
            x ∈ ∂ p t · s ⇿ x ∈ p · t ∷ s
∂-correct {p = p} = record
  { to         = P.→-to-⟶ $ ∂-sound p
  ; from       = P.→-to-⟶ ∂-complete
  ; inverse-of = record
    { left-inverse-of  = ∂-complete∘∂-sound p
    ; right-inverse-of = ∂-sound∘∂-complete
    }
  }

-- ∂ is monotone.

∂-mono : ∀ {Tok R xs₁ xs₂ t}
           {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
         p₁ ≲ p₂ → ∂ p₁ t ≲ ∂ p₂ t
∂-mono p₁≲p₂ = ∂-complete ∘ p₁≲p₂ ∘ ∂-sound _

-- ∂ preserves parser and language equivalence.

∂-cong : ∀ {k Tok R xs₁ xs₂}
           {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
         p₁ ≈[ k ] p₂ → ∀ {t} → ∂ p₁ t ≈[ k ] ∂ p₂ t
∂-cong {p₁ = p₁} {p₂} p₁≈p₂ {t} {x} {s} =
  x ∈ ∂ p₁ t · s  ⇿⟨ ∂-correct ⟩
  x ∈ p₁ · t ∷ s  ≈⟨ p₁≈p₂ ⟩
  x ∈ p₂ · t ∷ s  ⇿⟨ sym ∂-correct ⟩
  x ∈ ∂ p₂ t · s  ∎
  where open Inv.EquationalReasoning
