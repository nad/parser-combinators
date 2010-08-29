------------------------------------------------------------------------
-- Some additional lemmas
------------------------------------------------------------------------

module TotalParserCombinators.BreadthFirst.Lemmas where

open import Data.List
import Data.List.Any as Any
open import Data.Product as Prod
open import Function
open import Function.Inverse as Inv using (_⇿_)
open import Relation.Binary.HeterogeneousEquality as H using (_≅_)
import Relation.Binary.PropositionalEquality as P

open Any.Membership-≡ using (_∈_)

open import TotalParserCombinators.Parser
open import TotalParserCombinators.Semantics hiding (_≅_)
open import TotalParserCombinators.BreadthFirst.Derivative
open import TotalParserCombinators.BreadthFirst.SoundComplete
open import TotalParserCombinators.BreadthFirst.LeftInverse
open import TotalParserCombinators.BreadthFirst.RightInverse

------------------------------------------------------------------------
-- Lemmas about the derivative

-- D is correct.

D-correct : ∀ {Tok R xs x s} {t} {p : Parser Tok R xs} →
            x ∈ D t p · s ⇿ x ∈ p · t ∷ s
D-correct {p = p} = record
  { to         = P.→-to-⟶ $ D-sound p
  ; from       = P.→-to-⟶ D-complete
  ; inverse-of = record
    { left-inverse-of  = D-complete∘D-sound p
    ; right-inverse-of = D-sound∘D-complete
    }
  }

-- D is monotone.

D-mono : ∀ {Tok R xs₁ xs₂ t}
           {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
         p₁ ≲ p₂ → D t p₁ ≲ D t p₂
D-mono p₁≲p₂ = D-complete ∘ p₁≲p₂ ∘ D-sound _

-- D preserves parser and language equivalence.

D-cong : ∀ {k Tok R xs₁ xs₂}
           {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
         p₁ ≈[ k ] p₂ → ∀ {t} → D t p₁ ≈[ k ] D t p₂
D-cong {p₁ = p₁} {p₂} p₁≈p₂ {t} {x} {s} =
  x ∈ D t p₁ · s  ⇿⟨ D-correct ⟩
  x ∈ p₁ · t ∷ s  ≈⟨ p₁≈p₂ ⟩
  x ∈ p₂ · t ∷ s  ⇿⟨ sym D-correct ⟩
  x ∈ D t p₂ · s  ∎
  where open Inv.EquationalReasoning

------------------------------------------------------------------------
-- Lemmas about the backend

-- The backend is correct.

correct : ∀ {Tok R xs x s} {p : Parser Tok R xs} →
          x ∈ p · s ⇿ x ∈ parse p s
correct {s = s} {p} = record
  { to         = P.→-to-⟶ $ complete s
  ; from       = P.→-to-⟶ $ sound s
  ; inverse-of = record
    { left-inverse-of  = sound∘complete s
    ; right-inverse-of = complete∘sound s p
    }
  }

-- The worst-case complexity of the backend is /at least/ exponential
-- in the size of the input string. There is a (finite) parser p whose
-- derivative is p ∣ p (for any token). The n-th derivative thus
-- contains (at least) 2^n outermost occurrences of _∣_, and these
-- occurrences have to be traversed to compute the initial bag of the
-- n-th derivative.

inefficient : ∀ {Tok R} →
              ∃ λ (p : Parser Tok R []) → ∀ t → D t p ≅ p ∣ p
inefficient {R = R} = (fail {R = R} >>= (λ _ → fail) , λ t → H.refl)
