------------------------------------------------------------------------
-- Some additional lemmas
------------------------------------------------------------------------

module TotalParserCombinators.BreadthFirst.Lemmas where

open import Data.List
import Data.List.Any as Any
open import Data.Product as Prod
open import Function
open import Function.Equivalence as Eq
  using (module Equivalent) renaming (_∘_ to _⟨∘⟩_)
open import Function.Inverse as Inv
  using (_⇿_; module Inverse) renaming (_∘_ to _⟪∘⟫_)
import Relation.Binary.PropositionalEquality as P

open Any.Membership-≡

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
          (x ∈ parseComplete p s) ⇿ x ∈ p · s
correct {s = s} {p} = record
  { to         = P.→-to-⟶ $ sound s
  ; from       = P.→-to-⟶ $ complete s
  ; inverse-of = record
    { left-inverse-of  = complete∘sound s p
    ; right-inverse-of = sound∘complete s
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
         p₁ ⊑ p₂ → ∂ p₁ t ⊑ ∂ p₂ t
∂-mono p₁⊑p₂ = ∂-complete ∘ p₁⊑p₂ ∘ ∂-sound _

-- ∂ preserves language equivalence.

∂-cong-≈ : ∀ {Tok R xs₁ xs₂ t}
             {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
           p₁ ≈ p₂ → ∂ p₁ t ≈ ∂ p₂ t
∂-cong-≈ p₁≈p₂ =
  Eq.sym (Inverse.equivalent ∂-correct) ⟨∘⟩
  p₁≈p₂ ⟨∘⟩
  Inverse.equivalent ∂-correct

-- ∂ preserves parser equivalence.

∂-cong-≅ : ∀ {Tok R xs₁ xs₂ t}
             {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
           p₁ ≅ p₂ → ∂ p₁ t ≅ ∂ p₂ t
∂-cong-≅ p₁≅p₂ = Inv.sym ∂-correct ⟪∘⟫ p₁≅p₂ ⟪∘⟫ ∂-correct
