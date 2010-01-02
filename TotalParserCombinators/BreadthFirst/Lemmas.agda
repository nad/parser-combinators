------------------------------------------------------------------------
-- Some additional lemmas
------------------------------------------------------------------------

module TotalParserCombinators.BreadthFirst.Lemmas where

open import Data.Product as Prod
open import Function

open import TotalParserCombinators.Parser
open import TotalParserCombinators.Semantics
open import TotalParserCombinators.BreadthFirst.Derivative
open import TotalParserCombinators.BreadthFirst.Correct

-- ∂ is monotone.

∂-mono : ∀ {Tok R xs₁ xs₂ t}
           {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
         p₁ ⊑ p₂ → ∂ p₁ t ⊑ ∂ p₂ t
∂-mono p₁⊑p₂ = ∂-complete ∘ p₁⊑p₂ ∘ ∂-sound _

-- ∂ preserves language equality.

∂-cong : ∀ {Tok R xs₁ xs₂ t}
           {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
         p₁ ≈ p₂ → ∂ p₁ t ≈ ∂ p₂ t
∂-cong = Prod.map ∂-mono ∂-mono
