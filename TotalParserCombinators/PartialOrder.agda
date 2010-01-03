------------------------------------------------------------------------
-- The relation _⊑_ is a partial order with respect to _≈_
------------------------------------------------------------------------

module TotalParserCombinators.PartialOrder where

open import Function
open import Function.Equivalence using (equivalent)

open import TotalParserCombinators.Parser
open import TotalParserCombinators.Semantics

refl : ∀ {Tok R xs} {p : Parser Tok R xs} → p ⊑ p
refl = id

trans : ∀ {Tok R xs₁ xs₂ xs₃}
          {p₁ : Parser Tok R xs₁}
          {p₂ : Parser Tok R xs₂}
          {p₃ : Parser Tok R xs₃} →
        p₁ ⊑ p₂ → p₂ ⊑ p₃ → p₁ ⊑ p₃
trans p₁⊑p₂ p₂⊑p₃ = p₂⊑p₃ ∘ p₁⊑p₂

antisym : ∀ {Tok R xs₁ xs₂}
            {p₁ : Parser Tok R xs₁}
            {p₂ : Parser Tok R xs₂} →
          p₁ ⊑ p₂ → p₂ ⊑ p₁ → p₁ ≈ p₂
antisym p₁⊑p₂ p₂⊑p₁ = equivalent p₁⊑p₂ p₂⊑p₁
