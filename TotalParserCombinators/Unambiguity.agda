------------------------------------------------------------------------
-- Unambiguity
------------------------------------------------------------------------

module TotalParserCombinators.Unambiguity where

open import Data.Product
open import Function using (_$_)
open import Function.Equivalence
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality as H
  renaming (_≅_ to _≅′_)

open import TotalParserCombinators.Parser
open import TotalParserCombinators.Semantics

-- A parser is unambiguous if every string can be parsed in at most
-- one way.

Unambiguous : ∀ {Tok R xs} → Parser Tok R xs → Set1
Unambiguous p =
  ∀ {x₁ x₂ s} (x₁∈p : x₁ ∈ p · s) (x₂∈p : x₂ ∈ p · s) →
  x₁ ≡ x₂ × x₁∈p ≅′ x₂∈p

-- Language and parser equivalence coincide for unambiguous parsers.

≈⇒≅ : ∀ {Tok R xs₁ xs₂}
        {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
      Unambiguous p₁ → Unambiguous p₂ → p₁ ≈ p₂ → p₁ ≅ p₂
≈⇒≅ u₁ u₂ p₁≈p₂ = record
  { to         = Equivalent.to   p₁≈p₂
  ; from       = Equivalent.from p₁≈p₂
  ; inverse-of = record
    { left-inverse-of  = λ x∈p₁ → H.≅-to-≡ $ proj₂ $ u₁ _ x∈p₁
    ; right-inverse-of = λ x∈p₂ → H.≅-to-≡ $ proj₂ $ u₂ _ x∈p₂
    }
  }
