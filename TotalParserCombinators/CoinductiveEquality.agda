------------------------------------------------------------------------
-- An alternative definition of equality
------------------------------------------------------------------------

module TotalParserCombinators.CoinductiveEquality where

open import Coinduction
open import Data.List
import Data.List.Any as Any
open import Data.Product
open import Function.Equivalence as Eq
  using (_⇔_) renaming (_∘_ to _⟨∘⟩_)
open import Function.Inverse using (module Inverse)
open import Relation.Binary

private
  open module SetEq {R : Set} =
    Setoid (Any.Membership-≡.Set-equality {R})
      using () renaming (_≈_ to _≛_)

open import TotalParserCombinators.Parser
open import TotalParserCombinators.Semantics
import TotalParserCombinators.InitialSet as I
open import TotalParserCombinators.BreadthFirst
  hiding (sound; complete; correct)

infix 5 _∷_
infix 4 _≈′_

-- Two recognisers/languages are equal if their nullability indices
-- are equal (as sets) and all their derivatives are equal
-- (coinductively). Note that the inhabitants of this type are
-- bisimulations.

data _≈′_ {Tok R xs₁ xs₂}
          (p₁ : Parser Tok R xs₁) (p₂ : Parser Tok R xs₂) : Set where
  _∷_ : (init : xs₁ ≛ xs₂) (rest : ∀ t → ∞ (∂ p₁ t ≈′ ∂ p₂ t)) →
        p₁ ≈′ p₂

-- This equality coincides with _≈_.

sound : ∀ {Tok R xs₁ xs₂}
          {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
        p₁ ≈′ p₂ → p₁ ≈ p₂
sound (xs₁≛xs₂ ∷ rest) {s = []} =
  Eq.sym (Inverse.equivalence I.correct) ⟨∘⟩
  xs₁≛xs₂ ⟨∘⟩
  Inverse.equivalence I.correct
sound (xs₁≛xs₂ ∷ rest) {s = t ∷ s} =
  Inverse.equivalence ∂-correct ⟨∘⟩
  sound (♭ (rest t)) ⟨∘⟩
  Eq.sym (Inverse.equivalence ∂-correct)

complete : ∀ {Tok R xs₁ xs₂}
             {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
           p₁ ≈ p₂ → p₁ ≈′ p₂
complete p₁≈p₂ = I.same-set p₁≈p₂ ∷ λ t → ♯ complete (∂-cong p₁≈p₂)

correct : ∀ {Tok R xs₁ xs₂}
            {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
          p₁ ≈′ p₂ ⇔ p₁ ≈ p₂
correct = Eq.equivalent sound complete
