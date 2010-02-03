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
open import Function.Inverse as Inv
  using (module Inverse) renaming (_∘_ to _⟪∘⟫_)
open import Relation.Binary

private
  module SetEq {R : Set} = Setoid (Any.Membership-≡.Set-equality {R})
  module BagEq {R : Set} = Setoid (Any.Membership-≡.Bag-equality {R})

open import TotalParserCombinators.Parser
open import TotalParserCombinators.Semantics
import TotalParserCombinators.InitialSet as I
open import TotalParserCombinators.BreadthFirst
  hiding (sound; complete; correct)

infix 5 _∷_

-- Two recognisers/languages are equal if their nullability indices
-- are equal (according to _∼_) and all their derivatives are equal
-- (coinductively). Note that the inhabitants of this type are
-- bisimulations.

data Eq {Tok R xs₁ xs₂} (_∼_ : List R → List R → Set)
        (p₁ : Parser Tok R xs₁) (p₂ : Parser Tok R xs₂) :
        Set where
  _∷_ : (init : xs₁ ∼ xs₂)
        (rest : ∀ t → ∞ (Eq _∼_ (∂ p₁ t) (∂ p₂ t))) →
        Eq _∼_ p₁ p₂

------------------------------------------------------------------------
-- Language equivalence

infix 4 _≈′_

_≈′_ : ∀ {Tok R xs₁ xs₂} → Parser Tok R xs₁ → Parser Tok R xs₂ → Set
_≈′_ = Eq SetEq._≈_

-- The two definitions of language equivalence are equivalent.

module LanguageEquivalence where

  sound : ∀ {Tok R xs₁ xs₂}
            {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
          p₁ ≈′ p₂ → p₁ ≈ p₂
  sound (xs₁≈xs₂ ∷ rest) {s = []} =
    Eq.sym (Inverse.equivalent I.correct) ⟨∘⟩
    xs₁≈xs₂ ⟨∘⟩
    Inverse.equivalent I.correct
  sound (xs₁≈xs₂ ∷ rest) {s = t ∷ s} =
    Inverse.equivalent ∂-correct ⟨∘⟩
    sound (♭ (rest t)) ⟨∘⟩
    Eq.sym (Inverse.equivalent ∂-correct)

  complete : ∀ {Tok R xs₁ xs₂}
               {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
             p₁ ≈ p₂ → p₁ ≈′ p₂
  complete p₁≈p₂ =
    (λ {_} → I.same-set p₁≈p₂) ∷ λ t → ♯ complete (∂-cong-≈ p₁≈p₂)

  correct : ∀ {Tok R xs₁ xs₂}
              {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
            p₁ ≈′ p₂ ⇔ p₁ ≈ p₂
  correct = Eq.equivalent sound complete

------------------------------------------------------------------------
-- Parser equivalence

infix 4 _≅′_

_≅′_ : ∀ {Tok R xs₁ xs₂} → Parser Tok R xs₁ → Parser Tok R xs₂ → Set
_≅′_ = Eq BagEq._≈_

-- The two definitions of parser equivalence are equivalent.

module ParserEquivalence where

  sound : ∀ {Tok R xs₁ xs₂}
            {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
          p₁ ≅′ p₂ → p₁ ≅ p₂
  sound (xs₁≅xs₂ ∷ rest) {s = []}    =
    Inv.sym I.correct ⟪∘⟫ xs₁≅xs₂ ⟪∘⟫ I.correct
  sound (xs₁≅xs₂ ∷ rest) {s = t ∷ s} =
    ∂-correct ⟪∘⟫ sound (♭ (rest t)) ⟪∘⟫ Inv.sym ∂-correct

  complete : ∀ {Tok R xs₁ xs₂}
               {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
             p₁ ≅ p₂ → p₁ ≅′ p₂
  complete p₁≅p₂ =
    (λ {_} → I.same-bag p₁≅p₂) ∷ λ t → ♯ complete (∂-cong-≅ p₁≅p₂)

  correct : ∀ {Tok R xs₁ xs₂}
              {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
            p₁ ≅′ p₂ ⇔ p₁ ≅ p₂
  correct = Eq.equivalent sound complete
