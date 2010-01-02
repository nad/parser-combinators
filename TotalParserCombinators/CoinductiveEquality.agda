------------------------------------------------------------------------
-- An alternative definition of equality
------------------------------------------------------------------------

module TotalParserCombinators.CoinductiveEquality where

open import Coinduction
open import Data.List
import Data.List.Any as Any
open import Data.Product
open import Relation.Binary

private
  open module Eq {R : Set} = Setoid (Any.Membership-≡.Set-equality {R})
    using () renaming (_≈_ to _≗_)

open import TotalParserCombinators.Parser
open import TotalParserCombinators.Semantics
import TotalParserCombinators.InitialSet as I
open import TotalParserCombinators.BreadthFirst
  hiding (sound; complete)

infix 5 _∷_
infix 4 _≈′_

-- Two recognisers/languages are equal if their nullability indices
-- are equal (as sets) and all their derivatives are equal
-- (coinductively). Note that the inhabitants of this type are
-- bisimulations.

data _≈′_ {Tok R xs₁ xs₂}
          (p₁ : Parser Tok R xs₁) (p₂ : Parser Tok R xs₂) : Set where
  _∷_ : (init : xs₁ ≗ xs₂) (rest : ∀ t → ∞ (∂ p₁ t ≈′ ∂ p₂ t)) →
        p₁ ≈′ p₂

-- This equality coincides with _≈_.

sym : ∀ {Tok R xs₁ xs₂}
        {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
      p₁ ≈′ p₂ → p₂ ≈′ p₁
sym (init ∷ rest) = Eq.sym init ∷ λ t → ♯ sym (♭ (rest t))

sound : ∀ {Tok R xs₁ xs₂}
          {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
        p₁ ≈′ p₂ → p₁ ≈ p₂
sound {Tok} {R} p₁≈′p₂ =
  ((λ {_} → lemma p₁≈′p₂) , λ {_} → lemma (sym p₁≈′p₂))
  where
  lemma : ∀ {xs₁ xs₂} {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
          p₁ ≈′ p₂ → p₁ ⊑ p₂
  lemma ((⊆ , _) ∷ rest) {s = []}    []∈p₁  =
    I.sound _ (⊆ (I.complete []∈p₁))
  lemma (_       ∷ rest) {s = t ∷ s} t∷s∈p₁ =
    ∂-sound _ (lemma (♭ (rest t)) (∂-complete t∷s∈p₁))

complete : ∀ {Tok R xs₁ xs₂}
             {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
           p₁ ≈ p₂ → p₁ ≈′ p₂
complete p₁≈p₂ = I.same-set p₁≈p₂ ∷ λ t → ♯ complete (∂-cong p₁≈p₂)
