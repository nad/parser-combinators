------------------------------------------------------------------------
-- An alternative definition of equality
------------------------------------------------------------------------

module TotalParserCombinators.CoinductiveEquality where

open import Coinduction
open import Data.List
import Data.List.Any as Any
open import Function.Equivalence as Eq using (_⇔_)
import Function.Inverse as Inv

open Any.Membership-≡ using (_∈_) renaming (_≈[_]_ to _List-≈[_]_)
open Inv.EquationalReasoning

open import TotalParserCombinators.Parser
open import TotalParserCombinators.Semantics
import TotalParserCombinators.InitialBag as I
open import TotalParserCombinators.BreadthFirst
  using (∂; ∂-correct; ∂-cong)

infix 5 _∷_
infix 4 _≈[_]′_

-- Two recognisers/languages are equal if their nullability indices
-- are equal (according to _List-≈[_]_) and all their derivatives are
-- equal (coinductively). Note that the inhabitants of this type are
-- bisimulations.

data _≈[_]′_ {Tok R xs₁ xs₂}
             (p₁ : Parser Tok R xs₁) (k : Kind)
             (p₂ : Parser Tok R xs₂) : Set where
  _∷_ : (init : xs₁ List-≈[ k ] xs₂)
        (rest : ∀ t → ∞ (∂ p₁ t ≈[ k ]′ ∂ p₂ t)) →
        p₁ ≈[ k ]′ p₂

-- The two definitions of parser/language equivalence are equivalent.

sound : ∀ {k Tok R xs₁ xs₂}
          {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
        p₁ ≈[ k ]′ p₂ → p₁ ≈[ k ] p₂
sound {xs₁ = xs₁} {xs₂} {p₁} {p₂} (xs₁≈xs₂ ∷ rest) {x} {[]} =
  x ∈ p₁ · []  ⇿⟨ I.correct ⟩
  (x ∈ xs₁)    ≈⟨ xs₁≈xs₂ ⟩
  (x ∈ xs₂)    ⇿⟨ sym I.correct ⟩
  x ∈ p₂ · []  ∎
sound {xs₁ = xs₁} {xs₂} {p₁} {p₂} (xs₁≈xs₂ ∷ rest) {x} {t ∷ s} =
  x ∈   p₁   · t ∷ s  ⇿⟨ sym ∂-correct ⟩
  x ∈ ∂ p₁ t ·     s  ≈⟨ sound (♭ (rest t)) ⟩
  x ∈ ∂ p₂ t ·     s  ⇿⟨ ∂-correct ⟩
  x ∈   p₂   · t ∷ s  ∎

complete : ∀ {k Tok R xs₁ xs₂}
             {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
           p₁ ≈[ k ] p₂ → p₁ ≈[ k ]′ p₂
complete p₁≈p₂ =
  (λ {_} → I.same-set p₁≈p₂) ∷ λ t → ♯ complete (∂-cong p₁≈p₂)

correct : ∀ {k Tok R xs₁ xs₂}
            {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
          p₁ ≈[ k ]′ p₂ ⇔ p₁ ≈[ k ] p₂
correct = Eq.equivalent sound complete
