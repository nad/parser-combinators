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
open import TotalParserCombinators.BreadthFirst.Derivative using (D)
open import TotalParserCombinators.BreadthFirst.Lemmas
  using (D-correct; D-cong)

infix 5 _∷_
infix 4 _≈[_]c_

-- Two recognisers/languages are equal if their nullability indices
-- are equal (according to _List-≈[_]_) and all their derivatives are
-- equal (coinductively). Note that the inhabitants of this type are
-- bisimulations.

data _≈[_]c_ {Tok R xs₁ xs₂}
             (p₁ : Parser Tok R xs₁) (k : Kind)
             (p₂ : Parser Tok R xs₂) : Set where
  _∷_ : (init : xs₁ List-≈[ k ] xs₂)
        (rest : ∀ t → ∞ (D t p₁ ≈[ k ]c D t p₂)) →
        p₁ ≈[ k ]c p₂

-- The two definitions of parser/language equivalence are equivalent.

sound : ∀ {k Tok R xs₁ xs₂}
          {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
        p₁ ≈[ k ]c p₂ → p₁ ≈[ k ] p₂
sound {xs₁ = xs₁} {xs₂} {p₁} {p₂} (xs₁≈xs₂ ∷ rest) {x} {[]} =
  x ∈ p₁ · []  ⇿⟨ I.correct ⟩
  (x ∈ xs₁)    ≈⟨ xs₁≈xs₂ ⟩
  (x ∈ xs₂)    ⇿⟨ sym I.correct ⟩
  x ∈ p₂ · []  ∎
sound {xs₁ = xs₁} {xs₂} {p₁} {p₂} (xs₁≈xs₂ ∷ rest) {x} {t ∷ s} =
  x ∈   p₁   · t ∷ s  ⇿⟨ sym D-correct ⟩
  x ∈ D t p₁ ·     s  ≈⟨ sound (♭ (rest t)) ⟩
  x ∈ D t p₂ ·     s  ⇿⟨ D-correct ⟩
  x ∈   p₂   · t ∷ s  ∎

complete : ∀ {k Tok R xs₁ xs₂}
             {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
           p₁ ≈[ k ] p₂ → p₁ ≈[ k ]c p₂
complete p₁≈p₂ =
  (λ {_} → I.cong p₁≈p₂) ∷ λ t → ♯ complete (D-cong p₁≈p₂)

correct : ∀ {k Tok R xs₁ xs₂}
            {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
          p₁ ≈[ k ]c p₂ ⇔ p₁ ≈[ k ] p₂
correct = Eq.equivalent sound complete
