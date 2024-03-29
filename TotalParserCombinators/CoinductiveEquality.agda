------------------------------------------------------------------------
-- An alternative definition of equality
------------------------------------------------------------------------

module TotalParserCombinators.CoinductiveEquality where

open import Codata.Musical.Notation
open import Data.List
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Binary.BagAndSetEquality
  using () renaming (_∼[_]_ to _List-∼[_]_)
open import Function.Equivalence as Eq using (_⇔_)
import Function.Related as Related

open Related using (SK-sym)
open Related.EquationalReasoning

open import TotalParserCombinators.Parser
open import TotalParserCombinators.Semantics
import TotalParserCombinators.InitialBag as I
open import TotalParserCombinators.Derivative as D using (D)

infix 5 _∷_
infix 4 _∼[_]c_

-- Two recognisers/languages are equal if their nullability indices
-- are equal (according to _List-∼[_]_) and all their derivatives are
-- equal (coinductively). Note that the inhabitants of this type are
-- bisimulations (if the Kind stands for a symmetric relation).

data _∼[_]c_ {Tok R xs₁ xs₂}
             (p₁ : Parser Tok R xs₁) (k : Kind)
             (p₂ : Parser Tok R xs₂) : Set where
  _∷_ : (init : xs₁ List-∼[ k ] xs₂)
        (rest : ∀ t → ∞ (D t p₁ ∼[ k ]c D t p₂)) →
        p₁ ∼[ k ]c p₂

-- The two definitions of parser/language equivalence are equivalent.

sound : ∀ {k Tok R xs₁ xs₂}
          {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
        p₁ ∼[ k ]c p₂ → p₁ ∼[ k ] p₂
sound {xs₁ = xs₁} {xs₂} {p₁} {p₂} (xs₁≈xs₂ ∷ rest) {x} {[]} =
  x ∈ p₁ · []  ↔⟨ I.correct ⟩
  (x ∈ xs₁)    ∼⟨ xs₁≈xs₂ ⟩
  (x ∈ xs₂)    ↔⟨ SK-sym I.correct ⟩
  x ∈ p₂ · []  ∎
sound {xs₁ = xs₁} {xs₂} {p₁} {p₂} (xs₁≈xs₂ ∷ rest) {x} {t ∷ s} =
  x ∈   p₁   · t ∷ s  ↔⟨ SK-sym D.correct ⟩
  x ∈ D t p₁ ·     s  ∼⟨ sound (♭ (rest t)) ⟩
  x ∈ D t p₂ ·     s  ↔⟨ D.correct ⟩
  x ∈   p₂   · t ∷ s  ∎

complete : ∀ {k Tok R xs₁ xs₂}
             {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
           p₁ ∼[ k ] p₂ → p₁ ∼[ k ]c p₂
complete p₁≈p₂ =
  (λ {_} → I.cong p₁≈p₂) ∷ λ t → ♯ complete (D.cong p₁≈p₂)

correct : ∀ {k Tok R xs₁ xs₂}
            {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
          p₁ ∼[ k ]c p₂ ⇔ p₁ ∼[ k ] p₂
correct = Eq.equivalence sound complete
