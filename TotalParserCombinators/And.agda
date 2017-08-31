------------------------------------------------------------------------
-- And
------------------------------------------------------------------------

module TotalParserCombinators.And where

open import Category.Monad
import Data.List as List
open import Data.List.Any.BagAndSetEquality
open import Data.List.Any.Membership.Propositional.Properties
open import Data.Product
open import Function
open import Function.Inverse using (_↔_)
import Function.Related as Related
open import Function.Related.TypeIsomorphisms
open import Level
open import Relation.Binary.Product.Pointwise

open RawMonadPlus {f = zero} List.monadPlus using (_⊗_)

open import TotalParserCombinators.Congruence using (_∼[_]P_; _≅P_)
open import TotalParserCombinators.Derivative using (D)
open import TotalParserCombinators.Parser
import TotalParserCombinators.Pointwise as Pointwise
open import TotalParserCombinators.Semantics using (_∈_·_)

-- _&_ is defined as a pointwise lifting of _⊗_.

private
  module And {R₁ R₂ : Set} = Pointwise R₁ R₂ id _⊗_ ⊗-cong

-- p₁ & p₂ returns a result if both p₁ and p₂ do.

infixr 6 _&_ _&-cong_

_&_ : ∀ {Tok R₁ R₂ xs₁ xs₂} →
      Parser Tok R₁ xs₁ → Parser Tok R₂ xs₂ →
      Parser Tok (R₁ × R₂) (xs₁ ⊗ xs₂)
_&_ = And.lift

-- D distributes over _&_.

D-& : ∀ {Tok R₁ R₂ xs₁ xs₂ t}
      (p₁ : Parser Tok R₁ xs₁) (p₂ : Parser Tok R₂ xs₂) →
      D t (p₁ & p₂) ≅P D t p₁ & D t p₂
D-& = And.D-lift

-- _&_ preserves equality.

_&-cong_ : ∀ {k Tok R xs₁ xs₁′ xs₂ xs₂′}
             {p₁  : Parser Tok R xs₁} {p₁′ : Parser Tok R xs₁′}
             {p₂  : Parser Tok R xs₂} {p₂′ : Parser Tok R xs₂′} →
           p₁ ∼[ k ]P p₁′ → p₂ ∼[ k ]P p₂′ → p₁ & p₂ ∼[ k ]P p₁′ & p₂′
_&-cong_ = And.lift-cong

-- _&_ is correct.

correct : ∀ {Tok R₁ R₂ xs₁ xs₂ x₁ x₂ s}
          (p₁ : Parser Tok R₁ xs₁) (p₂ : Parser Tok R₂ xs₂) →
          (x₁ , x₂) ∈ p₁ & p₂ · s ↔ (x₁ ∈ p₁ · s × x₂ ∈ p₂ · s)
correct {x₁ = x₁} {x₂} =
  And.lift-property
    (λ F G H → H (x₁ , x₂) ↔ (F x₁ × G x₂))
    (λ F↔F′ G↔G′ H↔H′ →
       Related-cong (H↔H′ (x₁ , x₂)) (F↔F′ x₁ ×-↔ G↔G′ x₂))
    (sym ⊗-∈↔)
  where open Related.EquationalReasoning
