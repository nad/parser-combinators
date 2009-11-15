------------------------------------------------------------------------
-- Recognisers form a Kleene algebra
------------------------------------------------------------------------

module TotalRecognisers.LeftRecursion.KleeneAlgebra (Tok : Set) where

open import Algebra
import Algebra.Props.BooleanAlgebra
open import Coinduction
open import Data.Bool hiding (_∧_)
import Data.Bool.Properties as Bool
private
  module BoolCS = CommutativeSemiring Bool.commutativeSemiring-∨-∧
  module BoolBA = Algebra.Props.BooleanAlgebra Bool.booleanAlgebra
open import Data.Function
open import Data.List as List
private
  module ListMonoid {A} = Monoid (List.monoid A)
open import Data.Product
open import Relation.Binary.HeterogeneousEquality using (_≅_; refl)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

import TotalRecognisers.LeftRecursion
open TotalRecognisers.LeftRecursion Tok hiding (left-zero)
import TotalRecognisers.LeftRecursion.Lib
open TotalRecognisers.LeftRecursion.Lib Tok
open KleeneStar₂

------------------------------------------------------------------------
-- A variant of _≤_

infix 4 _≲_

-- If _∣_ is viewed as the join operation of a join-semilattice, then
-- the following definition of order is natural.

_≲_ : ∀ {n₁ n₂} → P n₁ → P n₂ → Set
p₁ ≲ p₂ = p₁ ∣ p₂ ≈ p₂

-- The order above coincides with _≤_.

≤⇔≲ : ∀ {n₁ n₂} (p₁ : P n₁) (p₂ : P n₂) → p₁ ≤ p₂ ⇔ p₁ ≲ p₂
≤⇔≲ {n₁} p₁ p₂ =
  ((λ p₁≤p₂ → ((λ {_} → helper₁ p₁≤p₂) , λ {_} → ∣ʳ {n₁ = n₁}))
  , helper₂
  )
  where
  helper₁ : p₁ ≤ p₂ → p₁ ∣ p₂ ≤ p₂
  helper₁ p₁≤p₂ (∣ˡ s∈p₁) = p₁≤p₂ s∈p₁
  helper₁ p₁≤p₂ (∣ʳ s∈p₂) = s∈p₂

  helper₂ : p₁ ≲ p₂ → p₁ ≤ p₂
  helper₂ (p₁∣p₂≤p₂ , _) s∈p₁ = p₁∣p₂≤p₂ (∣ˡ s∈p₁)

------------------------------------------------------------------------
-- Recognisers form a *-continuous Kleene algebra

-- The definition of *-continuous Kleene algebras used here is the one
-- given by Kozen in "On Kleene Algebras and Closed Semirings", except
-- for the presence of the recogniser indices. Kozen used the order
-- _≲_ in his definition, but as shown above this order is equivalent
-- to _≤_.

-- Additive idempotent commutative monoid. (One of the identity lemmas
-- could be omitted.)

∣-commutative : ∀ {n₁ n₂} (p₁ : P n₁) (p₂ : P n₂) → p₁ ∣ p₂ ≋ p₂ ∣ p₁
∣-commutative {n₁} {n₂} p₁ p₂ =
  BoolCS.+-comm n₁ n₂ ∷ λ t → ♯ ∣-commutative (∂ p₁ t) (∂ p₂ t)

∅-left-identity : ∀ {n} (p : P n) → ∅ ∣ p ≋ p
∅-left-identity p = refl ∷ λ t → ♯ ∅-left-identity (∂ p t)

∅-right-identity : ∀ {n} (p : P n) → p ∣ ∅ ≋ p
∅-right-identity {n} p =
  proj₂ BoolCS.+-identity n ∷ λ t → ♯ ∅-right-identity (∂ p t)

∣-associative : ∀ {n₁ n₂ n₃} (p₁ : P n₁) (p₂ : P n₂) (p₃ : P n₃) →
                p₁ ∣ (p₂ ∣ p₃) ≋ (p₁ ∣ p₂) ∣ p₃
∣-associative {n₁} {n₂} {n₃} p₁ p₂ p₃ =
  sym (BoolCS.+-assoc n₁ n₂ n₃) ∷ λ t →
    ♯ ∣-associative (∂ p₁ t) (∂ p₂ t) (∂ p₃ t)

∣-idempotent : ∀ {n} (p : P n) → p ∣ p ≋ p
∣-idempotent {n} p =
  BoolBA.∨-idempotent n ∷ λ t → ♯ ∣-idempotent (∂ p t)

-- Multiplicative monoid.

ε-left-identity : ∀ {n} (p : P n) → ε ⊙ p ≈ p
ε-left-identity {n} p = ( (λ {_} → helper)
                        , λ s∈p → add-♭♯ n ε · s∈p
                        )
  where
  helper : ε ⊙ p ≤ p
  helper ([]∈ε · s∈p) with drop-♭♯ n []∈ε
  ... | ε = s∈p

ε-right-identity : ∀ {n} (p : P n) → p ⊙ ε ≈ p
ε-right-identity {n} p =
  ( (λ {_} s∈ → helper s∈ refl)
  , λ s∈p → cast∈ (proj₂ ListMonoid.identity _) refl
                  (s∈p · add-♭♯ n ε)
  )
  where
  helper : ∀ {s n′} {p′ : P n′} →
           s ∈ p ⊙ p′ → p′ ≅ (P _ ∶ ε) → s ∈ p
  helper (s∈p · []∈ε) refl with drop-♭♯ n []∈ε
  ... | ε = cast∈ (sym (proj₂ ListMonoid.identity _)) refl s∈p

·-associative : ∀ {n₁ n₂ n₃} (p₁ : P n₁) (p₂ : P n₂) (p₃ : P n₃) →
                p₁ ⊙ (p₂ ⊙ p₃) ≈ (p₁ ⊙ p₂) ⊙ p₃
·-associative {n₁} {n₂} {n₃} p₁ p₂ p₃ =
  ((λ {_} → helper₁) , λ {_} → helper₂)
  where
  helper₁ : p₁ ⊙ (p₂ ⊙ p₃) ≤ (p₁ ⊙ p₂) ⊙ p₃
  helper₁ (_·_ {s₁ = s₁} s₁∈ s₂++s₃∈) with drop-♭♯ n₁ s₂++s₃∈
  ... | s₂∈ · s₃∈ =
    cast∈ (ListMonoid.assoc s₁ _ _) refl $
      add-♭♯ n₃ (add-♭♯ n₂ (drop-♭♯ (n₂ ∧ n₃) s₁∈) ·
                 add-♭♯ n₁ (drop-♭♯ n₃        s₂∈)) ·
      add-♭♯ (n₁ ∧ n₂) (drop-♭♯ n₂ s₃∈)

  helper₂ : (p₁ ⊙ p₂) ⊙ p₃ ≤ p₁ ⊙ (p₂ ⊙ p₃)
  helper₂ (s₁++s₂∈ · s₃∈) with drop-♭♯ n₃ s₁++s₂∈
  ... | _·_ {s₁ = s₁} s₁∈ s₂∈ =
    cast∈ (sym $ ListMonoid.assoc s₁ _ _) refl $
      add-♭♯ (n₂ ∧ n₃) (drop-♭♯ n₂ s₁∈) ·
      add-♭♯ n₁ (add-♭♯ n₃ (drop-♭♯ n₁        s₂∈) ·
                 add-♭♯ n₂ (drop-♭♯ (n₁ ∧ n₂) s₃∈))

-- Distributivity.

left-distributive :
  ∀ {n₁ n₂ n₃} (p₁ : P n₁) (p₂ : P n₂) (p₃ : P n₃) →
  p₁ ⊙ (p₂ ∣ p₃) ≈ p₁ ⊙ p₂ ∣ p₁ ⊙ p₃
left-distributive {n₁} {n₂} {n₃} p₁ p₂ p₃ =
  ((λ {_} → helper₁) , λ {_} → helper₂)
  where
  helper₁ : p₁ ⊙ (p₂ ∣ p₃) ≤ p₁ ⊙ p₂ ∣ p₁ ⊙ p₃
  helper₁ (s₁∈p₁ · s₂∈p₂∣p₃) with drop-♭♯ n₁ s₂∈p₂∣p₃
  ... | ∣ˡ s₂∈p₂ = ∣ˡ $ add-♭♯ n₂ (drop-♭♯ (n₂ ∨ n₃) s₁∈p₁) ·
                        add-♭♯ n₁                    s₂∈p₂
  ... | ∣ʳ s₂∈p₃ = ∣ʳ {n₁ = n₁ ∧ n₂} $
                      add-♭♯ n₃ (drop-♭♯ (n₂ ∨ n₃) s₁∈p₁) ·
                      add-♭♯ n₁                    s₂∈p₃

  helper₂ : p₁ ⊙ p₂ ∣ p₁ ⊙ p₃ ≤ p₁ ⊙ (p₂ ∣ p₃)
  helper₂ (∣ˡ (s₁∈p₁ · s₂∈p₂)) =
    add-♭♯ (n₂ ∨ n₃)      (drop-♭♯ n₂ s₁∈p₁) ·
    add-♭♯ n₁        (∣ˡ $ drop-♭♯ n₁ s₂∈p₂)
  helper₂ (∣ʳ (s₁∈p₁ · s₂∈p₃)) =
    add-♭♯ (n₂ ∨ n₃)                (drop-♭♯ n₃ s₁∈p₁) ·
    add-♭♯ n₁        (∣ʳ {n₁ = n₂} $ drop-♭♯ n₁ s₂∈p₃)

right-distributive :
  ∀ {n₁ n₂ n₃} (p₁ : P n₁) (p₂ : P n₂) (p₃ : P n₃) →
  (p₁ ∣ p₂) ⊙ p₃ ≈ p₁ ⊙ p₃ ∣ p₂ ⊙ p₃
right-distributive {n₁} {n₂} {n₃} p₁ p₂ p₃ =
  ((λ {_} → helper₁) , λ {_} → helper₂)
  where
  helper₁ : (p₁ ∣ p₂) ⊙ p₃ ≤ p₁ ⊙ p₃ ∣ p₂ ⊙ p₃
  helper₁ (s₁∈p₁∣p₂ · s₂∈p₃) with drop-♭♯ n₃ s₁∈p₁∣p₂
  ... | ∣ˡ s₁∈p₁ = ∣ˡ $ add-♭♯ n₃                    s₁∈p₁ ·
                        add-♭♯ n₁ (drop-♭♯ (n₁ ∨ n₂) s₂∈p₃)
  ... | ∣ʳ s₁∈p₂ = ∣ʳ {n₁ = n₁ ∧ n₃} $
                      add-♭♯ n₃                    s₁∈p₂ ·
                      add-♭♯ n₂ (drop-♭♯ (n₁ ∨ n₂) s₂∈p₃)

  helper₂ : p₁ ⊙ p₃ ∣ p₂ ⊙ p₃ ≤ (p₁ ∣ p₂) ⊙ p₃
  helper₂ (∣ˡ (s₁∈p₁ · s₂∈p₃)) =
    add-♭♯ n₃        (∣ˡ $ drop-♭♯ n₃ s₁∈p₁) ·
    add-♭♯ (n₁ ∨ n₂)      (drop-♭♯ n₁ s₂∈p₃)
  helper₂ (∣ʳ (s₁∈p₂ · s₂∈p₃)) =
    add-♭♯ n₃        (∣ʳ {n₁ = n₁} $ drop-♭♯ n₃ s₁∈p₂) ·
    add-♭♯ (n₁ ∨ n₂)                (drop-♭♯ n₂ s₂∈p₃)

-- Zero.

left-zero : ∀ {n} (p : P n) → ∅ ⊙ p ≈ ∅
left-zero {n} p = ((λ {_} → helper) , λ {_} ())
  where
  helper : ∅ ⊙ p ≤ ∅
  helper (s∈∅ · _) with drop-♭♯ n s∈∅
  ... | ()

right-zero : ∀ {n} (p : P n) → p ⊙ ∅ ≈ ∅
right-zero {n} p = ((λ {_} → helper) , λ {_} ())
  where
  helper : p ⊙ ∅ ≤ ∅
  helper (_ · s∈∅) with drop-♭♯ n s∈∅
  ... | ()

-- *-continuity.

*-continuity-upper-bound :
  ∀ {n₁ n₂ n₃} (p₁ : P n₁) (p₂ : P n₂) (p₃ : P n₃) →
  ∀ i → p₁ ⊙ (p₂ ^ i ⊙ p₃) ≤ p₁ ⊙ (p₂ ⋆ ⊙ p₃)
*-continuity-upper-bound {n₁} {n₂} {n₃} _ _ _ i (s₁∈p₁ · s∈p₂ⁱ⊙p₃)
  with drop-♭♯ n₁ s∈p₂ⁱ⊙p₃
... | s₂∈p₂ⁱ · s₃∈p₃ =
  add-♭♯ (true ∧ n₃) (drop-♭♯ (^-n ∧ n₃) s₁∈p₁) ·
  add-♭♯ n₁ (add-♭♯ n₃ (^≤⋆ i (drop-♭♯ n₃ s₂∈p₂ⁱ)) · drop-♭♯ ^-n s₃∈p₃)
  where ^-n = ^-nullable n₂ i

*-continuity-least-upper-bound :
  ∀ {n₁ n₂ n₃ n} (p₁ : P n₁) (p₂ : P n₂) (p₃ : P n₃) (p : P n) →
  (∀ i → p₁ ⊙ (p₂ ^ i ⊙ p₃) ≤ p) → p₁ ⊙ (p₂ ⋆ ⊙ p₃) ≤ p
*-continuity-least-upper-bound
  {n₁} {n₂} {n₃} _ _ _ _ ub (s₁∈p₁ · s∈p₂⋆⊙p₃)
  with drop-♭♯ n₁ s∈p₂⋆⊙p₃
... | s₂∈p₂⋆ · s₃∈p₃ with ⋆≤^ (drop-♭♯ n₃ s₂∈p₂⋆)
... | (i , s₂∈p₂ⁱ) =
  ub i $ add-♭♯ (^-n ∧ n₃) (drop-♭♯ (true ∧ n₃) s₁∈p₁) ·
         add-♭♯ n₁ (add-♭♯ n₃ s₂∈p₂ⁱ · add-♭♯ ^-n s₃∈p₃)
  where ^-n = ^-nullable n₂ i
