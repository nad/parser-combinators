------------------------------------------------------------------------
-- Recognisers form a Kleene algebra
------------------------------------------------------------------------

open import Relation.Binary
open import Relation.Binary.PropositionalEquality

module TotalRecognisers.LeftRecursion.KleeneAlgebra
         (Tok : Set)
         (_≟_ : Decidable (_≡_ {A = Tok}))
         where

open import Algebra
open import Data.Bool hiding (_∧_)
open import Data.Function
open import Data.List as List
private
  module ListMonoid {A} = Monoid (List.monoid A)
open import Data.Product
open import Relation.Binary.HeterogeneousEquality using (_≅_; refl)
open import Relation.Nullary

import TotalRecognisers.LeftRecursion
open TotalRecognisers.LeftRecursion Tok _≟_ hiding (left-zero)
open Variant₂

------------------------------------------------------------------------
-- Relations on recognisers

infix 4 _≤_ _≲_ _≈_

-- p₁ ≤ p₂ iff the language (defined by) p₂ contains all the strings
-- in the language p₁.

_≤_ : ∀ {n₁ n₂} → P n₁ → P n₂ → Set
p₁ ≤ p₂ = ∀ {s} → s ∈ p₁ → s ∈ p₂

-- p₁ ≈ p₂ iff the languages p₁ and p₂ contain the same strings.

_≈_ : ∀ {n₁ n₂} → P n₁ → P n₂ → Set
p₁ ≈ p₂ = p₁ ≤ p₂ × p₂ ≤ p₁

-- If _∣_ is viewed as the join operation of a join-semilattice, then
-- the following definition of order is natural.

_≲_ : ∀ {n₁ n₂} → P n₁ → P n₂ → Set
p₁ ≲ p₂ = p₁ ∣ p₂ ≈ p₂

-- The two definitions of order above coincide.

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
-- Variant of a combinator defined in TotalRecognisers.LeftRecursion

infixl 10 _⊙_

-- The following sequencing operator takes operators rather than
-- potentially delayed operators as arguments.

_⊙_ : ∀ {n₁ n₂} → P n₁ → P n₂ → P (n₁ ∧ n₂)
p₁ ⊙ p₂ = ♯? p₁ · ♯? p₂

------------------------------------------------------------------------
-- Recognisers form a Kleene algebra

-- The definition of Kleene algebras used is due to Kozen (see "On
-- Kleene Algebras and Closed Semirings"), except for the presence of
-- the recogniser indices. Kozen used the order _≲_, but as shown
-- above this order is equivalent to _≤_.

-- Additive idempotent commutative monoid. (One of the identity lemmas
-- could be omitted.)

∣-commutative : ∀ {n₁ n₂} (p₁ : P n₁) (p₂ : P n₂) → p₁ ∣ p₂ ≈ p₂ ∣ p₁
∣-commutative p₁ p₂ = ((λ {_} → helper p₁ p₂) , λ {_} → helper p₂ p₁)
  where
  helper : ∀ {n₁ n₂} (p₁ : P n₁) (p₂ : P n₂) → p₁ ∣ p₂ ≤ p₂ ∣ p₁
  helper _ _ (∣ˡ {n₂ = n₂} s∈p₁) = ∣ʳ {n₁ = n₂} s∈p₁
  helper _ _ (∣ʳ           s∈p₂) = ∣ˡ s∈p₂

∅-left-identity : ∀ {n} (p : P n) → ∅ ∣ p ≈ p
∅-left-identity p = ((λ {_} → helper) , λ {_} s∈p → ∣ʳ {p₁ = ∅} s∈p)
  where
  helper : ∅ ∣ p ≤ p
  helper (∣ˡ ())
  helper (∣ʳ s∈p) = s∈p

∅-right-identity : ∀ {n} (p : P n) → p ∣ ∅ ≈ p
∅-right-identity p = ((λ {_} → helper) , λ {_} s∈p → ∣ˡ s∈p)
  where
  helper : p ∣ ∅ ≤ p
  helper (∣ˡ s∈p) = s∈p
  helper (∣ʳ ())

∣-associative : ∀ {n₁ n₂ n₃} (p₁ : P n₁) (p₂ : P n₂) (p₃ : P n₃) →
                p₁ ∣ (p₂ ∣ p₃) ≈ (p₁ ∣ p₂) ∣ p₃
∣-associative {n₁} {n₂} p₁ p₂ p₃ =
  ((λ {_} → helper₁) , λ {_} → helper₂)
  where
  helper₁ : p₁ ∣ (p₂ ∣ p₃) ≤ (p₁ ∣ p₂) ∣ p₃
  helper₁ (∣ˡ s∈p₁)      = ∣ˡ (∣ˡ s∈p₁)
  helper₁ (∣ʳ (∣ˡ s∈p₂)) = ∣ˡ (∣ʳ {n₁ = n₁} s∈p₂)
  helper₁ (∣ʳ (∣ʳ s∈p₃)) = ∣ʳ {n₁ = n₁ ∨ n₂} s∈p₃

  helper₂ : (p₁ ∣ p₂) ∣ p₃ ≤ p₁ ∣ (p₂ ∣ p₃)
  helper₂ (∣ˡ (∣ˡ s∈p₁)) = ∣ˡ s∈p₁
  helper₂ (∣ˡ (∣ʳ s∈p₂)) = ∣ʳ {n₁ = n₁} (∣ˡ s∈p₂)
  helper₂ (∣ʳ s∈p₃)      = ∣ʳ {n₁ = n₁} (∣ʳ {n₁ = n₂} s∈p₃)

∣-idempotent : ∀ {n} (p : P n) → p ∣ p ≈ p
∣-idempotent p = ((λ {_} → helper) , λ {_} → ∣ˡ)
  where
  helper : p ∣ p ≤ p
  helper (∣ˡ s∈p) = s∈p
  helper (∣ʳ s∈p) = s∈p

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

-- Laws for the Kleene star.

unfold-left : ∀ {n} (p : P n) → ε ∣ p ⋆ ⊙ p ≤ p ⋆
unfold-left     p (∣ˡ ε)              = ∣ˡ ε
unfold-left {n} p (∣ʳ (s₁∈p⋆ · s₂∈p)) =
  ⋆-complete (snoc (⋆-sound $ drop-♭♯ n s₁∈p⋆) s₂∈p)
  where
  cast⋆ : ∀ {s₁ s₂} → s₁ ≡ s₂ → s₁ ∈[ p ]⋆ → s₂ ∈[ p ]⋆
  cast⋆ refl = id

  snoc : ∀ {s₁ s₂} → s₁ ∈[ p ]⋆ → s₂ ∈ p → s₁ ++ s₂ ∈[ p ]⋆
  snoc [] s₂∈p =
    cast⋆ (proj₂ ListMonoid.identity _) (s₂∈p ∷ [])
  snoc (_∷_ {s₁} s₁∈p s∈p⋆) s₂∈p =
    cast⋆ (sym $ ListMonoid.assoc s₁ _ _) (s₁∈p ∷ snoc s∈p⋆ s₂∈p)

unfold-right : ∀ {n} (p : P n) → ε ∣ p ⊙ p ⋆ ≤ p ⋆
unfold-right     p (∣ˡ ε)       = ∣ˡ ε
unfold-right {n} p (∣ʳ s₁++s₂∈) = helper s₁++s₂∈ refl
  where
  helper : ∀ {s n′} {p′ : P n′} →
           s ∈ p ⊙ p′ → p′ ≅ (P _ ∶ p ⋆) → s ∈ p ⋆
  helper (s₁∈p · s₂∈p⋆) refl =
    ⋆-complete (s₁∈p ∷ ⋆-sound (drop-♭♯ n s₂∈p⋆))

iterate-left : ∀ {n₁ n₂} (p₁ : P n₁) (p₂ : P n₂) →
               p₁ ⊙ p₂ ≤ p₂ → p₁ ⋆ ⊙ p₂ ≤ p₂
iterate-left {n₁} {n₂} p₁ p₂ p₁⊙p₂≤p₂ (s₁∈p₁⋆ · s₂∈p₂) =
  helper (⋆-sound (drop-♭♯ n₂ s₁∈p₁⋆)) s₂∈p₂
  where
  helper : ∀ {s₁ s₂} → s₁ ∈[ p₁ ]⋆ → s₂ ∈ p₂ → s₁ ++ s₂ ∈ p₂
  helper []                        s₂∈p₂ = s₂∈p₂
  helper (_∷_ {s₁} s₁₁∈p₁ s₁₂∈p₂⋆) s₂∈p₂ =
    cast∈ (sym $ ListMonoid.assoc s₁ _ _) refl $
      p₁⊙p₂≤p₂ (add-♭♯ n₂ s₁₁∈p₁ · add-♭♯ n₁ (helper s₁₂∈p₂⋆ s₂∈p₂))

iterate-right : ∀ {n₁ n₂} (p₁ : P n₁) (p₂ : P n₂) →
                p₁ ⊙ p₂ ≤ p₁ → p₁ ⊙ p₂ ⋆ ≤ p₁
iterate-right {n₁} {n₂} p₁ p₂ p₁⊙p₂≤p₁ = flip helper₁ refl
  where
  helper₂ : ∀ {s₁ s₂} → s₁ ∈ p₁ → s₂ ∈[ p₂ ]⋆ → s₁ ++ s₂ ∈ p₁
  helper₂ s₁∈p₁ [] =
    cast∈ (sym $ proj₂ ListMonoid.identity _) refl s₁∈p₁
  helper₂ {s₁} s₁∈p₁ (s₂₁∈p₂ ∷ s₂₂∈p₂⋆) =
    cast∈ (ListMonoid.assoc s₁ _ _) refl $
      helper₂ (p₁⊙p₂≤p₁ (add-♭♯ n₂ s₁∈p₁ · add-♭♯ n₁ s₂₁∈p₂)) s₂₂∈p₂⋆

  helper₁ : ∀ {s n} {p : P n} →
            s ∈ p₁ ⊙ p → p ≅ (P _ ∶ p₂ ⋆) → s ∈ p₁
  helper₁ (s₁∈p₁ · s₂∈p₂⋆) refl =
    helper₂ s₁∈p₁ (⋆-sound (drop-♭♯ n₁ s₂∈p₂⋆))
