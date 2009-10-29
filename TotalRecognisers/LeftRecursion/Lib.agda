------------------------------------------------------------------------
-- A tiny library of derived combinators
------------------------------------------------------------------------

open import Relation.Binary
open import Relation.Binary.PropositionalEquality

module TotalRecognisers.LeftRecursion.Lib
         (Tok : Set)
         (_≟_ : Decidable (_≡_ {A = Tok}))
         where

open import Coinduction
open import Data.Bool hiding (_∧_)
open import Data.Function
open import Data.List
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product as Prod

import TotalRecognisers.LeftRecursion
open TotalRecognisers.LeftRecursion Tok _≟_ hiding (left-zero)

------------------------------------------------------------------------
-- Kleene star

-- The intended semantics of the Kleene star.

infixr 5 _∷_
infix  4 _∈[_]⋆

data _∈[_]⋆ {n} : List Tok → P n → Set where
  []  : ∀ {p}       → [] ∈[ p ]⋆
  _∷_ : ∀ {s₁ s₂ p} → s₁ ∈ p → s₂ ∈[ p ]⋆ → s₁ ++ s₂ ∈[ p ]⋆

module KleeneStar₁ where

  infix 15 _⋆

  -- This definition requires that the argument recognisers are not
  -- nullable.

  _⋆ : P false → P true
  p ⋆ = ε ∣ ⟨ p ⟩ · ⟪ ♯ (p ⋆) ⟫

  -- The definition of _⋆ above is correct.

  ⋆-sound : ∀ {s p} → s ∈ p ⋆ → s ∈[ p ]⋆
  ⋆-sound (∣ˡ ε)           = []
  ⋆-sound (∣ʳ (pr₁ · pr₂)) = pr₁ ∷ ⋆-sound pr₂

  ⋆-complete : ∀ {s p} → s ∈[ p ]⋆ → s ∈ p ⋆
  ⋆-complete []                    = ∣ˡ ε
  ⋆-complete (_∷_ {[]}    pr₁ pr₂) = ⋆-complete pr₂
  ⋆-complete (_∷_ {_ ∷ _} pr₁ pr₂) =
    ∣ʳ {n₁ = true} (pr₁ · ⋆-complete pr₂)

module KleeneStar₂ where

  infix 15 _⋆

  -- This definition works for any argument recogniser.

  _⋆ : ∀ {n} → P n → P true
  _⋆ = KleeneStar₁._⋆ ∘ nonempty

  -- The definition of _⋆ above is correct.

  ⋆-sound : ∀ {s n} {p : P n} → s ∈ p ⋆ → s ∈[ p ]⋆
  ⋆-sound (∣ˡ ε)                    = []
  ⋆-sound (∣ʳ (nonempty pr₁ · pr₂)) = pr₁ ∷ ⋆-sound pr₂

  ⋆-complete : ∀ {s n} {p : P n} → s ∈[ p ]⋆ → s ∈ p ⋆
  ⋆-complete []                    = ∣ˡ ε
  ⋆-complete (_∷_ {[]}    pr₁ pr₂) = ⋆-complete pr₂
  ⋆-complete (_∷_ {_ ∷ _} pr₁ pr₂) =
    ∣ʳ {n₁ = true} (nonempty pr₁ · ⋆-complete pr₂)

  -- Note, however, that for actual parsing the corresponding
  -- definition would not be correct. The reason is that p would give
  -- a result also when the empty string was accepted, and these
  -- results are ignored by the definition above. In the case of
  -- actual parsing the result of p ⋆, when p is nullable, should be a
  -- stream and not a finite list.

------------------------------------------------------------------------
-- A simplified sequencing operator

infixl 10 _⊙_

_⊙_ : ∀ {n₁ n₂} → P n₁ → P n₂ → P (n₁ ∧ n₂)
p₁ ⊙ p₂ = ♯? p₁ · ♯? p₂

------------------------------------------------------------------------
-- A combinator which repeats a recogniser a fixed number of times

infixl 15 _^_

^-nullable : Bool → ℕ → Bool
^-nullable _ zero    = _
^-nullable _ (suc _) = _

_^_ : ∀ {n} → P n → (i : ℕ) → P (^-nullable n i)
p ^ 0     = ε
p ^ suc i = p ⊙ p ^ i

-- Some lemmas relating _^_ to _⋆.

open KleeneStar₂

^≤⋆ : ∀ {n} {p : P n} i → p ^ i ≤ p ⋆
^≤⋆ {n} {p} i s∈ = ⋆-complete $ helper i s∈
  where
  helper : ∀ i {s} → s ∈ p ^ i → s ∈[ p ]⋆
  helper zero    ε              = []
  helper (suc i) (s₁∈p · s₂∈pⁱ) =
    drop-♭♯ (^-nullable n i) s₁∈p ∷ helper i (drop-♭♯ n s₂∈pⁱ)

⋆≤^ : ∀ {n} {p : P n} {s} → s ∈ p ⋆ → ∃ λ i → s ∈ p ^ i
⋆≤^ {n} {p} s∈p⋆ = helper (⋆-sound s∈p⋆)
  where
  helper : ∀ {s} → s ∈[ p ]⋆ → ∃ λ i → s ∈ p ^ i
  helper []             = (0 , ε)
  helper (s₁∈p ∷ s₂∈p⋆) =
    Prod.map suc (λ {i} s₂∈pⁱ → add-♭♯ (^-nullable n i) s₁∈p ·
                                add-♭♯ n                s₂∈pⁱ)
             (helper s₂∈p⋆)