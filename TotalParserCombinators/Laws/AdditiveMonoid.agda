------------------------------------------------------------------------
-- Laws related to _∣_ and fail
------------------------------------------------------------------------

module TotalParserCombinators.Laws.AdditiveMonoid where

open import Algebra
open import Coinduction
import Data.List.Any.BagAndSetEquality as Eq
open import Data.Product using (proj₁; proj₂)
open import Function

private
  module BagMonoid {k} {A : Set} =
    CommutativeMonoid (Eq.commutativeMonoid k A)

open import TotalParserCombinators.Derivative
open import TotalParserCombinators.Congruence
open import TotalParserCombinators.Parser

------------------------------------------------------------------------
-- _∣_ and fail form a commutative monoid

-- This monoid is idempotent if language equivalence is used.

commutative : ∀ {Tok R xs₁ xs₂}
              (p₁ : Parser Tok R xs₁) (p₂ : Parser Tok R xs₂) →
              p₁ ∣ p₂ ≅P p₂ ∣ p₁
commutative {xs₁ = xs₁} {xs₂} p₁ p₂ =
  BagMonoid.comm xs₁ xs₂ ∷ λ t → ♯ commutative (D t p₁) (D t p₂)

left-identity : ∀ {Tok R xs} (p : Parser Tok R xs) → fail ∣ p ≅P p
left-identity {xs = xs} p =
  proj₁ BagMonoid.identity xs ∷ λ t → ♯ left-identity (D t p)

right-identity : ∀ {Tok R xs} (p : Parser Tok R xs) → p ∣ fail ≅P p
right-identity {xs = xs} p =
  proj₂ BagMonoid.identity xs ∷ λ t → ♯ right-identity (D t p)

associative : ∀ {Tok R xs₁ xs₂ xs₃}
              (p₁ : Parser Tok R xs₁) (p₂ : Parser Tok R xs₂)
              (p₃ : Parser Tok R xs₃) →
              (p₁ ∣ p₂) ∣ p₃ ≅P p₁ ∣ (p₂ ∣ p₃)
associative {xs₁ = xs₁} p₁ p₂ p₃ =
  BagMonoid.assoc xs₁ _ _ ∷ λ t →
  ♯ associative (D t p₁) (D t p₂) (D t p₃)

-- Note that this law uses language equivalence, not parser
-- equivalence.

idempotent : ∀ {Tok R xs} (p : Parser Tok R xs) → p ∣ p ≈P p
idempotent {xs = xs} p =
  Eq.++-idempotent xs ∷ λ t → ♯ idempotent (D t p)

------------------------------------------------------------------------
-- A lemma which can be convenient when proving distributivity laws

swap : ∀ {Tok R xs₁ xs₂ xs₃ xs₄}
       (p₁ : Parser Tok R xs₁) (p₂ : Parser Tok R xs₂)
       (p₃ : Parser Tok R xs₃) (p₄ : Parser Tok R xs₄) →
       (p₁ ∣ p₂) ∣ (p₃ ∣ p₄) ≅P (p₁ ∣ p₃) ∣ (p₂ ∣ p₄)
swap p₁ p₂ p₃ p₄ =
  (p₁ ∣ p₂) ∣ (p₃ ∣ p₄)  ≅⟨ associative p₁ p₂ (p₃ ∣ p₄) ⟩
  p₁ ∣ (p₂ ∣ (p₃ ∣ p₄))  ≅⟨ (p₁ ∎) ∣ (
    p₂ ∣ (p₃ ∣ p₄)            ≅⟨ sym $ associative p₂ p₃ p₄ ⟩
    (p₂ ∣ p₃) ∣ p₄            ≅⟨ commutative p₂ p₃ ∣ (p₄ ∎) ⟩
    (p₃ ∣ p₂) ∣ p₄            ≅⟨ associative p₃ p₂ p₄ ⟩
    p₃ ∣ (p₂ ∣ p₄)            ∎) ⟩
  p₁ ∣ (p₃ ∣ (p₂ ∣ p₄))  ≅⟨ sym $ associative p₁ p₃ (p₂ ∣ p₄) ⟩
  (p₁ ∣ p₃) ∣ (p₂ ∣ p₄)  ∎
