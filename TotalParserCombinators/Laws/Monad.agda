------------------------------------------------------------------------
-- Laws related to _>>=_
------------------------------------------------------------------------

module TotalParserCombinators.Laws.Monad where

open import Algebra
open import Category.Monad
open import Coinduction
open import Data.List
import Data.List.Any.BagAndSetEquality as BSEq
open import Data.List.Categorical
  using () renaming (module MonadProperties to ListMonad)
open import Function
open import Level

private
  module BagMonoid {k} {A : Set} =
    CommutativeMonoid (BSEq.commutativeMonoid k A)
  open RawMonad {f = zero} Data.List.Categorical.monad
    using () renaming (_>>=_ to _>>=′_)

open import TotalParserCombinators.Derivative
open import TotalParserCombinators.Congruence as Eq
  hiding (return; fail) renaming (_∣_ to _∣′_)
import TotalParserCombinators.Laws.AdditiveMonoid as AdditiveMonoid
open import TotalParserCombinators.Laws.Derivative as Derivative
open import TotalParserCombinators.Laws.ReturnStar as Return⋆
open import TotalParserCombinators.Lib
open import TotalParserCombinators.Parser

------------------------------------------------------------------------
-- _>>=_, return, _∣_ and fail form a monad with a zero and a plus

-- If the laws below are combined with the additive monoid laws this
-- means that we have something which resembles an idempotent semiring
-- (if we restrict ourselves to language equivalence).

-- The zero laws are proved elsewhere.

open Derivative public
  using () renaming (left-zero->>=  to left-zero;
                     right-zero->>= to right-zero)

left-distributive : ∀ {Tok R₁ R₂ xs} {f g : R₁ → List R₂}
                    (p₁ : Parser Tok R₁ xs)
                    (p₂ : (x : R₁) → Parser Tok R₂ (f x))
                    (p₃ : (x : R₁) → Parser Tok R₂ (g x)) →
                    p₁ >>= (λ x → p₂ x ∣ p₃ x) ≅P p₁ >>= p₂ ∣ p₁ >>= p₃
left-distributive {xs = xs} {f} {g} p₁ p₂ p₃ =
  BSEq.>>=-left-distributive xs {f = f} ∷ λ t → ♯ (
    D t (p₁ >>= (λ x → p₂ x ∣ p₃ x))                       ≅⟨ D->>= p₁ (λ x → p₂ x ∣ p₃ x) ⟩

    D t p₁ >>= (λ x → p₂ x ∣ p₃ x) ∣
    return⋆ xs >>= (λ x → D t (p₂ x) ∣ D t (p₃ x))         ≅⟨ left-distributive (D t p₁) p₂ p₃ ∣′
                                                              left-distributive (return⋆ xs)
                                                                (λ x → D t (p₂ x)) (λ x → D t (p₃ x)) ⟩
    (D t p₁ >>= p₂ ∣ D t p₁ >>= p₃) ∣
    (return⋆ xs >>= (λ x → D t (p₂ x)) ∣
     return⋆ xs >>= (λ x → D t (p₃ x)))                    ≅⟨ AdditiveMonoid.swap
                                                               (D t p₁ >>= p₂) (D t p₁ >>= p₃)
                                                               (return⋆ xs >>= (λ x → D t (p₂ x)))
                                                               (return⋆ xs >>= (λ x → D t (p₃ x))) ⟩
    (D t p₁ >>= p₂ ∣ return⋆ xs >>= (λ x → D t (p₂ x))) ∣
    (D t p₁ >>= p₃ ∣ return⋆ xs >>= (λ x → D t (p₃ x)))    ≅⟨ sym (D->>= p₁ p₂ ∣′ D->>= p₁ p₃) ⟩

    D t (p₁ >>= p₂) ∣ D t (p₁ >>= p₃)                      ∎)

right-distributive : ∀ {Tok R₁ R₂ xs₁ xs₂} {f : R₁ → List R₂}
                     (p₁ : Parser Tok R₁ xs₁)
                     (p₂ : Parser Tok R₁ xs₂)
                     (p₃ : (x : R₁) → Parser Tok R₂ (f x)) →
                     (p₁ ∣ p₂) >>= p₃ ≅P p₁ >>= p₃ ∣ p₂ >>= p₃
right-distributive {xs₁ = xs₁} {xs₂} {f} p₁ p₂ p₃ =
  BagMonoid.reflexive (ListMonad.right-distributive xs₁ xs₂ f) ∷ λ t → ♯ (
    D t ((p₁ ∣ p₂) >>= p₃)                                  ≅⟨ D->>= (p₁ ∣ p₂) p₃ ⟩

    (D t p₁ ∣ D t p₂) >>= p₃ ∣
    return⋆ (xs₁ ++ xs₂) >>= (λ x → D t (p₃ x))             ≅⟨ ((D t p₁ ∣ D t p₂) >>= p₃ ∎) ∣′
                                                               [ ○ - ○ - ○ - ○ ] Return⋆.distrib-∣ xs₁ xs₂ >>=
                                                                                 (λ x → D t (p₃ x) ∎) ⟩
    (D t p₁ ∣ D t p₂) >>= p₃ ∣
    (return⋆ xs₁ ∣ return⋆ xs₂) >>= (λ x → D t (p₃ x))      ≅⟨ right-distributive (D t p₁) (D t p₂) p₃ ∣′
                                                               right-distributive (return⋆ xs₁) (return⋆ xs₂)
                                                                                  (λ x → D t (p₃ x)) ⟩
    ((D t p₁ >>= p₃) ∣ (D t p₂ >>= p₃)) ∣
    (return⋆ xs₁ >>= (λ x → D t (p₃ x)) ∣
     return⋆ xs₂ >>= (λ x → D t (p₃ x)))                    ≅⟨ AdditiveMonoid.swap
                                                                 (D t p₁ >>= p₃) (D t p₂ >>= p₃)
                                                                 (return⋆ xs₁ >>= (λ x → D t (p₃ x)))
                                                                 (return⋆ xs₂ >>= (λ x → D t (p₃ x))) ⟩
    (D t p₁ >>= p₃ ∣ return⋆ xs₁ >>= (λ x → D t (p₃ x))) ∣
    (D t p₂ >>= p₃ ∣ return⋆ xs₂ >>= (λ x → D t (p₃ x)))    ≅⟨ sym (D->>= p₁ p₃ ∣′ D->>= p₂ p₃) ⟩

    D t (p₁ >>= p₃) ∣ D t (p₂ >>= p₃)                       ∎)

left-identity : ∀ {Tok R₁ R₂} {f : R₁ → List R₂}
                (x : R₁) (p : (x : R₁) → Parser Tok R₂ (f x)) →
                return x >>= p ≅P p x
left-identity {f = f} x p =
  BagMonoid.reflexive (ListMonad.left-identity x f) ∷ λ t → ♯ (
    D t (return x >>= p)                              ≅⟨ D->>= (return x) p ⟩
    fail >>= p ∣ return⋆ [ x ] >>= (λ x → D t (p x))  ≅⟨ left-zero p ∣′
                                                         [ ○ - ○ - ○ - ○ ] AdditiveMonoid.right-identity (return x) >>=
                                                                           (λ x → D t (p x) ∎) ⟩
    fail ∣ return x >>= (λ x → D t (p x))             ≅⟨ AdditiveMonoid.left-identity (return x >>= (λ x → D t (p x))) ⟩
    return x >>= (λ x → D t (p x))                    ≅⟨ left-identity x (λ x → D t (p x)) ⟩
    D t (p x)                                         ∎)

right-identity : ∀ {Tok R xs}
                 (p : Parser Tok R xs) → p >>= return ≅P p
right-identity {xs = xs} p =
  BagMonoid.reflexive (ListMonad.right-identity xs) ∷ λ t → ♯ (
    D t (p >>= return)                              ≅⟨ D->>= p return ⟩
    D t p >>= return ∣ return⋆ xs >>= (λ _ → fail)  ≅⟨ right-identity (D t p) ∣′ right-zero (return⋆ xs) ⟩
    D t p            ∣ fail                         ≅⟨ AdditiveMonoid.right-identity (D t p) ⟩
    D t p                                           ∎)

associative : ∀ {Tok R₁ R₂ R₃ xs}
                {f : R₁ → List R₂} {g : R₂ → List R₃}
              (p₁ : Parser Tok R₁ xs)
              (p₂ : (x : R₁) → Parser Tok R₂ (f x))
              (p₃ : (x : R₂) → Parser Tok R₃ (g x)) →
              p₁ >>= (λ x → p₂ x >>= p₃) ≅P p₁ >>= p₂ >>= p₃
associative {xs = xs} {f} {g} p₁ p₂ p₃ =
  BagMonoid.reflexive (ListMonad.associative xs f g) ∷ λ t → ♯ (
    D t (p₁ >>= λ x → p₂ x >>= p₃)                               ≅⟨ D->>= p₁ (λ x → p₂ x >>= p₃) ⟩

    D t p₁ >>= (λ x → p₂ x >>= p₃) ∣
    return⋆ xs >>= (λ x → D t (p₂ x >>= p₃))                     ≅⟨ associative (D t p₁) p₂ p₃ ∣′
                                                                    [ ○ - ○ - ○ - ○ ] return⋆ xs ∎ >>= (λ x → D->>= (p₂ x) p₃) ⟩
    D t p₁ >>= p₂ >>= p₃ ∣
    return⋆ xs >>=
      (λ x → D t (p₂ x) >>= p₃ ∣
             return⋆ (f x) >>= λ x → D t (p₃ x))                 ≅⟨ (D t p₁ >>= p₂ >>= p₃ ∎) ∣′
                                                                    left-distributive (return⋆ xs)
                                                                                      (λ x → D t (p₂ x) >>= p₃)
                                                                                      (λ x → return⋆ (f x) >>= (λ x → D t (p₃ x))) ⟩
    D t p₁ >>= p₂ >>= p₃ ∣
    (return⋆ xs >>= (λ x → D t (p₂ x) >>= p₃) ∣
     return⋆ xs >>= (λ x → return⋆ (f x) >>= λ x → D t (p₃ x)))  ≅⟨ (D t p₁ >>= p₂ >>= p₃ ∎) ∣′
                                                                    (associative (return⋆ xs) (λ x → D t (p₂ x)) p₃ ∣′
                                                                     associative (return⋆ xs) (return⋆ ∘ f) (λ x → D t (p₃ x))) ⟩
    D t p₁ >>= p₂ >>= p₃ ∣
    (return⋆ xs >>= (λ x → D t (p₂ x)) >>= p₃ ∣
     return⋆ xs >>= (return⋆ ∘ f) >>= λ x → D t (p₃ x))          ≅⟨ sym $ AdditiveMonoid.associative
                                                                            (D t p₁ >>= p₂ >>= p₃)
                                                                            (return⋆ xs >>= (λ x → D t (p₂ x)) >>= p₃)
                                                                            (return⋆ xs >>= (return⋆ ∘ f) >>= (λ x → D t (p₃ x))) ⟩
    D t p₁ >>= p₂ >>= p₃ ∣
    return⋆ xs >>= (λ x → D t (p₂ x)) >>= p₃ ∣
    return⋆ xs >>= (return⋆ ∘ f) >>= (λ x → D t (p₃ x))          ≅⟨ sym (right-distributive
                                                                           (D t p₁ >>= p₂)
                                                                           (return⋆ xs >>= (λ x → D t (p₂ x)))
                                                                           p₃) ∣′
                                                                    [ ○ - ○ - ○ - ○ ] sym (Return⋆.distrib->>= xs f) >>=
                                                                                      (λ x → D t (p₃ x) ∎) ⟩
    (D t p₁ >>= p₂ ∣
     return⋆ xs >>= (λ x → D t (p₂ x))) >>= p₃ ∣
    return⋆ (xs >>=′ f) >>= (λ x → D t (p₃ x))                   ≅⟨ [ ○ - ○ - ○ - ○ ] sym (D->>= p₁ p₂) >>= (λ x → p₃ x ∎) ∣′
                                                                    (return⋆ (xs >>=′ f) >>= (λ x → D t (p₃ x)) ∎) ⟩
    D t (p₁ >>= p₂) >>= p₃ ∣
    return⋆ (xs >>=′ f) >>= (λ x → D t (p₃ x))                   ≅⟨ sym $ D->>= (p₁ >>= p₂) p₃ ⟩

    D t (p₁ >>= p₂ >>= p₃)                                       ∎)
