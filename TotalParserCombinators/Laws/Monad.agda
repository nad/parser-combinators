------------------------------------------------------------------------
-- Laws related to _>>=_
------------------------------------------------------------------------

module TotalParserCombinators.Laws.Monad where

open import Algebra
open import Category.Monad
open import Coinduction
open import Data.List as List
import Data.List.Any.BagAndSetEquality as BSEq
import Data.List.Properties as ListProp
open import Function

private
  module BagMonoid {A : Set} =
    CommutativeMonoid (BSEq.commutativeMonoid _ A)
  open module ListMonad = RawMonad List.monad
         using () renaming (_>>=_ to _>>=′_)

open import TotalParserCombinators.BreadthFirst
open import TotalParserCombinators.Coinduction
open import TotalParserCombinators.Congruence as Eq
import TotalParserCombinators.Laws.AdditiveMonoid as AdditiveMonoid
open import TotalParserCombinators.Laws.Derivative as Derivative
  hiding (>>=!≅>>=)
open import TotalParserCombinators.Laws.ReturnStar as Return⋆
open import TotalParserCombinators.Lib
open import TotalParserCombinators.Parser
open import TotalParserCombinators.Semantics

------------------------------------------------------------------------
-- _>>=_, _>>=!_ and _≫=_ are equivalent (where their domains overlap)

open Derivative public using (>>=!≅>>=)

≫=≅>>= : ∀ {Tok R₁ R₂ xs} {f : R₁ → List R₂}
         (p₁ : Parser Tok R₁ xs)
         (p₂ : (x : R₁) → ∞? (Parser Tok R₂ (f x)) xs) →
         p₁ ≫= (♭? ∘ p₂) ≅P p₁ >>= p₂
≫=≅>>= {xs = xs} p₁ p₂ =
  p₁ ≫= (♭? ∘ p₂)  ≅⟨ (p₁ ∎) >>= (λ _ → Eq.complete (♭♯.correct xs)) ⟩
  p₁ >>= p₂        ∎

>>=!≅≫= : ∀ {Tok R₁ R₂ xs}
          (p₁ : ∞ (Parser Tok R₁ xs))
          (p₂ : (x : R₁) → ∞? (Parser Tok R₂ []) xs) →
          p₁ >>=! p₂ ≅P ♭ p₁ ≫= (♭? ∘ p₂)
>>=!≅≫= p₁ p₂ =
  p₁   >>=! p₂        ≅⟨ >>=!≅>>= p₁ p₂ ⟩
  ♭ p₁ >>=  p₂        ≅⟨ sym $ ≫=≅>>= (♭ p₁) p₂ ⟩
  ♭ p₁  ≫= (♭? ∘ p₂)  ∎

------------------------------------------------------------------------
-- _≫=_, return, _∣_ and fail form a monad with a zero and a plus

-- If the laws below are combined with the additive monoid laws this
-- means that we have something which resembles an idempotent semiring
-- (if we restrict ourselves to language equivalence).

-- The zero laws are proved elsewhere.

open Derivative public
  using () renaming (left-zero-≫=  to left-zero;
                     right-zero-≫= to right-zero)

left-distributive : ∀ {Tok R₁ R₂ xs} {f g : R₁ → List R₂}
                    (p₁ : Parser Tok R₁ xs)
                    (p₂ : (x : R₁) → Parser Tok R₂ (f x))
                    (p₃ : (x : R₁) → Parser Tok R₂ (g x)) →
                    p₁ ≫= (λ x → p₂ x ∣ p₃ x) ≅P p₁ ≫= p₂ ∣ p₁ ≫= p₃
left-distributive {xs = xs} {f} {g} p₁ p₂ p₃ =
  BSEq.>>=-left-distributive xs ∷ λ t → ♯ (
    ∂ (p₁ ≫= (λ x → p₂ x ∣ p₃ x)) t                      ≅⟨ ∂-≫= p₁ (λ x → p₂ x ∣ p₃ x) ⟩

    ∂ p₁ t ≫= (λ x → p₂ x ∣ p₃ x) ∣
    return⋆ xs ≫= (λ x → ∂ (p₂ x) t ∣ ∂ (p₃ x) t)        ≅⟨ left-distributive (∂ p₁ t) p₂ p₃ ∣
                                                            left-distributive (return⋆ xs)
                                                              (λ x → ∂ (p₂ x) t) (λ x → ∂ (p₃ x) t) ⟩
    (∂ p₁ t ≫= p₂ ∣ ∂ p₁ t ≫= p₃) ∣
    (return⋆ xs ≫= (λ x → ∂ (p₂ x) t) ∣
     return⋆ xs ≫= (λ x → ∂ (p₃ x) t))                   ≅⟨ AdditiveMonoid.swap
                                                              (∂ p₁ t ≫= p₂) (∂ p₁ t ≫= p₃)
                                                              (return⋆ xs ≫= (λ x → ∂ (p₂ x) t))
                                                              (return⋆ xs ≫= (λ x → ∂ (p₃ x) t)) ⟩
    (∂ p₁ t ≫= p₂ ∣ return⋆ xs ≫= (λ x → ∂ (p₂ x) t)) ∣
    (∂ p₁ t ≫= p₃ ∣ return⋆ xs ≫= (λ x → ∂ (p₃ x) t))    ≅⟨ sym (∂-≫= p₁ p₂ ∣ ∂-≫= p₁ p₃) ⟩

    ∂ (p₁ ≫= p₂) t ∣ ∂ (p₁ ≫= p₃) t                      ∎)

right-distributive : ∀ {Tok R₁ R₂ xs₁ xs₂} {f : R₁ → List R₂}
                     (p₁ : Parser Tok R₁ xs₁)
                     (p₂ : Parser Tok R₁ xs₂)
                     (p₃ : (x : R₁) → Parser Tok R₂ (f x)) →
                     (p₁ ∣ p₂) ≫= p₃ ≅P p₁ ≫= p₃ ∣ p₂ ≫= p₃
right-distributive {xs₁ = xs₁} {xs₂} {f} p₁ p₂ p₃ =
  BagMonoid.reflexive (ListProp.Monad.right-distributive xs₁ xs₂ f) ∷ λ t → ♯ (
    ∂ ((p₁ ∣ p₂) ≫= p₃) t                                 ≅⟨ ∂-≫= (p₁ ∣ p₂) p₃ ⟩

    (∂ p₁ t ∣ ∂ p₂ t) ≫= p₃ ∣
    return⋆ (xs₁ ++ xs₂) ≫= (λ x → ∂ (p₃ x) t)            ≅⟨ ((∂ p₁ t ∣ ∂ p₂ t) ≫= p₃ ∎) ∣
                                                             Return⋆.distrib-∣ xs₁ xs₂ ≫=′ (λ x → ∂ (p₃ x) t ∎) ⟩
    (∂ p₁ t ∣ ∂ p₂ t) ≫= p₃ ∣
    (return⋆ xs₁ ∣ return⋆ xs₂) ≫= (λ x → ∂ (p₃ x) t)     ≅⟨ right-distributive (∂ p₁ t) (∂ p₂ t) p₃ ∣
                                                             right-distributive (return⋆ xs₁) (return⋆ xs₂)
                                                                                (λ x → ∂ (p₃ x) t) ⟩
    ((∂ p₁ t ≫= p₃) ∣ (∂ p₂ t ≫= p₃)) ∣
    (return⋆ xs₁ ≫= (λ x → ∂ (p₃ x) t) ∣
     return⋆ xs₂ ≫= (λ x → ∂ (p₃ x) t))                   ≅⟨ AdditiveMonoid.swap
                                                               (∂ p₁ t ≫= p₃) (∂ p₂ t ≫= p₃)
                                                               (return⋆ xs₁ ≫= (λ x → ∂ (p₃ x) t))
                                                               (return⋆ xs₂ ≫= (λ x → ∂ (p₃ x) t)) ⟩
    (∂ p₁ t ≫= p₃ ∣ return⋆ xs₁ ≫= (λ x → ∂ (p₃ x) t)) ∣
    (∂ p₂ t ≫= p₃ ∣ return⋆ xs₂ ≫= (λ x → ∂ (p₃ x) t))    ≅⟨ sym (∂-≫= p₁ p₃ ∣ ∂-≫= p₂ p₃) ⟩

    ∂ (p₁ ≫= p₃) t ∣ ∂ (p₂ ≫= p₃) t                       ∎)

left-identity : ∀ {Tok R₁ R₂} {f : R₁ → List R₂}
                (x : R₁) (p : (x : R₁) → Parser Tok R₂ (f x)) →
                return x ≫= p ≅P p x
left-identity {f = f} x p =
  BagMonoid.reflexive (ListProp.Monad.left-identity x f) ∷ λ t → ♯ (
    ∂ (return x ≫= p) t                             ≅⟨ ∂-≫= (return x) p ⟩
    fail ≫= p ∣ return⋆ [ x ] ≫= (λ x → ∂ (p x) t)  ≅⟨ left-zero p ∣
                                                       AdditiveMonoid.right-identity (return x) ≫=′ (λ x → ∂ (p x) t ∎) ⟩
    fail ∣ return x ≫= (λ x → ∂ (p x) t)            ≅⟨ AdditiveMonoid.left-identity (return x ≫= (λ x → ∂ (p x) t)) ⟩
    return x ≫= (λ x → ∂ (p x) t)                   ≅⟨ left-identity x (λ x → ∂ (p x) t) ⟩
    ∂ (p x) t                                       ∎)

right-identity : ∀ {Tok R xs}
                 (p : Parser Tok R xs) → p ≫= return ≅P p
right-identity {xs = xs} p =
  BagMonoid.reflexive (ListProp.Monad.right-identity xs) ∷ λ t → ♯ (
    ∂ (p ≫= return) t                             ≅⟨ ∂-≫= p return ⟩
    ∂ p t ≫= return ∣ return⋆ xs ≫= (λ _ → fail)  ≅⟨ right-identity (∂ p t) ∣ right-zero (return⋆ xs) ⟩
    ∂ p t           ∣ fail                        ≅⟨ AdditiveMonoid.right-identity (∂ p t) ⟩
    ∂ p t                                         ∎)

associative : ∀ {Tok R₁ R₂ R₃ xs}
                {f : R₁ → List R₂} {g : R₂ → List R₃}
              (p₁ : Parser Tok R₁ xs)
              (p₂ : (x : R₁) → Parser Tok R₂ (f x))
              (p₃ : (x : R₂) → Parser Tok R₃ (g x)) →
              (p₁ ≫= λ x → p₂ x ≫= p₃) ≅P p₁ ≫= p₂ ≫= p₃
associative {xs = xs} {f} {g} p₁ p₂ p₃ =
  BagMonoid.reflexive (ListProp.Monad.associative xs f g) ∷ λ t → ♯ (
    ∂ (p₁ ≫= λ x → p₂ x ≫= p₃) t                               ≅⟨ ∂-≫= p₁ (λ x → p₂ x ≫= p₃) ⟩

    ∂ p₁ t ≫= (λ x → p₂ x ≫= p₃) ∣
    return⋆ xs ≫= (λ x → ∂ (p₂ x ≫= p₃) t)                     ≅⟨ associative (∂ p₁ t) p₂ p₃ ∣
                                                                  (return⋆ xs ∎) ≫=′ (λ x → ∂-≫= (p₂ x) p₃) ⟩
    ∂ p₁ t ≫= p₂ ≫= p₃ ∣
    return⋆ xs ≫=
      (λ x → ∂ (p₂ x) t ≫= p₃ ∣
             return⋆ (f x) ≫= λ x → ∂ (p₃ x) t)                ≅⟨ (∂ p₁ t ≫= p₂ ≫= p₃ ∎) ∣
                                                                  left-distributive (return⋆ xs)
                                                                                    (λ x → ∂ (p₂ x) t ≫= p₃)
                                                                                    (λ x → return⋆ (f x) ≫= (λ x → ∂ (p₃ x) t)) ⟩
    ∂ p₁ t ≫= p₂ ≫= p₃ ∣
    (return⋆ xs ≫= (λ x → ∂ (p₂ x) t ≫= p₃) ∣
     return⋆ xs ≫= (λ x → return⋆ (f x) ≫= λ x → ∂ (p₃ x) t))  ≅⟨ (∂ p₁ t ≫= p₂ ≫= p₃ ∎) ∣
                                                                  (associative (return⋆ xs) (λ x → ∂ (p₂ x) t) p₃ ∣
                                                                   associative (return⋆ xs) (return⋆ ∘ f) (λ x → ∂ (p₃ x) t)) ⟩
    ∂ p₁ t ≫= p₂ ≫= p₃ ∣
    (return⋆ xs ≫= (λ x → ∂ (p₂ x) t) ≫= p₃ ∣
     return⋆ xs ≫= (return⋆ ∘ f) ≫= λ x → ∂ (p₃ x) t)          ≅⟨ sym $ AdditiveMonoid.associative
                                                                          (∂ p₁ t ≫= p₂ ≫= p₃)
                                                                          (return⋆ xs ≫= (λ x → ∂ (p₂ x) t) ≫= p₃)
                                                                          (return⋆ xs ≫= (return⋆ ∘ f) ≫= (λ x → ∂ (p₃ x) t)) ⟩
    ∂ p₁ t ≫= p₂ ≫= p₃ ∣
    return⋆ xs ≫= (λ x → ∂ (p₂ x) t) ≫= p₃ ∣
    return⋆ xs ≫= (return⋆ ∘ f) ≫= (λ x → ∂ (p₃ x) t)          ≅⟨ sym (right-distributive
                                                                         (∂ p₁ t ≫= p₂)
                                                                         (return⋆ xs ≫= (λ x → ∂ (p₂ x) t))
                                                                         p₃) ∣
                                                                  sym (Return⋆.distrib-≫= xs f) ≫=′ (λ x → ∂ (p₃ x) t ∎) ⟩
    (∂ p₁ t ≫= p₂ ∣
     return⋆ xs ≫= (λ x → ∂ (p₂ x) t)) ≫= p₃ ∣
    return⋆ (xs >>=′ f) ≫= (λ x → ∂ (p₃ x) t)                  ≅⟨ sym (∂-≫= p₁ p₂) ≫=′ (λ x → p₃ x ∎) ∣
                                                                  (return⋆ (xs >>=′ f) ≫= (λ x → ∂ (p₃ x) t) ∎) ⟩
    ∂ (p₁ ≫= p₂) t ≫= p₃ ∣
    return⋆ (xs >>=′ f) ≫= (λ x → ∂ (p₃ x) t)                  ≅⟨ sym $ ∂-≫= (p₁ ≫= p₂) p₃ ⟩

    ∂ (p₁ ≫= p₂ ≫= p₃) t                                       ∎)
