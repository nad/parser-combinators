------------------------------------------------------------------------
-- Laws related to _⊙_ and return
------------------------------------------------------------------------

module TotalParserCombinators.Laws.ApplicativeFunctor where

open import Algebra
open import Coinduction
open import Data.List
import Data.List.Any.BagAndSetEquality as BSEq
open import Function

private
  module BagMonoid {A : Set} =
    CommutativeMonoid (BSEq.commutativeMonoid _ A)

open import TotalParserCombinators.Applicative as ⊛ using (_⊛′_)
open import TotalParserCombinators.BreadthFirst
open import TotalParserCombinators.Coinduction
open import TotalParserCombinators.Congruence as Eq
import TotalParserCombinators.Laws.AdditiveMonoid as AdditiveMonoid
open import TotalParserCombinators.Laws.Derivative as Derivative
import TotalParserCombinators.Laws.ReturnStar as Return⋆
open import TotalParserCombinators.Lib
open import TotalParserCombinators.Parser
open import TotalParserCombinators.Semantics

------------------------------------------------------------------------
-- _⊙_ and _⊛_ are equivalent

⊙≅⊛ : ∀ {Tok R₁ R₂ fs xs}
      (p₁ : ∞? (Parser Tok (R₁ → R₂) fs) xs)
      (p₂ : ∞? (Parser Tok R₁        xs) fs) →
      ♭? p₁ ⊙ ♭? p₂ ≅P p₁ ⊛ p₂
⊙≅⊛ {fs = fs} {xs} p₁ p₂ =
  ♭? p₁ ⊙ ♭? p₂  ≅⟨ Eq.complete (♭♯.correct xs) ⊛
                    Eq.complete (♭♯.correct fs {♭? p₂}) ⟩
  p₁    ⊛ p₂     ∎

------------------------------------------------------------------------
-- _⊙_, return, _∣_ and fail form an applicative functor "with a zero
-- and a plus"

-- Together with the additive monoid laws we get something which
-- resembles an idempotent semiring (if we restrict ourselves to
-- language equivalence).

-- The zero lemmas are proved elsewhere.

open Derivative public
  using () renaming (left-zero-⊙  to left-zero;
                     right-zero-⊙ to right-zero)

-- _⊙_ distributes from the left over _∣_.

left-distributive : ∀ {Tok R₁ R₂ fs xs₁ xs₂}
                    (p₁ : Parser Tok (R₁ → R₂) fs)
                    (p₂ : Parser Tok R₁ xs₁)
                    (p₃ : Parser Tok R₁ xs₂) →
                    p₁ ⊙ (p₂ ∣ p₃) ≅P p₁ ⊙ p₂ ∣ p₁ ⊙ p₃
left-distributive {fs = fs} {xs₁} p₁ p₂ p₃ =
  BagMonoid.reflexive (⊛.left-distributive xs₁) ∷ λ t → ♯ (
    ∂ (p₁ ⊙ (p₂ ∣ p₃)) t                         ≅⟨ ∂-⊙ p₁ (p₂ ∣ p₃) ⟩

    ∂ p₁ t ⊙ (p₂ ∣ p₃) ∣
    return⋆ fs ⊙ ∂ (p₂ ∣ p₃) t                   ≅⟨ left-distributive (∂ p₁ t) p₂ p₃ ∣
                                                    left-distributive (return⋆ fs) (∂ p₂ t) (∂ p₃ t) ⟩
    (∂ p₁ t ⊙ p₂ ∣ ∂ p₁ t ⊙ p₃) ∣
    (return⋆ fs ⊙ ∂ p₂ t ∣ return⋆ fs ⊙ ∂ p₃ t)  ≅⟨ AdditiveMonoid.swap
                                                      (∂ p₁ t ⊙ p₂) (∂ p₁ t ⊙ p₃)
                                                      (return⋆ fs ⊙ ∂ p₂ t) (return⋆ fs ⊙ ∂ p₃ t) ⟩
    (∂ p₁ t ⊙ p₂ ∣ return⋆ fs ⊙ ∂ p₂ t) ∣
    (∂ p₁ t ⊙ p₃ ∣ return⋆ fs ⊙ ∂ p₃ t)          ≅⟨ sym (∂-⊙ p₁ p₂) ∣ sym (∂-⊙ p₁ p₃) ⟩

    ∂ (p₁ ⊙ p₂) t ∣ ∂ (p₁ ⊙ p₃) t                ∎)

-- _⊙_ distributes from the right over _∣_.

right-distributive : ∀ {Tok R₁ R₂ fs₁ fs₂ xs}
                     (p₁ : Parser Tok (R₁ → R₂) fs₁)
                     (p₂ : Parser Tok (R₁ → R₂) fs₂)
                     (p₃ : Parser Tok R₁ xs) →
                     (p₁ ∣ p₂) ⊙ p₃ ≅P p₁ ⊙ p₃ ∣ p₂ ⊙ p₃
right-distributive {fs₁ = fs₁} {fs₂} {xs} p₁ p₂ p₃ =
  ⊛.right-distributive xs ∷ λ t → ♯ (
    ∂ ((p₁ ∣ p₂) ⊙ p₃) t                           ≅⟨ ∂-⊙ (p₁ ∣ p₂) p₃ ⟩

    ∂ (p₁ ∣ p₂) t ⊙ p₃ ∣
    return⋆ (fs₁ ++ fs₂) ⊙ ∂ p₃ t                  ≅⟨ (∂ (p₁ ∣ p₂) t ⊙ p₃ ∎) ∣
                                                      Return⋆.distrib-∣ fs₁ fs₂ ⊙′ (∂ p₃ t ∎) ⟩
    ∂ (p₁ ∣ p₂) t ⊙ p₃ ∣
    (return⋆ fs₁ ∣ return⋆ fs₂) ⊙ ∂ p₃ t           ≅⟨ right-distributive (∂ p₁ t) (∂ p₂ t) p₃ ∣
                                                      right-distributive (return⋆ fs₁) (return⋆ fs₂) (∂ p₃ t) ⟩
    (∂ p₁ t ⊙ p₃ ∣ ∂ p₂ t ⊙ p₃) ∣
    (return⋆ fs₁ ⊙ ∂ p₃ t ∣ return⋆ fs₂ ⊙ ∂ p₃ t)  ≅⟨ AdditiveMonoid.swap
                                                        (∂ p₁ t ⊙ p₃) (∂ p₂ t ⊙ p₃)
                                                        (return⋆ fs₁ ⊙ ∂ p₃ t) (return⋆ fs₂ ⊙ ∂ p₃ t) ⟩
    (∂ p₁ t ⊙ p₃ ∣ return⋆ fs₁ ⊙ ∂ p₃ t) ∣
    (∂ p₂ t ⊙ p₃ ∣ return⋆ fs₂ ⊙ ∂ p₃ t)           ≅⟨ sym $ ∂-⊙ p₁ p₃ ∣ ∂-⊙ p₂ p₃ ⟩

    ∂ (p₁ ⊙ p₃) t ∣ ∂ (p₂ ⊙ p₃) t                  ∎)

identity : ∀ {Tok R xs} (p : Parser Tok R xs) → return id ⊙ p ≅P p
identity {xs = xs} p =
  BagMonoid.reflexive (⊛.identity xs) ∷ λ t → ♯ (
    ∂ (return id ⊙ p) t                    ≅⟨ ∂-⊙ (return id) p ⟩
    fail ⊙ p ∣ (return id ∣ fail) ⊙ ∂ p t  ≅⟨ left-zero p ∣
                                              AdditiveMonoid.right-identity (return id) ⊙′ (∂ p t ∎) ⟩
    fail ∣ return id ⊙ ∂ p t               ≅⟨ AdditiveMonoid.left-identity (return id ⊙ ∂ p t) ⟩
    return id ⊙ ∂ p t                      ≅⟨ identity (∂ p t) ⟩
    ∂ p t                                  ∎)

homomorphism : ∀ {Tok R₁ R₂} (f : R₁ → R₂) (x : R₁) →
               return f ⊙ return x ≅P return {Tok = Tok} (f x)
homomorphism f x = BagMonoid.refl ∷ λ t → ♯ (
  ∂ (return f ⊙ return x) t  ≅⟨ ∂-return-⊙ f (return x) {t} ⟩
  return f ⊙ fail            ≅⟨ right-zero (return f) ⟩
  fail                       ≅⟨ fail ∎ ⟩
  ∂ (return (f x)) t         ∎)

composition :
  ∀ {Tok R₁ R₂ R₃ fs gs xs}
  (p₁ : Parser Tok (R₂ → R₃) fs)
  (p₂ : Parser Tok (R₁ → R₂) gs)
  (p₃ : Parser Tok R₁        xs) →
  return _∘′_ ⊙ p₁ ⊙ p₂ ⊙ p₃ ≅P p₁ ⊙ (p₂ ⊙ p₃)
composition {fs = fs} {gs} {xs} p₁ p₂ p₃ =
  BagMonoid.reflexive (⊛.composition fs gs xs) ∷ λ t → ♯ (
    ∂ (return _∘′_ ⊙ p₁ ⊙ p₂ ⊙ p₃) t                 ≅⟨ ∂-⊙ (return _∘′_ ⊙ p₁ ⊙ p₂) p₃ ⟩

    ∂ (return _∘′_ ⊙ p₁ ⊙ p₂) t ⊙ p₃ ∣
    return⋆ ([ _∘′_ ] ⊛′ fs ⊛′ gs) ⊙ ∂ p₃ t          ≅⟨ ∂-⊙ (return _∘′_ ⊙ p₁) p₂ ⊙′ (p₃ ∎) ∣
                                                        Return⋆.distrib-⊙ ([ _∘′_ ] ⊛′ fs) gs ⊙′ (∂ p₃ t ∎) ⟩
    (∂ (return _∘′_ ⊙ p₁) t ⊙ p₂ ∣
     return⋆ ([ _∘′_ ] ⊛′ fs) ⊙ ∂ p₂ t) ⊙ p₃ ∣
    return⋆ ([ _∘′_ ] ⊛′ fs) ⊙ return⋆ gs ⊙ ∂ p₃ t   ≅⟨ (∂-return-⊙ _∘′_ p₁ ⊙′ (p₂ ∎) ∣
                                                         distrib-⊙′ _∘′_ fs ⊙′ (∂ p₂ t ∎)) ⊙′ (p₃ ∎) ∣
                                                        distrib-⊙′ _∘′_ fs ⊙′ (return⋆ gs ∎) ⊙′ (∂ p₃ t ∎) ⟩
    (return _∘′_ ⊙ ∂ p₁ t ⊙ p₂ ∣
     return _∘′_ ⊙ return⋆ fs ⊙ ∂ p₂ t) ⊙ p₃ ∣
    return _∘′_ ⊙ return⋆ fs ⊙ return⋆ gs ⊙ ∂ p₃ t   ≅⟨ right-distributive (return _∘′_ ⊙ ∂ p₁ t ⊙ p₂)
                                                                           (return _∘′_ ⊙ return⋆ fs ⊙ ∂ p₂ t) p₃ ∣
                                                        (return _∘′_ ⊙ return⋆ fs ⊙ return⋆ gs ⊙ ∂ p₃ t ∎) ⟩
    return _∘′_ ⊙ ∂ p₁ t ⊙ p₂ ⊙ p₃ ∣
    return _∘′_ ⊙ return⋆ fs ⊙ ∂ p₂ t ⊙ p₃ ∣
    return _∘′_ ⊙ return⋆ fs ⊙ return⋆ gs ⊙ ∂ p₃ t   ≅⟨ composition (∂ p₁ t) p₂ p₃ ∣
                                                        composition (return⋆ fs) (∂ p₂ t) p₃ ∣
                                                        composition (return⋆ fs) (return⋆ gs) (∂ p₃ t) ⟩
    ∂ p₁ t ⊙ (p₂ ⊙ p₃) ∣
    return⋆ fs ⊙ (∂ p₂ t ⊙ p₃) ∣
    return⋆ fs ⊙ (return⋆ gs ⊙ ∂ p₃ t)               ≅⟨ AdditiveMonoid.associative
                                                          (∂ p₁ t ⊙ (p₂ ⊙ p₃))
                                                          (return⋆ fs ⊙ (∂ p₂ t ⊙ p₃))
                                                          (return⋆ fs ⊙ (return⋆ gs ⊙ ∂ p₃ t)) ⟩
    ∂ p₁ t ⊙ (p₂ ⊙ p₃) ∣
    (return⋆ fs ⊙ (∂ p₂ t ⊙ p₃) ∣
     return⋆ fs ⊙ (return⋆ gs ⊙ ∂ p₃ t))             ≅⟨ sym $ (∂ p₁ t ⊙ (p₂ ⊙ p₃) ∎) ∣
                                                              left-distributive
                                                                (return⋆ fs) (∂ p₂ t ⊙ p₃) (return⋆ gs ⊙ ∂ p₃ t) ⟩
    ∂ p₁ t ⊙ (p₂ ⊙ p₃) ∣
    return⋆ fs ⊙ (∂ p₂ t ⊙ p₃ ∣
                   return⋆ gs ⊙ ∂ p₃ t)              ≅⟨ sym $ (∂ p₁ t ⊙ (p₂ ⊙ p₃) ∎) ∣ (return⋆ fs ∎) ⊙′ ∂-⊙ p₂ p₃ ⟩

    ∂ p₁ t ⊙ (p₂ ⊙ p₃) ∣ return⋆ fs ⊙ ∂ (p₂ ⊙ p₃) t  ≅⟨ sym $ ∂-⊙ p₁ (p₂ ⊙ p₃) ⟩

    ∂ (p₁ ⊙ (p₂ ⊙ p₃)) t                             ∎)
  where
  distrib-⊙′ : ∀ {Tok R₁ R₂} (f : R₁ → R₂) xs →
               return⋆ {Tok = Tok} ([ f ] ⊛′ xs) ≅P
               return f ⊙ return⋆ xs
  distrib-⊙′ f xs =
    return⋆ ([ f ] ⊛′ xs)           ≅⟨ Return⋆.distrib-⊙ [ f ] xs ⟩
    (return f ∣ fail) ⊙ return⋆ xs  ≅⟨ AdditiveMonoid.right-identity (return f) ⊙′
                                         (return⋆ xs ∎) ⟩
    return f ⊙ return⋆ xs           ∎

interchange : ∀ {Tok R₁ R₂ fs}
              (p : Parser Tok (R₁ → R₂) fs) (x : R₁) →
              p ⊙ return x ≅P return (λ f → f x) ⊙ p
interchange {fs = fs} p x =
  BagMonoid.reflexive (⊛.interchange fs) ∷ λ t → ♯ (
    ∂ (p ⊙ return x) t            ≅⟨ ∂-⊙-return p x ⟩
    ∂ p t ⊙ return x              ≅⟨ interchange (∂ p t) x ⟩
    return (λ f → f x) ⊙ ∂ p t    ≅⟨ sym $ ∂-return-⊙ (λ f → f x) p ⟩
    ∂ (return (λ f → f x) ⊙ p) t  ∎)
