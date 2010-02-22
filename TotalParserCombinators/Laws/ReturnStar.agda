------------------------------------------------------------------------
-- Laws related to return⋆
------------------------------------------------------------------------

module TotalParserCombinators.Laws.ReturnStar where

open import Algebra
open import Category.Monad
open import Coinduction
open import Data.List as List
import Data.List.Any as Any
import Data.List.Any.BagAndSetEquality as Eq
open import Function

open Any.Membership-≡ using () renaming (_≈[_]_ to _List-≈[_]_)
private
  module BagMonoid {A : Set} =
    CommutativeMonoid (Eq.commutativeMonoid Any.Membership-≡.bag A)
  open module ListMonad = RawMonad List.monad
    using () renaming (_>>=_ to _>>=′_)

open import TotalParserCombinators.Applicative using (_⊛′_)
open import TotalParserCombinators.BreadthFirst
open import TotalParserCombinators.Congruence
import TotalParserCombinators.Laws.AdditiveMonoid as AdditiveMonoid
open import TotalParserCombinators.Laws.Derivative
open import TotalParserCombinators.Lib
open import TotalParserCombinators.Parser
open import TotalParserCombinators.Semantics

-- return⋆ preserves equality.

cong : ∀ {k Tok R} {xs₁ xs₂ : List R} →
       xs₁ List-≈[ k ] xs₂ → return⋆ {Tok = Tok} xs₁ ≈[ k ]P return⋆ xs₂
cong {xs₁ = xs₁} {xs₂} xs₁≈xs₂ = xs₁≈xs₂ ∷ λ t → ♯ (
  ∂ (return⋆ xs₁) t  ≅⟨ ∂-return⋆ xs₁ ⟩
  fail               ≅⟨ sym $ ∂-return⋆ xs₂ ⟩
  ∂ (return⋆ xs₂) t  ∎)

-- return⋆ is homomorphic with respect to _++_/_∣_.

distrib-∣ :
  ∀ {Tok R} (xs₁ xs₂ : List R) →
  return⋆ {Tok = Tok} (xs₁ ++ xs₂) ≅P return⋆ xs₁ ∣ return⋆ xs₂
distrib-∣ xs₁ xs₂ =
  BagMonoid.refl ∷ λ t → ♯ (
    ∂ (return⋆ (xs₁ ++ xs₂)) t             ≅⟨ ∂-return⋆ (xs₁ ++ xs₂) ⟩
    fail                                   ≅⟨ sym $ AdditiveMonoid.left-identity fail ⟩
    fail ∣ fail                            ≅⟨ sym $ ∂-return⋆ xs₁ ∣ ∂-return⋆ xs₂ ⟩
    ∂ (return⋆ xs₁) t ∣ ∂ (return⋆ xs₂) t  ∎)

-- return⋆ is homomorphic with respect to _⊛′_/_⊙_.

distrib-⊙ :
  ∀ {Tok R₁ R₂} (fs : List (R₁ → R₂)) xs →
  return⋆ {Tok = Tok} (fs ⊛′ xs) ≅P return⋆ fs ⊙ return⋆ xs
distrib-⊙ fs xs =
  BagMonoid.refl ∷ λ t → ♯ (
    ∂ (return⋆ (fs ⊛′ xs)) t         ≅⟨ ∂-return⋆ (fs ⊛′ xs) ⟩

    fail                             ≅⟨ sym $ AdditiveMonoid.left-identity fail ⟩

    fail ∣ fail                      ≅⟨ sym $ left-zero-⊙ (return⋆ xs) ∣
                                              right-zero-⊙ (return⋆ fs) ⟩
    fail ⊙ return⋆ xs ∣
    return⋆ fs ⊙ fail                ≅⟨ sym $ ∂-return⋆ fs ⊙′ (return⋆ xs ∎) ∣
                                              (return⋆ fs ∎) ⊙′ ∂-return⋆ xs ⟩
    ∂ (return⋆ fs) t ⊙ return⋆ xs ∣
    return⋆ fs ⊙ ∂ (return⋆ xs) t    ≅⟨ sym $ ∂-⊙ (return⋆ fs) (return⋆ xs) ⟩

    ∂ (return⋆ fs ⊙ return⋆ xs) t    ∎)

-- return⋆ is homomorphic with respect to _>>=′_/_≫=_.

distrib-≫= :
  ∀ {Tok R₁ R₂} xs (f : R₁ → List R₂) →
  return⋆ {Tok = Tok} (xs >>=′ f) ≅P return⋆ xs ≫= (return⋆ ∘ f)
distrib-≫= xs f =
  BagMonoid.refl ∷ λ t → ♯ (
    ∂ (return⋆ (xs >>=′ f)) t                  ≅⟨ ∂-return⋆ (xs >>=′ f) ⟩

    fail                                       ≅⟨ sym $ AdditiveMonoid.left-identity fail ⟩

    fail ∣ fail                                ≅⟨ sym $ left-zero-≫=  (return⋆ ∘ f) ∣
                                                        right-zero-≫= (return⋆ xs) ⟩

    fail ≫= (return⋆ ∘ f) ∣
    return⋆ xs ≫= (λ _ → fail)                 ≅⟨ sym $ ∂-return⋆ xs ≫=′ (λ x → return⋆ (f x) ∎) ∣
                                                        (return⋆ xs ∎) ≫=′ (λ x → ∂-return⋆ (f x)) ⟩
    ∂ (return⋆ xs) t ≫= (return⋆ ∘ f) ∣
    return⋆ xs ≫= (λ x → ∂ (return⋆ (f x)) t)  ≅⟨ sym $ ∂-≫= (return⋆ xs) (return⋆ ∘ f) ⟩

    ∂ (return⋆ xs ≫= (return⋆ ∘ f)) t          ∎)
