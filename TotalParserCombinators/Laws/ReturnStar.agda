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
open import Level

open Any.Membership-≡ using () renaming (_∼[_]_ to _List-∼[_]_)
private
  module BagMonoid {A : Set} =
    CommutativeMonoid (Eq.commutativeMonoid Any.Membership-≡.bag A)
  open module ListMonad = RawMonad {f = zero} List.monad
    using () renaming (_⊛_ to _⊛′_; _>>=_ to _>>=′_)

open import TotalParserCombinators.Derivative using (D)
open import TotalParserCombinators.Congruence
  hiding (fail)
import TotalParserCombinators.Laws.AdditiveMonoid as AdditiveMonoid
open import TotalParserCombinators.Laws.Derivative
open import TotalParserCombinators.Lib
open import TotalParserCombinators.Parser

-- return⋆ preserves equality.

cong : ∀ {k Tok R} {xs₁ xs₂ : List R} →
       xs₁ List-∼[ k ] xs₂ → return⋆ {Tok = Tok} xs₁ ∼[ k ]P return⋆ xs₂
cong {xs₁ = xs₁} {xs₂} xs₁≈xs₂ = xs₁≈xs₂ ∷ λ t → ♯ (
  D t (return⋆ xs₁)  ≅⟨ D-return⋆ xs₁ ⟩
  fail               ≅⟨ sym $ D-return⋆ xs₂ ⟩
  D t (return⋆ xs₂)  ∎)

-- return⋆ is homomorphic with respect to _++_/_∣_.

distrib-∣ :
  ∀ {Tok R} (xs₁ xs₂ : List R) →
  return⋆ {Tok = Tok} (xs₁ ++ xs₂) ≅P return⋆ xs₁ ∣ return⋆ xs₂
distrib-∣ xs₁ xs₂ =
  BagMonoid.refl ∷ λ t → ♯ (
    D t (return⋆ (xs₁ ++ xs₂))             ≅⟨ D-return⋆ (xs₁ ++ xs₂) ⟩
    fail                                   ≅⟨ sym $ AdditiveMonoid.left-identity fail ⟩
    fail ∣ fail                            ≅⟨ sym $ D-return⋆ xs₁ ∣ D-return⋆ xs₂ ⟩
    D t (return⋆ xs₁) ∣ D t (return⋆ xs₂)  ∎)

-- return⋆ is homomorphic with respect to _⊛′_/_⊛_.

distrib-⊛ :
  ∀ {Tok R₁ R₂} (fs : List (R₁ → R₂)) xs →
  return⋆ {Tok = Tok} (fs ⊛′ xs) ≅P return⋆ fs ⊛ return⋆ xs
distrib-⊛ fs xs =
  BagMonoid.refl ∷ λ t → ♯ (
    D t (return⋆ (fs ⊛′ xs))         ≅⟨ D-return⋆ (fs ⊛′ xs) ⟩

    fail                             ≅⟨ sym $ AdditiveMonoid.left-identity fail ⟩

    fail ∣ fail                      ≅⟨ sym $ left-zero-⊛ (return⋆ xs) ∣
                                              right-zero-⊛ (return⋆ fs) ⟩
    fail ⊛ return⋆ xs ∣
    return⋆ fs ⊛ fail                ≅⟨ sym $ [ ○ - ○ - ○ - ○ ] D-return⋆ fs ⊛ (return⋆ xs ∎) ∣
                                              [ ○ - ○ - ○ - ○ ] return⋆ fs ∎ ⊛ D-return⋆ xs ⟩
    D t (return⋆ fs) ⊛ return⋆ xs ∣
    return⋆ fs ⊛ D t (return⋆ xs)    ≅⟨ sym $ D-⊛ (return⋆ fs) (return⋆ xs) ⟩

    D t (return⋆ fs ⊛ return⋆ xs)    ∎)

-- return⋆ is homomorphic with respect to _>>=′_/_>>=_.

distrib->>= :
  ∀ {Tok R₁ R₂} xs (f : R₁ → List R₂) →
  return⋆ {Tok = Tok} (xs >>=′ f) ≅P return⋆ xs >>= (return⋆ ∘ f)
distrib->>= xs f =
  BagMonoid.refl ∷ λ t → ♯ (
    D t (return⋆ (xs >>=′ f))                   ≅⟨ D-return⋆ (xs >>=′ f) ⟩

    fail                                        ≅⟨ sym $ AdditiveMonoid.left-identity fail ⟩

    fail ∣ fail                                 ≅⟨ sym $ left-zero->>=  (return⋆ ∘ f) ∣
                                                         right-zero->>= (return⋆ xs) ⟩
    fail >>= (return⋆ ∘ f) ∣
    return⋆ xs >>= (λ _ → fail)                 ≅⟨ sym $ [ ○ - ○ - ○ - ○ ] D-return⋆ xs >>= (λ x → return⋆ (f x) ∎) ∣
                                                         [ ○ - ○ - ○ - ○ ] return⋆ xs ∎ >>= (λ x → D-return⋆ (f x)) ⟩
    D t (return⋆ xs) >>= (return⋆ ∘ f) ∣
    return⋆ xs >>= (λ x → D t (return⋆ (f x)))  ≅⟨ sym $ D->>= (return⋆ xs) (return⋆ ∘ f) ⟩

    D t (return⋆ xs >>= (return⋆ ∘ f))          ∎)
