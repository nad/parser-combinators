------------------------------------------------------------------------
-- Laws related to ⋁
------------------------------------------------------------------------

module TotalParserCombinators.Laws.Or where

open import Category.Monad
open import Data.List as List
open import Function

private
  open module ListMonad = RawMonad List.monad
         using () renaming (_>>=_ to _>>=′_)

open import TotalParserCombinators.Congruence.Parser
import TotalParserCombinators.Laws.AdditiveMonoid as AdditiveMonoid
open import TotalParserCombinators.Lib
open import TotalParserCombinators.Parser

-- ⋁ distributes over _++_.

distrib-++ :
  ∀ {Tok R₁ R₂} {f : R₁ → List R₂}
  (p : (x : R₁) → Parser Tok R₂ (f x)) (xs₁ xs₂ : List R₁) →
  ⋁ p (xs₁ ++ xs₂) ≅P ⋁ p xs₁ ∣ ⋁ p xs₂
distrib-++ p [] xs₂ =
  ⋁ p xs₂         ≅⟨ sym $ AdditiveMonoid.left-identity (⋁ p xs₂) ⟩
  fail ∣ ⋁ p xs₂  ∎
distrib-++ p (x ∷ xs₁) xs₂ =
  p x ∣ ⋁ p (xs₁ ++ xs₂)     ≅⟨ (p x ∎) ∣ distrib-++ p xs₁ xs₂ ⟩
  p x ∣ (⋁ p xs₁ ∣ ⋁ p xs₂)  ≅⟨ sym $ AdditiveMonoid.associative (p x) (⋁ p xs₁) _ ⟩
  p x ∣ ⋁ p xs₁ ∣ ⋁ p xs₂    ∎

-- fail is a zero for ⋁.

zero : ∀ {Tok R₁ R₂} (xs : List R₁) →
       ⋁ (λ _ → fail) xs ≅P fail {Tok = Tok} {R = R₂}
zero []       = fail ∎
zero (x ∷ xs) =
  fail ∣ ⋁ (λ _ → fail) xs  ≅⟨ AdditiveMonoid.left-identity (⋁ (λ _ → fail) xs) ⟩
  ⋁ (λ _ → fail) xs         ≅⟨ zero xs ⟩
  fail                      ∎

-- ⋁ distributes over _∣_.

distrib-∣ :
  ∀ {Tok R₁ R₂} {f₁ f₂ : R₁ → List R₂}
  (p₁ : (x : R₁) → Parser Tok R₂ (f₁ x))
  (p₂ : (x : R₁) → Parser Tok R₂ (f₂ x)) (xs : List R₁) →
  ⋁ (λ x → p₁ x ∣ p₂ x) xs ≅P ⋁ p₁ xs ∣ ⋁ p₂ xs
distrib-∣ p₁ p₂ []       =
  fail         ≅⟨ sym $ AdditiveMonoid.left-identity fail ⟩
  fail ∣ fail  ∎
distrib-∣ p₁ p₂ (x ∷ xs) =
  (p₁ x ∣ p₂ x) ∣ ⋁ (λ x → p₁ x ∣ p₂ x) xs  ≅⟨ (p₁ x ∣ p₂ x ∎) ∣ distrib-∣ p₁ p₂ xs ⟩
  (p₁ x ∣ p₂ x) ∣ (⋁ p₁ xs ∣ ⋁ p₂ xs)       ≅⟨ AdditiveMonoid.swap (p₁ x) (p₂ x) (⋁ p₁ xs) (⋁ p₂ xs) ⟩
  (p₁ x ∣ ⋁ p₁ xs) ∣ (p₂ x ∣ ⋁ p₂ xs)       ∎

-- ⋁ is related to _>>=′_.

⋁⋁≅⋁>>= :
  ∀ {Tok R₁ R₂ R₃} {g : R₂ → List R₃}
  (p : (x : R₂) → Parser Tok R₃ (g x))
  (f : R₁ → List R₂) (xs : List R₁) →
  ⋁ (⋁ p ∘ f) xs ≅P ⋁ p (xs >>=′ f)
⋁⋁≅⋁>>= p f []       = fail ∎
⋁⋁≅⋁>>= p f (x ∷ xs) =
  ⋁ p (f x) ∣ ⋁ (⋁ p ∘ f) xs   ≅⟨ (⋁ p (f x) ∎) ∣ ⋁⋁≅⋁>>= p f xs ⟩
  ⋁ p (f x) ∣ ⋁ p (xs >>=′ f)  ≅⟨ sym $ distrib-++ p (f x) (xs >>=′ f) ⟩
  ⋁ p (f x ++ (xs >>=′ f))     ∎
