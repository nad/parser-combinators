------------------------------------------------------------------------
-- Laws related to ∂
------------------------------------------------------------------------

module TotalParserCombinators.Laws.Derivative where

open import Algebra
open import Coinduction
open import Data.List
import Data.List.Any.BagAndSetEquality as BSEq
import Data.List.Properties as ListProp
open import Data.Maybe using (Maybe); open Data.Maybe.Maybe
open import Function using (_∘_; _$_)

private
  module BagMonoid {A : Set} =
    CommutativeMonoid (BSEq.commutativeMonoid _ A)

open import TotalParserCombinators.BreadthFirst
open import TotalParserCombinators.Congruence as Eq
  hiding (return; fail)
import TotalParserCombinators.Laws.AdditiveMonoid as AdditiveMonoid
open import TotalParserCombinators.Lib
open import TotalParserCombinators.Parser

-- Unfolding lemma for ∂ applied to return⋆.

∂-return⋆ : ∀ {Tok R} (xs : List R) {t} →
            ∂ (return⋆ xs) t ≅P fail {Tok = Tok}
∂-return⋆ []           = fail ∎
∂-return⋆ (x ∷ xs) {t} =
  fail ∣ ∂ (return⋆ xs) t  ≅⟨ AdditiveMonoid.left-identity (∂ (return⋆ xs) t) ⟩
  ∂ (return⋆ xs) t         ≅⟨ ∂-return⋆ xs ⟩
  fail                     ∎

mutual

  -- Unfolding lemma for ∂ applied to _⊛_.

  ∂-⊛ : ∀ {Tok R₁ R₂ fs xs}
        (p₁ : ∞⟨ xs ⟩Parser Tok (R₁ → R₂) (flatten fs))
        (p₂ : ∞⟨ fs ⟩Parser Tok  R₁       (flatten xs)) {t} →
        ∂ (p₁ ⊛ p₂) t ≅P
        ∂ (♭? p₁) t ⊛ ♭? p₂ ∣ return⋆ (flatten fs) ⊛ ∂ (♭? p₂) t
  ∂-⊛ {fs = nothing} {xs = just _} p₁ p₂ {t} =
    ∂ p₁ t ⊛ ♭ p₂                      ≅⟨ sym $ AdditiveMonoid.right-identity (∂ p₁ t ⊛ ♭ p₂) ⟩
    ∂ p₁ t ⊛ ♭ p₂ ∣ fail               ≅⟨ (∂ p₁ t ⊛ ♭ p₂ ∎) ∣ sym (left-zero-⊛ (∂ (♭ p₂) t)) ⟩
    ∂ p₁ t ⊛ ♭ p₂ ∣ fail ⊛ ∂ (♭ p₂) t  ∎
  ∂-⊛ {fs = nothing} {xs = nothing} p₁ p₂ {t} =
    ∂ (p₁ ⊛ p₂) t                          ≅⟨ [ ◌ - ○ - ○ - ○ ] ∂ (♭ p₁) t ∎ ⊛ (♭ p₂ ∎) ⟩
    ∂ (♭ p₁) t ⊛ ♭ p₂                      ≅⟨ sym $ AdditiveMonoid.right-identity (∂ (♭ p₁) t ⊛ ♭ p₂) ⟩
    ∂ (♭ p₁) t ⊛ ♭ p₂ ∣ fail               ≅⟨ (∂ (♭ p₁) t ⊛ ♭ p₂ ∎) ∣ sym (left-zero-⊛ (∂ (♭ p₂) t)) ⟩
    ∂ (♭ p₁) t ⊛ ♭ p₂ ∣ fail ⊛ ∂ (♭ p₂) t  ∎
  ∂-⊛ {fs = just _} {xs = just _} p₁ p₂ {t} =
    ∂ (p₁ ⊛ p₂) t ∎
  ∂-⊛ {fs = just fs} {xs = nothing} p₁ p₂ {t} =
    ∂ (p₁ ⊛ p₂) t                          ≅⟨ [ ◌ - ○ - ○ - ○ ] ∂ (♭ p₁) t ∎ ⊛ (p₂ ∎) ∣
                                              (return⋆ fs ⊛ ∂ p₂ t ∎) ⟩
    ∂ (♭ p₁) t ⊛ p₂ ∣ return⋆ fs ⊛ ∂ p₂ t  ∎

  -- fail is a left zero of ⊛.

  left-zero-⊛ : ∀ {Tok R₁ R₂ xs} (p : Parser Tok R₁ xs) →
                fail ⊛ p ≅P fail {R = R₂}
  left-zero-⊛ {xs = xs} p =
    BagMonoid.reflexive (ListProp.Applicative.left-zero xs) ∷ λ t → ♯ (
      ∂ (fail ⊛ p) t           ≅⟨ ∂-⊛ fail p ⟩
      fail ⊛ p ∣ fail ⊛ ∂ p t  ≅⟨ left-zero-⊛ p ∣ left-zero-⊛ (∂ p t) ⟩
      fail ∣ fail              ≅⟨ AdditiveMonoid.right-identity fail ⟩
      fail                     ∎)

-- fail is a right zero of ⊛.

right-zero-⊛ : ∀ {Tok R₁ R₂ fs} (p : Parser Tok (R₁ → R₂) fs) →
               p ⊛ fail ≅P fail
right-zero-⊛ {fs = fs} p =
  BagMonoid.reflexive (ListProp.Applicative.right-zero fs) ∷ λ t → ♯ (
    ∂ (p ⊛ fail) t                    ≅⟨ ∂-⊛ p fail ⟩
    ∂ p t ⊛ fail ∣ return⋆ fs ⊛ fail  ≅⟨ right-zero-⊛ (∂ p t) ∣ right-zero-⊛ (return⋆ fs) ⟩
    fail ∣ fail                       ≅⟨ AdditiveMonoid.left-identity fail ⟩
    fail                              ∎)

-- A simplified instance of ∂-⊛.

∂-return-⊛ : ∀ {Tok R₁ R₂ xs}
             (f : R₁ → R₂) (p : Parser Tok R₁ xs) {t} →
             ∂ (return f ⊛ p) t ≅P return f ⊛ ∂ p t
∂-return-⊛ f p {t} =
  ∂ (return f ⊛ p) t                ≅⟨ ∂-⊛ (return f) p ⟩
  fail ⊛ p ∣ return⋆ [ f ] ⊛ ∂ p t  ≅⟨ left-zero-⊛ p ∣
                                       [ ○ - ○ - ○ - ○ ] AdditiveMonoid.right-identity (return f) ⊛ (∂ p t ∎) ⟩
  fail ∣ return f ⊛ ∂ p t           ≅⟨ AdditiveMonoid.left-identity (return f ⊛ ∂ p t) ⟩
  return f ⊛ ∂ p t                  ∎

mutual

  -- Unfolding lemma for ∂ applied to _>>=_.

  ∂->>= : ∀ {Tok R₁ R₂ xs} {f : Maybe (R₁ → List R₂)}
          (p₁ : ∞⟨ f ⟩Parser Tok R₁ (flatten xs))
          (p₂ : (x : R₁) → ∞⟨ xs ⟩Parser Tok R₂ (app f x)) {t} →
          ∂ (p₁ >>= p₂) t ≅P
          ∂ (♭? p₁) t >>= (♭? ∘ p₂) ∣
          return⋆ (flatten xs) >>= (λ x → ∂ (♭? (p₂ x)) t)
  ∂->>= {xs = nothing} {f = just _} p₁ p₂ {t} =
    ∂ p₁ t >>= (♭ ∘ p₂)                                    ≅⟨ sym $ AdditiveMonoid.right-identity (∂ p₁ t >>= (♭ ∘ p₂)) ⟩
    ∂ p₁ t >>= (♭ ∘ p₂) ∣ fail                             ≅⟨ (∂ p₁ t >>= (♭ ∘ p₂) ∎) ∣
                                                              sym (left-zero->>= (λ x → ∂ (♭ (p₂ x)) t)) ⟩
    ∂ p₁ t >>= (♭ ∘ p₂) ∣ fail >>= (λ x → ∂ (♭ (p₂ x)) t)  ∎
  ∂->>= {xs = just xs} {f = just _} p₁ p₂ {t} =
    ∂ p₁ t >>= p₂ ∣ return⋆ xs >>= (λ x → ∂ (p₂ x) t)  ∎
  ∂->>= {xs = nothing} {f = nothing} p₁ p₂ {t} =
    ∂ (p₁ >>= p₂) t                                            ≅⟨ [ ◌ - ○ - ○ - ○ ] _ ∎ >>= (λ _ → _ ∎) ⟩
    ∂ (♭ p₁) t >>= (♭ ∘ p₂)                                    ≅⟨ sym $ AdditiveMonoid.right-identity (∂ (♭ p₁) t >>= (♭ ∘ p₂)) ⟩
    ∂ (♭ p₁) t >>= (♭ ∘ p₂) ∣ fail                             ≅⟨ (∂ (♭ p₁) t >>= (♭ ∘ p₂) ∎) ∣
                                                                  sym (left-zero->>= (λ x → ∂ (♭ (p₂ x)) t)) ⟩
    ∂ (♭ p₁) t >>= (♭ ∘ p₂) ∣ fail >>= (λ x → ∂ (♭ (p₂ x)) t)  ∎
  ∂->>= {xs = just xs} {f = nothing} p₁ p₂ {t} =
    ∂ (p₁ >>= p₂) t                                        ≅⟨ [ ◌ - ○ - ○ - ○ ] _ ∎ >>= (λ _ → _ ∎) ∣ (_ ∎) ⟩
    ∂ (♭ p₁) t >>= p₂ ∣ return⋆ xs >>= (λ x → ∂ (p₂ x) t)  ∎

  -- fail is a left zero of _>>=_.

  left-zero->>= : ∀ {Tok R₁ R₂} {f : R₁ → List R₂}
                 (p : (x : R₁) → Parser Tok R₂ (f x)) →
                 fail >>= p ≅P fail
  left-zero->>= {f = f} p =
    BagMonoid.reflexive (ListProp.Monad.left-zero f) ∷ λ t → ♯ (
      ∂ (fail >>= p) t                         ≅⟨ ∂->>= fail p {t} ⟩
      fail >>= p ∣ fail >>= (λ x → ∂ (p x) t)  ≅⟨ left-zero->>= p ∣ left-zero->>= (λ x → ∂ (p x) t) ⟩
      fail ∣ fail                              ≅⟨ AdditiveMonoid.right-identity fail ⟩
      fail                                     ∎)

-- fail is a right zero of _>>=_.

right-zero->>= : ∀ {Tok R₁ R₂} {xs : List R₁}
                (p : Parser Tok R₁ xs) →
                p >>= (λ _ → fail) ≅P fail {Tok = Tok} {R = R₂}
right-zero->>= {xs = xs} p =
  BagMonoid.reflexive (ListProp.Monad.right-zero xs) ∷ λ t → ♯ (
    ∂ (p >>= λ _ → fail) t                                ≅⟨ ∂->>= p (λ _ → fail) ⟩
    ∂ p t >>= (λ _ → fail) ∣ return⋆ xs >>= (λ _ → fail)  ≅⟨ right-zero->>= (∂ p t) ∣ right-zero->>= (return⋆ xs) ⟩
    fail ∣ fail                                           ≅⟨ AdditiveMonoid.left-identity fail ⟩
    fail                                                  ∎)
