------------------------------------------------------------------------
-- Laws related to D
------------------------------------------------------------------------

module TotalParserCombinators.Laws.Derivative where

open import Algebra
open import Coinduction
open import Data.List
import Data.List.Any.BagAndSetEquality as BSEq
import Data.List.Categorical as List
open import Data.Maybe using (Maybe); open Data.Maybe.Maybe
open import Function using (_∘_; _$_)

private
  module BagMonoid {k} {A : Set} =
    CommutativeMonoid (BSEq.commutativeMonoid k A)

open import TotalParserCombinators.Derivative
open import TotalParserCombinators.Congruence as Eq
  hiding (return; fail)
import TotalParserCombinators.Laws.AdditiveMonoid as AdditiveMonoid
open import TotalParserCombinators.Lib
open import TotalParserCombinators.Parser

-- Unfolding lemma for D applied to return⋆.

D-return⋆ : ∀ {Tok R t} (xs : List R) →
            D t (return⋆ xs) ≅P fail {Tok = Tok}
D-return⋆         []       = fail ∎
D-return⋆ {t = t} (x ∷ xs) =
  fail ∣ D t (return⋆ xs)  ≅⟨ AdditiveMonoid.left-identity (D t (return⋆ xs)) ⟩
  D t (return⋆ xs)         ≅⟨ D-return⋆ xs ⟩
  fail                     ∎

mutual

  -- Unfolding lemma for D applied to _⊛_.

  D-⊛ : ∀ {Tok R₁ R₂ fs xs t}
        (p₁ : ∞⟨ xs ⟩Parser Tok (R₁ → R₂) (flatten fs))
        (p₂ : ∞⟨ fs ⟩Parser Tok  R₁       (flatten xs)) →
        D t (p₁ ⊛ p₂) ≅P
        D t (♭? p₁) ⊛ ♭? p₂ ∣ return⋆ (flatten fs) ⊛ D t (♭? p₂)
  D-⊛ {fs = nothing} {xs = just _} {t = t} p₁ p₂ =
    D t p₁ ⊛ ♭ p₂                      ≅⟨ sym $ AdditiveMonoid.right-identity (D t p₁ ⊛ ♭ p₂) ⟩
    D t p₁ ⊛ ♭ p₂ ∣ fail               ≅⟨ (D t p₁ ⊛ ♭ p₂ ∎) ∣ sym (left-zero-⊛ (D t (♭ p₂))) ⟩
    D t p₁ ⊛ ♭ p₂ ∣ fail ⊛ D t (♭ p₂)  ∎
  D-⊛ {fs = nothing} {xs = nothing} {t = t} p₁ p₂ =
    D t (p₁ ⊛ p₂)                          ≅⟨ [ ◌ - ○ - ○ - ○ ] D t (♭ p₁) ∎ ⊛ (♭ p₂ ∎) ⟩
    D t (♭ p₁) ⊛ ♭ p₂                      ≅⟨ sym $ AdditiveMonoid.right-identity (D t (♭ p₁) ⊛ ♭ p₂) ⟩
    D t (♭ p₁) ⊛ ♭ p₂ ∣ fail               ≅⟨ (D t (♭ p₁) ⊛ ♭ p₂ ∎) ∣ sym (left-zero-⊛ (D t (♭ p₂))) ⟩
    D t (♭ p₁) ⊛ ♭ p₂ ∣ fail ⊛ D t (♭ p₂)  ∎
  D-⊛ {fs = just _} {xs = just _} {t = t} p₁ p₂ =
    D t (p₁ ⊛ p₂) ∎
  D-⊛ {fs = just fs} {xs = nothing} {t = t} p₁ p₂ =
    D t (p₁ ⊛ p₂)                          ≅⟨ [ ◌ - ○ - ○ - ○ ] D t (♭ p₁) ∎ ⊛ (p₂ ∎) ∣
                                              (return⋆ fs ⊛ D t p₂ ∎) ⟩
    D t (♭ p₁) ⊛ p₂ ∣ return⋆ fs ⊛ D t p₂  ∎

  -- fail is a left zero of ⊛.

  left-zero-⊛ : ∀ {Tok R₁ R₂ xs} (p : Parser Tok R₁ xs) →
                fail ⊛ p ≅P fail {R = R₂}
  left-zero-⊛ {xs = xs} p =
    BagMonoid.reflexive (List.Applicative.left-zero xs) ∷ λ t → ♯ (
      D t (fail ⊛ p)           ≅⟨ D-⊛ fail p ⟩
      fail ⊛ p ∣ fail ⊛ D t p  ≅⟨ left-zero-⊛ p ∣ left-zero-⊛ (D t p) ⟩
      fail ∣ fail              ≅⟨ AdditiveMonoid.right-identity fail ⟩
      fail                     ∎)

-- fail is a right zero of ⊛.

right-zero-⊛ : ∀ {Tok R₁ R₂ fs} (p : Parser Tok (R₁ → R₂) fs) →
               p ⊛ fail ≅P fail
right-zero-⊛ {fs = fs} p =
  BagMonoid.reflexive (List.Applicative.right-zero fs) ∷ λ t → ♯ (
    D t (p ⊛ fail)                    ≅⟨ D-⊛ p fail ⟩
    D t p ⊛ fail ∣ return⋆ fs ⊛ fail  ≅⟨ right-zero-⊛ (D t p) ∣ right-zero-⊛ (return⋆ fs) ⟩
    fail ∣ fail                       ≅⟨ AdditiveMonoid.left-identity fail ⟩
    fail                              ∎)

-- A simplified instance of D-⊛.

D-return-⊛ : ∀ {Tok R₁ R₂ xs t}
             (f : R₁ → R₂) (p : Parser Tok R₁ xs) →
             D t (return f ⊛ p) ≅P return f ⊛ D t p
D-return-⊛ {t = t} f p =
  D t (return f ⊛ p)                ≅⟨ D-⊛ (return f) p ⟩
  fail ⊛ p ∣ return⋆ [ f ] ⊛ D t p  ≅⟨ left-zero-⊛ p ∣
                                       [ ○ - ○ - ○ - ○ ] AdditiveMonoid.right-identity (return f) ⊛ (D t p ∎) ⟩
  fail ∣ return f ⊛ D t p           ≅⟨ AdditiveMonoid.left-identity (return f ⊛ D t p) ⟩
  return f ⊛ D t p                  ∎

mutual

  -- Unfolding lemma for D applied to _>>=_.

  D->>= : ∀ {Tok R₁ R₂ xs t} {f : Maybe (R₁ → List R₂)}
          (p₁ : ∞⟨ f ⟩Parser Tok R₁ (flatten xs))
          (p₂ : (x : R₁) → ∞⟨ xs ⟩Parser Tok R₂ (apply f x)) →
          D t (p₁ >>= p₂) ≅P
          D t (♭? p₁) >>= (♭? ∘ p₂) ∣
          return⋆ (flatten xs) >>= (λ x → D t (♭? (p₂ x)))
  D->>= {xs = nothing} {t = t} {f = just _} p₁ p₂ =
    D t p₁ >>= (♭ ∘ p₂)                                    ≅⟨ sym $ AdditiveMonoid.right-identity (D t p₁ >>= (♭ ∘ p₂)) ⟩
    D t p₁ >>= (♭ ∘ p₂) ∣ fail                             ≅⟨ (D t p₁ >>= (♭ ∘ p₂) ∎) ∣
                                                              sym (left-zero->>= (λ x → D t (♭ (p₂ x)))) ⟩
    D t p₁ >>= (♭ ∘ p₂) ∣ fail >>= (λ x → D t (♭ (p₂ x)))  ∎
  D->>= {xs = just xs} {t = t} {f = just _} p₁ p₂ =
    D t p₁ >>= p₂ ∣ return⋆ xs >>= (λ x → D t (p₂ x))  ∎
  D->>= {xs = nothing} {t = t} {f = nothing} p₁ p₂ =
    D t (p₁ >>= p₂)                                            ≅⟨ [ ◌ - ○ - ○ - ○ ] _ ∎ >>= (λ _ → _ ∎) ⟩
    D t (♭ p₁) >>= (♭ ∘ p₂)                                    ≅⟨ sym $ AdditiveMonoid.right-identity (D t (♭ p₁) >>= (♭ ∘ p₂)) ⟩
    D t (♭ p₁) >>= (♭ ∘ p₂) ∣ fail                             ≅⟨ (D t (♭ p₁) >>= (♭ ∘ p₂) ∎) ∣
                                                                  sym (left-zero->>= (λ x → D t (♭ (p₂ x)))) ⟩
    D t (♭ p₁) >>= (♭ ∘ p₂) ∣ fail >>= (λ x → D t (♭ (p₂ x)))  ∎
  D->>= {xs = just xs} {t = t} {f = nothing} p₁ p₂ =
    D t (p₁ >>= p₂)                                        ≅⟨ [ ◌ - ○ - ○ - ○ ] _ ∎ >>= (λ _ → _ ∎) ∣ (_ ∎) ⟩
    D t (♭ p₁) >>= p₂ ∣ return⋆ xs >>= (λ x → D t (p₂ x))  ∎

  -- fail is a left zero of _>>=_.

  left-zero->>= : ∀ {Tok R₁ R₂} {f : R₁ → List R₂}
                 (p : (x : R₁) → Parser Tok R₂ (f x)) →
                 fail >>= p ≅P fail
  left-zero->>= {f = f} p =
    BagMonoid.reflexive (List.MonadProperties.left-zero f) ∷ λ t → ♯ (
      D t (fail >>= p)                         ≅⟨ D->>= {t = t} fail p ⟩
      fail >>= p ∣ fail >>= (λ x → D t (p x))  ≅⟨ left-zero->>= p ∣ left-zero->>= (λ x → D t (p x)) ⟩
      fail ∣ fail                              ≅⟨ AdditiveMonoid.right-identity fail ⟩
      fail                                     ∎)

-- fail is a right zero of _>>=_.

right-zero->>= : ∀ {Tok R₁ R₂} {xs : List R₁}
                (p : Parser Tok R₁ xs) →
                p >>= (λ _ → fail) ≅P fail {Tok = Tok} {R = R₂}
right-zero->>= {xs = xs} p =
  BagMonoid.reflexive (List.MonadProperties.right-zero xs) ∷ λ t → ♯ (
    D t (p >>= λ _ → fail)                                ≅⟨ D->>= p (λ _ → fail) ⟩
    D t p >>= (λ _ → fail) ∣ return⋆ xs >>= (λ _ → fail)  ≅⟨ right-zero->>= (D t p) ∣ right-zero->>= (return⋆ xs) ⟩
    fail ∣ fail                                           ≅⟨ AdditiveMonoid.left-identity fail ⟩
    fail                                                  ∎)
