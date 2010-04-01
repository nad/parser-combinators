------------------------------------------------------------------------
-- Laws related to ∂
------------------------------------------------------------------------

module TotalParserCombinators.Laws.Derivative where

open import Algebra
open import Coinduction
open import Data.List
import Data.List.Any.BagAndSetEquality as BSEq
import Data.List.Properties as ListProp
open import Function
import Relation.Binary.PropositionalEquality as P

private
  module BagMonoid {A : Set} =
    CommutativeMonoid (BSEq.commutativeMonoid _ A)

import TotalParserCombinators.Applicative as ⊛
open import TotalParserCombinators.BreadthFirst
open import TotalParserCombinators.BreadthFirst.Derivative
open import TotalParserCombinators.Coinduction
open import TotalParserCombinators.Congruence as Eq
import TotalParserCombinators.Laws.AdditiveMonoid as AdditiveMonoid
open import TotalParserCombinators.Lib
open import TotalParserCombinators.Parser
open import TotalParserCombinators.Semantics

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
        (p₁ : ∞? (Parser Tok (R₁ → R₂) fs) xs)
        (p₂ : ∞? (Parser Tok  R₁       xs) fs) {t} →
        ∂ (p₁ ⊛ p₂) t ≅P
        ∂ (♭? p₁) t ⊙ ♭? p₂ ∣ return⋆ fs ⊙ ∂ (♭? p₂) t
  ∂-⊛ ⟨ p₁ ⟩ ⟪ p₂ ⟫ {t} =
    ∂ p₁ t ⊙ ♭ p₂                      ≅⟨ sym $ AdditiveMonoid.right-identity (∂ p₁ t ⊙ ♭ p₂) ⟩
    ∂ p₁ t ⊙ ♭ p₂ ∣ fail               ≅⟨ (∂ p₁ t ⊙ ♭ p₂ ∎) ∣ sym (left-zero-⊙ (∂ (♭ p₂) t)) ⟩
    ∂ p₁ t ⊙ ♭ p₂ ∣ fail ⊙ ∂ (♭ p₂) t  ∎
  ∂-⊛ ⟪ p₁ ⟫ ⟪ p₂ ⟫ {t} =
    ∂ (⟪ p₁ ⟫ ⊛ ⟪ p₂ ⟫) t                  ≅⟨ (∂ (♭ p₁) t ∎) ⊛ (♭? {xs = ∂-initial (♭ p₁) t} (♯? (♭ p₂)) ∎) ⟩
    ∂ (♭ p₁) t ⊙ ♭ p₂                      ≅⟨ sym $ AdditiveMonoid.right-identity (∂ (♭ p₁) t ⊙ ♭ p₂) ⟩
    ∂ (♭ p₁) t ⊙ ♭ p₂ ∣ fail               ≅⟨ (∂ (♭ p₁) t ⊙ ♭ p₂ ∎) ∣ sym (left-zero-⊙ (∂ (♭ p₂) t)) ⟩
    ∂ (♭ p₁) t ⊙ ♭ p₂ ∣ fail ⊙ ∂ (♭ p₂) t  ∎
  ∂-⊛ ⟨ p₁ ⟩ ⟨ p₂ ⟩ {t} =
    ∂ (⟨ p₁ ⟩ ⊛ ⟨ p₂ ⟩) t ∎
  ∂-⊛ ⟪ p₁ ⟫ (⟨_⟩ {f} {fs} p₂) {t} =
    ∂ (⟪ p₁ ⟫ ⊛ ⟨ p₂ ⟩) t                        ≅⟨ (∂ (♭ p₁) t ∎) ⊛ (♭? {xs = ∂-initial (♭ p₁) t} (♯? p₂) ∎) ∣
                                                    (♯? (return⋆ (f ∷ fs)) ⊛ ⟨ ∂ p₂ t ⟩ ∎) ⟩
    ∂ (♭ p₁) t ⊙ p₂ ∣ return⋆ (f ∷ fs) ⊙ ∂ p₂ t  ∎

  -- Unfolding lemma for ∂ applied to _⊙_.

  ∂-⊙ : ∀ {Tok R₁ R₂ fs xs}
          (p₁ : Parser Tok (R₁ → R₂) fs)
          (p₂ : Parser Tok  R₁       xs) {t} →
        ∂ (p₁ ⊙ p₂) t ≅P ∂ p₁ t ⊙ p₂ ∣ return⋆ fs ⊙ ∂ p₂ t
  ∂-⊙ {fs = fs} {xs} p₁ p₂ {t} =
    ∂ (p₁ ⊙ p₂) t                                        ≅⟨ ∂-⊛ (♯? p₁) (♯? p₂) ⟩

    ∂ (♭? {xs = xs} (♯? p₁)) t ⊙ ♭? {xs = fs} (♯? p₂) ∣
    return⋆ fs ⊙ ∂ (♭? {xs = fs} (♯? p₂)) t              ≅⟨ Eq.complete (∂-cong (♭♯.correct xs {p₁})) ⊙′
                                                              Eq.complete (♭♯.correct fs {p₂}) ∣
                                                            (return⋆ fs ∎) ⊙′
                                                              Eq.complete (∂-cong (♭♯.correct fs {p₂}) {t}) ⟩
    ∂ p₁ t ⊙ p₂ ∣ return⋆ fs ⊙ ∂ p₂ t                     ∎

  -- fail is a left zero of ⊙.

  left-zero-⊙ : ∀ {Tok R₁ R₂ xs} (p : Parser Tok R₁ xs) →
                fail ⊙ p ≅P fail {R = R₂}
  left-zero-⊙ {xs = xs} p =
    BagMonoid.reflexive (⊛.left-zero xs) ∷ λ t → ♯ (
      ∂ (fail ⊙ p) t           ≅⟨ ∂-⊙ fail p ⟩
      fail ⊙ p ∣ fail ⊙ ∂ p t  ≅⟨ left-zero-⊙ p ∣ left-zero-⊙ (∂ p t) ⟩
      fail ∣ fail              ≅⟨ AdditiveMonoid.right-identity fail ⟩
      fail                     ∎)

right-zero-⊙ : ∀ {Tok R₁ R₂ fs} (p : Parser Tok (R₁ → R₂) fs) →
               p ⊙ fail ≅P fail
right-zero-⊙ {fs = fs} p = BagMonoid.refl ∷ λ t → ♯ (
  ∂ (p ⊙ fail) t                    ≅⟨ ∂-⊙ p fail ⟩
  ∂ p t ⊙ fail ∣ return⋆ fs ⊙ fail  ≅⟨ right-zero-⊙ (∂ p t) ∣ right-zero-⊙ (return⋆ fs) ⟩
  fail ∣ fail                       ≅⟨ AdditiveMonoid.left-identity fail ⟩
  fail                              ∎)

-- Some simplified instances of ∂-⊙.

∂-return-⊙ : ∀ {Tok R₁ R₂ xs}
             (f : R₁ → R₂) (p : Parser Tok R₁ xs) {t} →
             ∂ (return f ⊙ p) t ≅P return f ⊙ ∂ p t
∂-return-⊙ f p {t} =
  ∂ (return f ⊙ p) t                    ≅⟨ ∂-⊙ (return f) p ⟩
  fail ⊙ p ∣ (return f ∣ fail) ⊙ ∂ p t  ≅⟨ left-zero-⊙ p ∣
                                           (AdditiveMonoid.right-identity (return f)) ⊙′ (∂ p t ∎) ⟩
  fail ∣ return f ⊙ ∂ p t               ≅⟨ AdditiveMonoid.left-identity (return f ⊙ ∂ p t) ⟩
  return f ⊙ ∂ p t                      ∎

∂-⊙-return : ∀ {Tok R₁ R₂ fs}
             (p : Parser Tok (R₁ → R₂) fs) (x : R₁) {t} →
             ∂ (p ⊙ return x) t ≅P ∂ p t ⊙ return x
∂-⊙-return {fs = fs} p x {t} =
  ∂ (p ⊙ return x) t                    ≅⟨ ∂-⊙ p (return x) ⟩
  ∂ p t ⊙ return x ∣ return⋆ fs ⊙ fail  ≅⟨ (∂ p t ⊙ return x ∎) ∣ right-zero-⊙ (return⋆ fs) ⟩
  ∂ p t ⊙ return x ∣ fail               ≅⟨ AdditiveMonoid.right-identity (∂ p t ⊙ return x) ⟩
  ∂ p t ⊙ return x                      ∎

private

  -- ∂! is closely related to ∂.

  ∂!≅∂ : ∀ {Tok R₁ R₂ xs y} {ys : List R₁}
         (p : ∞? (Parser Tok R₂ xs) (y ∷ ys)) {t} →
         ∂! p t ≅P ∂ (♭? p) t
  ∂!≅∂ ⟨ p ⟩ {t} = ∂ p t ∎

mutual

  -- Unfolding lemma for ∂ applied to _>>=_.

  ∂->>= : ∀ {Tok R₁ R₂ xs} {f : R₁ → List R₂}
          (p₁ : Parser Tok R₁ xs)
          (p₂ : (x : R₁) → ∞? (Parser Tok R₂ (f x)) xs) {t} →
          ∂ (p₁ >>= p₂) t ≅P
          ∂ p₁ t ≫= (♭? ∘ p₂) ∣ return⋆ xs ≫= (λ x → ∂ (♭? (p₂ x)) t)
  ∂->>= {xs = []} p₁ p₂ {t} =
    ∂ p₁ t ≫= (♭? ∘ p₂)                                    ≅⟨ sym $ AdditiveMonoid.right-identity (∂ p₁ t ≫= (♭? ∘ p₂)) ⟩
    ∂ p₁ t ≫= (♭? ∘ p₂) ∣ fail                             ≅⟨ (∂ p₁ t ≫= (♭? ∘ p₂) ∎) ∣
                                                              sym (left-zero-≫= (λ x → ∂ (♭? (p₂ x)) t)) ⟩
    ∂ p₁ t ≫= (♭? ∘ p₂) ∣ fail ≫= (λ x → ∂ (♭? (p₂ x)) t)  ∎
  ∂->>= {xs = x ∷ xs} p₁ p₂ {t} =
    ∂ p₁ t ≫= (♭? ∘ p₂) ∣ return⋆ (x ∷ xs) >>= (λ x → ⟨ ∂! (p₂ x) t ⟩)  ≅⟨ (∂ p₁ t ≫= (♭? ∘ p₂) ∎) ∣
                                                                           (return⋆ (x ∷ xs) ∎) >>= (λ x → ∂!≅∂ (p₂ x)) ⟩
    ∂ p₁ t ≫= (♭? ∘ p₂) ∣ return⋆ (x ∷ xs)  ≫= (λ x → ∂ (♭? (p₂ x)) t)  ∎

  -- Unfolding lemma for ∂ applied to _≫=_.

  ∂-≫= : ∀ {Tok R₁ R₂ xs} {f : R₁ → List R₂}
         (p₁ : Parser Tok R₁ xs)
         (p₂ : (x : R₁) → Parser Tok R₂ (f x)) {t} →
         ∂ (p₁ ≫= p₂) t ≅P
         ∂ p₁ t ≫= p₂ ∣ return⋆ xs ≫= (λ x → ∂ (p₂ x) t)
  ∂-≫= {xs = xs} p₁ p₂ {t} =
    ∂ (p₁ ≫= p₂) t                                        ≅⟨ ∂->>= p₁ (♯? ∘ p₂) ⟩

    ∂ p₁ t ≫= (♭? ∘ ♯? {xs = xs} ∘ p₂) ∣
    return⋆ xs ≫= (λ x → ∂ (♭? (♯? {xs = xs} (p₂ x))) t)  ≅⟨ (∂ p₁ t ∎) ≫=′ (λ _ → Eq.complete (♭♯.correct xs)) ∣
                                                             (return⋆ xs ∎) ≫=′ (λ _ → Eq.complete (∂-cong (♭♯.correct xs))) ⟩
    ∂ p₁ t ≫= p₂ ∣ return⋆ xs ≫= (λ x → ∂ (p₂ x) t)       ∎

  -- fail is a left zero of _≫=_.

  left-zero-≫= : ∀ {Tok R₁ R₂} {f : R₁ → List R₂}
                 (p : (x : R₁) → Parser Tok R₂ (f x)) →
                 fail ≫= p ≅P fail
  left-zero-≫= {f = f} p =
    BagMonoid.reflexive (ListProp.Monad.left-zero f) ∷ λ t → ♯ (
      ∂ (fail ≫= p) t                        ≅⟨ ∂-≫= fail p {t} ⟩
      fail ≫= p ∣ fail ≫= (λ x → ∂ (p x) t)  ≅⟨ left-zero-≫= p ∣ left-zero-≫= (λ x → ∂ (p x) t) ⟩
      fail ∣ fail                            ≅⟨ AdditiveMonoid.right-identity fail ⟩
      fail                                   ∎)

-- fail is a right zero of _≫=_.

right-zero-≫= : ∀ {Tok R₁ R₂} {xs : List R₁}
                (p : Parser Tok R₁ xs) →
                p ≫= (λ _ → fail) ≅P fail {Tok = Tok} {R = R₂}
right-zero-≫= {xs = xs} p =
  BagMonoid.reflexive (ListProp.Monad.right-zero xs) ∷ λ t → ♯ (
    ∂ (p ≫= λ _ → fail) t                               ≅⟨ ∂-≫= p (λ _ → fail) ⟩
    ∂ p t ≫= (λ _ → fail) ∣ return⋆ xs ≫= (λ _ → fail)  ≅⟨ right-zero-≫= (∂ p t) ∣ right-zero-≫= (return⋆ xs) ⟩
    fail ∣ fail                                         ≅⟨ AdditiveMonoid.left-identity fail ⟩
    fail                                                ∎)

private

  -- Preliminary unfolding lemma for ∂ applied to _>>=!_.

  ∂->>=!′ : ∀ {Tok R₁ R₂ xs}
            (p₁ : ∞ (Parser Tok R₁ xs))
            (p₂ : (x : R₁) → ∞? (Parser Tok R₂ []) xs) {t} →
            ∂ (p₁ >>=! p₂) t ≅P
            ♯ (∂ (♭ p₁) t) >>=! (λ x → ♯? (♭? (p₂ x))) ∣
              return⋆ xs ≫= (λ x → ∂ (♭? (p₂ x)) t)
  ∂->>=!′ {xs = []} p₁ p₂ {t} =
    ∂ (p₁ >>=! p₂) t                     ≅⟨ (_ ∎) >>=! (λ _ → _ ∎) ⟩

    _ >>=! (λ x → ♯? (♭? (p₂ x)))        ≅⟨ sym $ AdditiveMonoid.right-identity
                                                    (_ >>=! (λ x → ♯? (♭? (p₂ x)))) ⟩
    _ >>=! (λ x → ♯? (♭? (p₂ x))) ∣ fail ≅⟨ (_ >>=! (λ x → ♯? (♭? (p₂ x))) ∎) ∣
                                            sym (left-zero-≫= (λ x → ∂ (♭? (p₂ x)) t)) ⟩
    _ >>=! (λ x → ♯? (♭? (p₂ x))) ∣
    fail ≫= (λ x → ∂ (♭? (p₂ x)) t)      ∎
  ∂->>=!′ {xs = x ∷ xs} p₁ p₂ {t} =
    ∂ (p₁ >>=! p₂) t                              ≅⟨ (_ ∎) >>=! (λ _ → _ ∎) ∣ (_ ∎) ⟩

    _ >>=! (λ x → ♯? (♭? (p₂ x))) ∣
    return⋆ (x ∷ xs) >>= (λ x → ⟨ ∂! (p₂ x) t ⟩)  ≅⟨ (_ >>=! (λ x → ♯? (♭? (p₂ x))) ∎) ∣
                                                     (return⋆ (x ∷ xs) ∎) >>= (λ x → ∂!≅∂ (p₂ x)) ⟩
    _ >>=! (λ x → ♯? (♭? (p₂ x))) ∣
    return⋆ (x ∷ xs) ≫= (λ x → ∂ (♭? (p₂ x)) t)   ∎

-- _>>=!_ and _>>=_ are equivalent (where their domains overlap).

>>=!≅>>= : ∀ {Tok R₁ R₂ xs}
           (p₁ : ∞ (Parser Tok R₁ xs))
           (p₂ : (x : R₁) → ∞? (Parser Tok R₂ []) xs) →
           p₁ >>=! p₂ ≅P ♭ p₁ >>= p₂
>>=!≅>>= {xs = xs} p₁ p₂ =
  BagMonoid.reflexive (P.sym $ ListProp.Monad.right-zero xs) ∷ λ t → ♯ (
    ∂ (p₁ >>=! p₂) t                                                       ≅⟨ ∂->>=!′ p₁ p₂ ⟩
    _ >>=! (λ x → ♯? (♭? (p₂ x))) ∣ return⋆ xs ≫= (λ x → ∂ (♭? (p₂ x)) t)  ≅⟨ >>=!≅>>= _ _ ∣ (_ ∎) ⟩
    ∂ (♭ p₁) t ≫= (♭? ∘ p₂) ∣ return⋆ xs ≫= (λ x → ∂ (♭? (p₂ x)) t)        ≅⟨ sym $ ∂->>= (♭ p₁) p₂ ⟩
    ∂ (♭ p₁ >>= p₂) t                                                      ∎)

-- Unfolding lemma for ∂ applied to _>>=!_.

∂->>=! : ∀ {Tok R₁ R₂ xs}
         (p₁ : ∞ (Parser Tok R₁ xs))
         (p₂ : (x : R₁) → ∞? (Parser Tok R₂ []) xs) {t} →
         ∂ (p₁ >>=! p₂) t ≅P
         ∂ (♭ p₁) t ≫= (♭? ∘ p₂) ∣ return⋆ xs ≫= (λ x → ∂ (♭? (p₂ x)) t)
∂->>=! {xs = xs} p₁ p₂ {t} =
  ∂ (p₁ >>=! p₂) t                                                       ≅⟨ ∂->>=!′ p₁ p₂ ⟩
  _ >>=! (λ x → ♯? (♭? (p₂ x))) ∣ return⋆ xs ≫= (λ x → ∂ (♭? (p₂ x)) t)  ≅⟨ >>=!≅>>= _ _ ∣ (_ ∎) ⟩
  ∂ (♭ p₁) t ≫= (♭? ∘ p₂) ∣ return⋆ xs ≫= (λ x → ∂ (♭? (p₂ x)) t)        ∎
