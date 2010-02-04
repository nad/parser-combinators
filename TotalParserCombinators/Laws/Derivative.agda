------------------------------------------------------------------------
-- Laws related to ∂
------------------------------------------------------------------------

module TotalParserCombinators.Laws.Derivative where

open import Algebra
open import Coinduction
open import Data.List
import Data.List.Any as Any
import Data.List.Any.BagEquality as BagEq
import Data.List.Properties as ListProp
open import Function
open import Relation.Binary
import Relation.Binary.PropositionalEquality as P

private
  module BagS {A : Set} = Setoid (Any.Membership-≡.Bag-equality {A})
  module BagMonoid {A : Set} =
    CommutativeMonoid (BagEq.commutativeMonoid A)

import TotalParserCombinators.Applicative as ⊛
open import TotalParserCombinators.BreadthFirst
open import TotalParserCombinators.BreadthFirst.Derivative
open import TotalParserCombinators.Coinduction
open import TotalParserCombinators.Congruence.Parser as Eq
import TotalParserCombinators.Laws.AdditiveMonoid as AdditiveMonoid
open import TotalParserCombinators.Lib
open import TotalParserCombinators.Parser
open import TotalParserCombinators.Semantics

-- ∂ distributes over ⋁.

∂-⋁-distrib : ∀ {Tok R₁ R₂} {f : R₁ → List R₂}
              (p : (x : R₁) → Parser Tok R₂ (f x))
              (xs : List R₁) {t} →
              ∂ (⋁ p xs) t ≅P ⋁ (λ x → ∂ (p x) t) xs
∂-⋁-distrib p []           = fail ∎
∂-⋁-distrib p (x ∷ xs) {t} =
  ∂ (p x) t ∣ ∂ (⋁ p xs) t            ≅⟨ (∂ (p x) t ∎) ∣ ∂-⋁-distrib p xs ⟩
  ∂ (p x) t ∣ ⋁ (λ x → ∂ (p x) t) xs  ∎

mutual

  -- Unfolding lemma for ∂ applied to _⊛_.

  ∂-⊛ : ∀ {Tok R₁ R₂ fs xs}
        (p₁ : ∞? (Parser Tok (R₁ → R₂) fs) xs)
        (p₂ : ∞? (Parser Tok  R₁       xs) fs) {t} →
        ∂ (p₁ ⊛ p₂) t ≅P
        ∂ (♭? p₁) t ⊙ ♭? p₂ ∣ ⋁ return fs ⊙ ∂ (♭? p₂) t
  ∂-⊛ ⟨ p₁ ⟩ ⟪ p₂ ⟫ {t} =
    ∂ p₁ t ⊙ ♭ p₂                      ≅⟨ sym $ AdditiveMonoid.right-identity (∂ p₁ t ⊙ ♭ p₂) ⟩
    ∂ p₁ t ⊙ ♭ p₂ ∣ fail               ≅⟨ (∂ p₁ t ⊙ ♭ p₂ ∎) ∣ sym (left-zero (∂ (♭ p₂) t)) ⟩
    ∂ p₁ t ⊙ ♭ p₂ ∣ fail ⊙ ∂ (♭ p₂) t  ∎
  ∂-⊛ ⟪ p₁ ⟫ ⟪ p₂ ⟫ {t} =
    ∂ (⟪ p₁ ⟫ ⊛ ⟪ p₂ ⟫) t                  ≅⟨ (∂ (♭ p₁) t ∎) ⊛ (♭? {xs = ∂-initial (♭ p₁) t} (♯? (♭ p₂)) ∎) ⟩
    ∂ (♭ p₁) t ⊙ ♭ p₂                      ≅⟨ sym $ AdditiveMonoid.right-identity (∂ (♭ p₁) t ⊙ ♭ p₂) ⟩
    ∂ (♭ p₁) t ⊙ ♭ p₂ ∣ fail               ≅⟨ (∂ (♭ p₁) t ⊙ ♭ p₂ ∎) ∣ sym (left-zero (∂ (♭ p₂) t)) ⟩
    ∂ (♭ p₁) t ⊙ ♭ p₂ ∣ fail ⊙ ∂ (♭ p₂) t  ∎
  ∂-⊛ ⟨ p₁ ⟩ ⟨ p₂ ⟩ {t} =
    ∂ (⟨ p₁ ⟩ ⊛ ⟨ p₂ ⟩) t ∎
  ∂-⊛ ⟪ p₁ ⟫ (⟨_⟩ {f} {fs} p₂) {t} =
    ∂ (⟪ p₁ ⟫ ⊛ ⟨ p₂ ⟩) t                         ≅⟨ (∂ (♭ p₁) t ∎) ⊛ (♭? {xs = ∂-initial (♭ p₁) t} (♯? p₂) ∎) ∣
                                                     (♯? (⋁ return (f ∷ fs)) ⊛ ⟨ ∂ p₂ t ⟩ ∎) ⟩
    ∂ (♭ p₁) t ⊙ p₂ ∣ ⋁ return (f ∷ fs) ⊙ ∂ p₂ t  ∎

  -- Unfolding lemma for ∂ applied to _⊙_.

  ∂-⊙ : ∀ {Tok R₁ R₂ fs xs}
          (p₁ : Parser Tok (R₁ → R₂) fs)
          (p₂ : Parser Tok  R₁       xs) {t} →
        ∂ (p₁ ⊙ p₂) t ≅P ∂ p₁ t ⊙ p₂ ∣ ⋁ return fs ⊙ ∂ p₂ t
  ∂-⊙ {fs = fs} {xs} p₁ p₂ {t} =
    ∂ (p₁ ⊙ p₂) t                                        ≅⟨ ∂-⊛ (♯? p₁) (♯? p₂) ⟩

    ∂ (♭? {xs = xs} (♯? p₁)) t ⊙ ♭? {xs = fs} (♯? p₂) ∣
    ⋁ return fs ⊙ ∂ (♭? {xs = fs} (♯? p₂)) t             ≅⟨ Eq.complete (∂-cong-≅ (♭♯.correct xs {p₁})) ⊙′
                                                              Eq.complete (♭♯.correct fs {p₂}) ∣
                                                            (⋁ return fs ∎) ⊙′
                                                              Eq.complete (∂-cong-≅ (♭♯.correct fs {p₂}) {t}) ⟩
    ∂ p₁ t ⊙ p₂ ∣ ⋁ return fs ⊙ ∂ p₂ t  ∎

  -- fail is a left zero of ⊙.

  left-zero : ∀ {Tok R₁ R₂ xs} (p : Parser Tok R₁ xs) →
              fail ⊙ p ≅P fail {R = R₂}
  left-zero {xs = xs} p =
    BagS.reflexive (⊛.left-zero xs) ∷ λ t → ♯ (
      ∂ (fail ⊙ p) t           ≅⟨ ∂-⊙ fail p ⟩
      fail ⊙ p ∣ fail ⊙ ∂ p t  ≅⟨ left-zero p ∣ left-zero (∂ p t) ⟩
      fail ∣ fail              ≅⟨ AdditiveMonoid.right-identity fail ⟩
      fail                     ∎)

right-zero : ∀ {Tok R₁ R₂ fs} (p : Parser Tok (R₁ → R₂) fs) →
             p ⊙ fail ≅P fail
right-zero {fs = fs} p = BagS.refl ∷ λ t → ♯ (
  ∂ (p ⊙ fail) t                     ≅⟨ ∂-⊙ p fail ⟩
  ∂ p t ⊙ fail ∣ ⋁ return fs ⊙ fail  ≅⟨ right-zero (∂ p t) ∣ right-zero (⋁ return fs) ⟩
  fail ∣ fail                        ≅⟨ AdditiveMonoid.left-identity fail ⟩
  fail                               ∎)

-- Some simplified instances of ∂-⊙.

∂-return-⊙ : ∀ {Tok R₁ R₂ xs}
             (f : R₁ → R₂) (p : Parser Tok R₁ xs) {t} →
             ∂ (return f ⊙ p) t ≅P return f ⊙ ∂ p t
∂-return-⊙ f p {t} =
  ∂ (return f ⊙ p) t                    ≅⟨ ∂-⊙ (return f) p ⟩
  fail ⊙ p ∣ (return f ∣ fail) ⊙ ∂ p t  ≅⟨ left-zero p ∣
                                           (AdditiveMonoid.right-identity (return f)) ⊙′ (∂ p t ∎) ⟩
  fail ∣ return f ⊙ ∂ p t               ≅⟨ AdditiveMonoid.left-identity (return f ⊙ ∂ p t) ⟩
  return f ⊙ ∂ p t                      ∎

∂-⊙-return : ∀ {Tok R₁ R₂ fs}
             (p : Parser Tok (R₁ → R₂) fs) (x : R₁) {t} →
             ∂ (p ⊙ return x) t ≅P ∂ p t ⊙ return x
∂-⊙-return {fs = fs} p x {t} =
  ∂ (p ⊙ return x) t                     ≅⟨ ∂-⊙ p (return x) ⟩
  ∂ p t ⊙ return x ∣ ⋁ return fs ⊙ fail  ≅⟨ (∂ p t ⊙ return x ∎) ∣ right-zero (⋁ return fs) ⟩
  ∂ p t ⊙ return x ∣ fail                ≅⟨ AdditiveMonoid.right-identity (∂ p t ⊙ return x) ⟩
  ∂ p t ⊙ return x                       ∎

private

  -- ∂-⋁ is related to ∂ and ⋁.

  ∂-⋁′ : ∀ {Tok R₁ R₂ y} {ys : List R₁} {f : R₁ → List R₂}
         (xs : List R₁)
         (p : (x : R₁) → ∞? (Parser Tok R₂ (f x)) (y ∷ ys)) (t : Tok) →
         ∂-⋁ xs p t ≅P ⋁ (λ x → ∂ (♭? (p x)) t) xs
  ∂-⋁′ []       p t = fail ∎
  ∂-⋁′ (x ∷ xs) p t with p x
  ... | ⟨ p′ ⟩ =
    ∂ p′ t ∣ ∂-⋁ xs p t                   ≅⟨ (∂ p′ t ∎) ∣ ∂-⋁′ xs p t ⟩
    ∂ p′ t ∣ ⋁ (λ x → ∂ (♭? (p x)) t) xs  ∎

-- Unfolding lemma for ∂ applied to _>>=_.

∂->>= : ∀ {Tok R₁ R₂ xs} {f : R₁ → List R₂}
        (p₁ : Parser Tok R₁ xs)
        (p₂ : (x : R₁) → ∞? (Parser Tok R₂ (f x)) xs) {t} →
        ∂ (p₁ >>= p₂) t ≅P
        ∂ p₁ t ⟫= (♭? ∘ p₂) ∣ ⋁ (λ x → ∂ (♭? (p₂ x)) t) xs
∂->>= {xs = []} p₁ p₂ {t} =
  ∂ (p₁ >>= p₂) t             ≅⟨ ∂ (p₁ >>= p₂) t ∎ ⟩
  ∂ p₁ t ⟫= (♭? ∘ p₂)         ≅⟨ sym $ AdditiveMonoid.right-identity (∂ p₁ t ⟫= (♭? ∘ p₂)) ⟩
  ∂ p₁ t ⟫= (♭? ∘ p₂) ∣ fail  ∎
∂->>= {xs = x ∷ xs} p₁ p₂ {t} =
  ∂ (p₁ >>= p₂) t                                           ≅⟨ ∂ (p₁ >>= p₂) t ∎ ⟩
  ∂ p₁ t ⟫= (♭? ∘ p₂) ∣ ∂-⋁ (x ∷ xs) p₂ t                   ≅⟨ (∂ p₁ t ⟫= (♭? ∘ p₂) ∎) ∣ ∂-⋁′ (x ∷ xs) p₂ t ⟩
  ∂ p₁ t ⟫= (♭? ∘ p₂) ∣ ⋁ (λ x → ∂ (♭? (p₂ x)) t) (x ∷ xs)  ∎

private

  -- Preliminary unfolding lemma for ∂ applied to _>>=!_.

  ∂->>=!′ : ∀ {Tok R₁ R₂ xs}
            (p₁ : ∞ (Parser Tok R₁ xs))
            (p₂ : (x : R₁) → ∞? (Parser Tok R₂ []) xs) {t} →
            ∂ (p₁ >>=! p₂) t ≅P
            ♯ (∂ (♭ p₁) t) >>=! (λ x → ♯? (♭? (p₂ x))) ∣
              ⋁ (λ x → ∂ (♭? (p₂ x)) t) xs
  ∂->>=!′ {xs = []} p₁ p₂ {t} =
    ∂ (p₁ >>=! p₂) t                      ≅⟨ (_ ∎) >>=! (λ _ → _ ∎) ⟩
    _ >>=! (λ x → ♯? (♭? (p₂ x)))         ≅⟨ sym $ AdditiveMonoid.right-identity
                                                     (_ >>=! (λ x → ♯? (♭? (p₂ x)))) ⟩
    _ >>=! (λ x → ♯? (♭? (p₂ x))) ∣ fail  ∎
  ∂->>=!′ {xs = x ∷ xs} p₁ p₂ {t} =
    ∂ (p₁ >>=! p₂) t                    ≅⟨ (_ ∎) >>=! (λ _ → _ ∎) ∣ (_ ∎) ⟩

    _ >>=! (λ x → ♯? (♭? (p₂ x))) ∣
    ∂-⋁ (x ∷ xs) p₂ t                   ≅⟨ (_ >>=! (λ x → ♯? (♭? (p₂ x))) ∎) ∣ ∂-⋁′ (x ∷ xs) p₂ t ⟩

    _ >>=! (λ x → ♯? (♭? (p₂ x))) ∣
    ⋁ (λ x → ∂ (♭? (p₂ x)) t) (x ∷ xs)  ∎

-- _>>=!_ and _>>=_ are equivalent.

>>=!≅>>= : ∀ {Tok R₁ R₂ xs}
           (p₁ : ∞ (Parser Tok R₁ xs))
           (p₂ : (x : R₁) → ∞? (Parser Tok R₂ []) xs) →
           p₁ >>=! p₂ ≅P ♭ p₁ >>= p₂
>>=!≅>>= {xs = xs} p₁ p₂ =
  BagMonoid.reflexive (P.sym $ ListProp.Monad.right-zero xs) ∷ λ t → ♯ (
    ∂ (p₁ >>=! p₂) t                                              ≅⟨ ∂->>=!′ p₁ p₂ ⟩
    _ >>=! (λ x → ♯? (♭? (p₂ x))) ∣ ⋁ (λ x → ∂ (♭? (p₂ x)) t) xs  ≅⟨ >>=!≅>>= _ _ ∣ (_ ∎) ⟩
    ∂ (♭ p₁) t ⟫= (♭? ∘ p₂) ∣ ⋁ (λ x → ∂ (♭? (p₂ x)) t) xs        ≅⟨ sym $ ∂->>= (♭ p₁) p₂ ⟩
    ∂ (♭ p₁ >>= p₂) t                                             ∎)

-- Unfolding lemma for ∂ applied to _>>=!_.

∂->>=! : ∀ {Tok R₁ R₂ xs}
         (p₁ : ∞ (Parser Tok R₁ xs))
         (p₂ : (x : R₁) → ∞? (Parser Tok R₂ []) xs) {t} →
         ∂ (p₁ >>=! p₂) t ≅P
         ∂ (♭ p₁) t ⟫= (♭? ∘ p₂) ∣ ⋁ (λ x → ∂ (♭? (p₂ x)) t) xs
∂->>=! {xs = xs} p₁ p₂ {t} =
  ∂ (p₁ >>=! p₂) t                                              ≅⟨ ∂->>=!′ p₁ p₂ ⟩
  _ >>=! (λ x → ♯? (♭? (p₂ x))) ∣ ⋁ (λ x → ∂ (♭? (p₂ x)) t) xs  ≅⟨ >>=!≅>>= _ _ ∣ (_ ∎) ⟩
  ∂ (♭ p₁) t ⟫= (♭? ∘ p₂) ∣ ⋁ (λ x → ∂ (♭? (p₂ x)) t) xs        ∎

-- Unfolding lemma for ∂ applied to _⟫=_.

∂-⟫= : ∀ {Tok R₁ R₂ xs} {f : R₁ → List R₂}
       (p₁ : Parser Tok R₁ xs)
       (p₂ : (x : R₁) → Parser Tok R₂ (f x)) {t} →
       ∂ (p₁ ⟫= p₂) t ≅P ∂ p₁ t ⟫= p₂ ∣ ⋁ (λ x → ∂ (p₂ x) t) xs
∂-⟫= {xs = xs} p₁ p₂ {t} =
  ∂ (p₁ ⟫= p₂) t                               ≅⟨ ∂->>= p₁ (♯? ∘ p₂) ⟩

  ∂ p₁ t ⟫= (♭? ∘ ♯? {xs = xs} ∘ p₂) ∣
  ⋁ (λ x → ∂ (♭? (♯? {xs = xs} (p₂ x))) t) xs  ≅⟨ (∂ p₁ t ∎) ⟫=′ (λ _ → Eq.complete (♭♯.correct xs)) ∣
                                                  ⋁′ (λ _ → Eq.complete (∂-cong-≅ (♭♯.correct xs)))
                                                     (BagS.refl {x = xs}) ⟩
  ∂ p₁ t ⟫= p₂ ∣ ⋁ (λ x → ∂ (p₂ x) t) xs       ∎
