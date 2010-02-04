------------------------------------------------------------------------
-- Laws related to _>>=_
------------------------------------------------------------------------

module TotalParserCombinators.Laws.Monad where

open import Category.Monad
open import Coinduction
open import Data.List as List
import Data.List.Any as Any
import Data.List.Any.BagEquality as BagEq
import Data.List.Properties as ListProp
open import Function
open import Relation.Binary

private
  open module ListMonad = RawMonad List.monad
         using () renaming (_>>=_ to _>>=′_)
  module BagS {A : Set} = Setoid (Any.Membership-≡.Bag-equality {A})

open import TotalParserCombinators.BreadthFirst
open import TotalParserCombinators.Coinduction
open import TotalParserCombinators.Congruence.Parser as Eq
import TotalParserCombinators.Laws.AdditiveMonoid as AdditiveMonoid
open import TotalParserCombinators.Laws.Derivative as Derivative
  hiding (left-zero; right-zero; >>=!≅>>=)
import TotalParserCombinators.Laws.Or as Or
open import TotalParserCombinators.Lib
open import TotalParserCombinators.Parser
open import TotalParserCombinators.Semantics

------------------------------------------------------------------------
-- _>>=_, _>>=!_ and _⟫=_ are equivalent

open Derivative public using (>>=!≅>>=)

⟫=≅>>= : ∀ {Tok R₁ R₂ xs} {f : R₁ → List R₂}
         (p₁ : Parser Tok R₁ xs)
         (p₂ : (x : R₁) → ∞? (Parser Tok R₂ (f x)) xs) →
         p₁ ⟫= (♭? ∘ p₂) ≅P p₁ >>= p₂
⟫=≅>>= {xs = xs} p₁ p₂ =
  p₁ ⟫= (♭? ∘ p₂)  ≅⟨ (p₁ ∎) >>= (λ _ → Eq.complete (♭♯.correct xs)) ⟩
  p₁ >>= p₂        ∎

>>=!≅⟫= : ∀ {Tok R₁ R₂ xs}
          (p₁ : ∞ (Parser Tok R₁ xs))
          (p₂ : (x : R₁) → ∞? (Parser Tok R₂ []) xs) →
          p₁ >>=! p₂ ≅P ♭ p₁ ⟫= (♭? ∘ p₂)
>>=!≅⟫= p₁ p₂ =
  p₁   >>=! p₂        ≅⟨ >>=!≅>>= p₁ p₂ ⟩
  ♭ p₁ >>=  p₂        ≅⟨ sym $ ⟫=≅>>= (♭ p₁) p₂ ⟩
  ♭ p₁  ⟫= (♭? ∘ p₂)  ∎

------------------------------------------------------------------------
-- _⟫=_, return, _∣_ and fail form a monad with a zero and a plus

-- If the laws below are combined with the additive monoid laws this
-- means that we have something which resembles an idempotent semiring
-- (if we restrict ourselves to language equivalence).

left-zero : ∀ {Tok R₁ R₂} {f : R₁ → List R₂}
            (p : (x : R₁) → Parser Tok R₂ (f x)) →
            fail ⟫= p ≅P fail
left-zero {f = f} p =
  BagS.reflexive (ListProp.Monad.left-zero f) ∷ λ t → ♯ (
    ∂ (fail ⟫= p) t     ≅⟨ ∂-⟫= fail p {t} ⟩
    (fail ⟫= p) ∣ fail  ≅⟨ AdditiveMonoid.right-identity (fail ⟫= p) ⟩
    fail ⟫= p           ≅⟨ left-zero p ⟩
    fail                ∎)

right-zero : ∀ {Tok R₁ R₂} {xs : List R₁}
             (p : Parser Tok R₁ xs) →
             (p ⟫= λ _ → fail) ≅P fail {Tok = Tok} {R = R₂}
right-zero {xs = xs} p =
  BagS.reflexive (ListProp.Monad.right-zero xs) ∷ λ t → ♯ (
    ∂ (p ⟫= λ _ → fail) t                      ≅⟨ ∂-⟫= p (λ _ → fail) ⟩
    ∂ p t ⟫= (λ _ → fail) ∣ ⋁ (λ _ → fail) xs  ≅⟨ right-zero (∂ p t) ∣ Or.zero xs ⟩
    fail ∣ fail                                ≅⟨ AdditiveMonoid.left-identity fail ⟩
    fail                                       ∎)

left-distributive : ∀ {Tok R₁ R₂ xs} {f g : R₁ → List R₂}
                    (p₁ : Parser Tok R₁ xs)
                    (p₂ : (x : R₁) → Parser Tok R₂ (f x))
                    (p₃ : (x : R₁) → Parser Tok R₂ (g x)) →
                    p₁ ⟫= (λ x → p₂ x ∣ p₃ x) ≅P p₁ ⟫= p₂ ∣ p₁ ⟫= p₃
left-distributive {xs = xs} {f} {g} p₁ p₂ p₃ =
  BagEq.>>=-left-distributive xs ∷ λ t → ♯ (
    ∂ (p₁ ⟫= (λ x → p₂ x ∣ p₃ x)) t             ≅⟨ ∂-⟫= p₁ (λ x → p₂ x ∣ p₃ x) ⟩

    ∂ p₁ t ⟫= (λ x → p₂ x ∣ p₃ x) ∣
    ⋁ (λ x → ∂ (p₂ x) t ∣ ∂ (p₃ x) t) xs        ≅⟨ left-distributive (∂ p₁ t) p₂ p₃ ∣
                                                   Or.distrib-∣ (λ x → ∂ (p₂ x) t) (λ x → ∂ (p₃ x) t) xs ⟩
    (∂ p₁ t ⟫= p₂ ∣ ∂ p₁ t ⟫= p₃) ∣
    (⋁ (λ x → ∂ (p₂ x) t) xs ∣
     ⋁ (λ x → ∂ (p₃ x) t) xs)                   ≅⟨ AdditiveMonoid.swap
                                                     (∂ p₁ t ⟫= p₂) (∂ p₁ t ⟫= p₃)
                                                     (⋁ (λ x → ∂ (p₂ x) t) xs) (⋁ (λ x → ∂ (p₃ x) t) xs) ⟩
    (∂ p₁ t ⟫= p₂ ∣ ⋁ (λ x → ∂ (p₂ x) t) xs) ∣
    (∂ p₁ t ⟫= p₃ ∣ ⋁ (λ x → ∂ (p₃ x) t) xs)    ≅⟨ sym (∂-⟫= p₁ p₂ ∣ ∂-⟫= p₁ p₃) ⟩

    ∂ (p₁ ⟫= p₂) t ∣ ∂ (p₁ ⟫= p₃) t             ∎)

right-distributive : ∀ {Tok R₁ R₂ xs₁ xs₂} {f : R₁ → List R₂}
                     (p₁ : Parser Tok R₁ xs₁)
                     (p₂ : Parser Tok R₁ xs₂)
                     (p₃ : (x : R₁) → Parser Tok R₂ (f x)) →
                     (p₁ ∣ p₂) ⟫= p₃ ≅P p₁ ⟫= p₃ ∣ p₂ ⟫= p₃
right-distributive {xs₁ = xs₁} {xs₂} {f} p₁ p₂ p₃ =
  BagS.reflexive (ListProp.Monad.right-distributive xs₁ xs₂ f) ∷ λ t → ♯ (
    ∂ ((p₁ ∣ p₂) ⟫= p₃) t                        ≅⟨ ∂-⟫= (p₁ ∣ p₂) p₃ ⟩

    (∂ p₁ t ∣ ∂ p₂ t) ⟫= p₃ ∣
    ⋁ (λ x → ∂ (p₃ x) t) (xs₁ ++ xs₂)            ≅⟨ right-distributive (∂ p₁ t) (∂ p₂ t) p₃ ∣
                                                    Or.distrib-++ (λ x → ∂ (p₃ x) t) xs₁ xs₂ ⟩
    ((∂ p₁ t ⟫= p₃) ∣ (∂ p₂ t ⟫= p₃)) ∣
    (⋁ (λ x → ∂ (p₃ x) t) xs₁ ∣
     ⋁ (λ x → ∂ (p₃ x) t) xs₂)                   ≅⟨ AdditiveMonoid.swap
                                                      (∂ p₁ t ⟫= p₃) (∂ p₂ t ⟫= p₃)
                                                      (⋁ (λ x → ∂ (p₃ x) t) xs₁) (⋁ (λ x → ∂ (p₃ x) t) xs₂) ⟩
    (∂ p₁ t ⟫= p₃ ∣ ⋁ (λ x → ∂ (p₃ x) t) xs₁) ∣
    (∂ p₂ t ⟫= p₃ ∣ ⋁ (λ x → ∂ (p₃ x) t) xs₂)    ≅⟨ sym (∂-⟫= p₁ p₃ ∣ ∂-⟫= p₂ p₃) ⟩

    ∂ (p₁ ⟫= p₃) t ∣ ∂ (p₂ ⟫= p₃) t              ∎)

left-identity : ∀ {Tok R₁ R₂} {f : R₁ → List R₂}
                (x : R₁) (p : (x : R₁) → Parser Tok R₂ (f x)) →
                return x ⟫= p ≅P p x
left-identity {f = f} x p =
  BagS.reflexive (ListProp.Monad.left-identity x f) ∷ λ t → ♯ (
    ∂ (return x ⟫= p) t             ≅⟨ ∂-⟫= (return x) p ⟩
    fail ⟫= p ∣ (∂ (p x) t ∣ fail)  ≅⟨ left-zero p ∣
                                       AdditiveMonoid.right-identity (∂ (p x) t) ⟩
    fail      ∣ ∂ (p x) t           ≅⟨ AdditiveMonoid.left-identity (∂ (p x) t) ⟩
    ∂ (p x) t                       ∎)

right-identity : ∀ {Tok R xs}
                 (p : Parser Tok R xs) → p ⟫= return ≅P p
right-identity {xs = xs} p =
  BagS.reflexive (ListProp.Monad.right-identity xs) ∷ λ t → ♯ (
    ∂ (p ⟫= return) t                    ≅⟨ ∂-⟫= p return ⟩
    ∂ p t ⟫= return ∣ ⋁ (λ _ → fail) xs  ≅⟨ right-identity (∂ p t) ∣ Or.zero xs ⟩
    ∂ p t           ∣ fail               ≅⟨ AdditiveMonoid.right-identity (∂ p t) ⟩
    ∂ p t                                ∎)

-- Unfolding lemma for ⋁.

⋁≅return⋆⟫= :
  ∀ {Tok R₁ R₂} {f : R₁ → List R₂}
  (p : (x : R₁) → Parser Tok R₂ (f x)) (xs : List R₁) →
  ⋁ p xs ≅P return⋆ xs ⟫= p
⋁≅return⋆⟫= p []       =
  fail       ≅⟨ sym (left-zero p) ⟩
  fail ⟫= p  ∎
⋁≅return⋆⟫= p (x ∷ xs) =
  p x ∣ ⋁ p xs                         ≅⟨ sym (left-identity x p) ∣ ⋁≅return⋆⟫= p xs ⟩
  (return x ⟫= p) ∣ (return⋆ xs ⟫= p)  ≅⟨ sym (right-distributive (return x) (return⋆ xs) p) ⟩
  (return x ∣ return⋆ xs) ⟫= p         ∎

mutual

  associative : ∀ {Tok R₁ R₂ R₃ xs}
                  {f : R₁ → List R₂} {g : R₂ → List R₃}
                (p₁ : Parser Tok R₁ xs)
                (p₂ : (x : R₁) → Parser Tok R₂ (f x))
                (p₃ : (x : R₂) → Parser Tok R₃ (g x)) →
                (p₁ ⟫= λ x → p₂ x ⟫= p₃) ≅P p₁ ⟫= p₂ ⟫= p₃
  associative {xs = xs} {f} {g} p₁ p₂ p₃ =
    BagS.reflexive (ListProp.Monad.associative xs f g) ∷ λ t → ♯ (
      ∂ (p₁ ⟫= λ x → p₂ x ⟫= p₃) t               ≅⟨ ∂-⟫= p₁ (λ x → p₂ x ⟫= p₃) ⟩

      ∂ p₁ t ⟫= (λ x → p₂ x ⟫= p₃) ∣
      ⋁ (λ x → ∂ (p₂ x ⟫= p₃) t) xs              ≅⟨ (∂ p₁ t ⟫= (λ x → p₂ x ⟫= p₃) ∎) ∣
                                                    ⋁′ (λ x → ∂-⟫= (p₂ x) p₃) (BagS.refl {x = xs}) ⟩
      ∂ p₁ t ⟫= (λ x → p₂ x ⟫= p₃) ∣
      ⋁ (λ x → ∂ (p₂ x) t ⟫= p₃ ∣
               ⋁ (λ x → ∂ (p₃ x) t) (f x)) xs    ≅⟨ (∂ p₁ t ⟫= (λ x → p₂ x ⟫= p₃) ∎) ∣
                                                    Or.distrib-∣ (λ x → ∂ (p₂ x) t ⟫= p₃)
                                                                 (λ x → ⋁ (λ x → ∂ (p₃ x) t) (f x)) xs ⟩
      ∂ p₁ t ⟫= (λ x → p₂ x ⟫= p₃) ∣
      (⋁ (λ x → ∂ (p₂ x) t ⟫= p₃) xs ∣
       ⋁ (λ x → ⋁ (λ x → ∂ (p₃ x) t) (f x)) xs)  ≅⟨ associative (∂ p₁ t) p₂ p₃ ∣
                                                    (⋁-⟫=-distrib (λ x → ∂ (p₂ x) t) p₃ xs ∣
                                                     Or.⋁⋁≅⋁>>= (λ x → ∂ (p₃ x) t) f xs) ⟩

      ∂ p₁ t ⟫= p₂ ⟫= p₃ ∣
      (⋁ (λ x → ∂ (p₂ x) t) xs ⟫= p₃ ∣
       ⋁ (λ x → ∂ (p₃ x) t) (xs >>=′ f))         ≅⟨ sym $ AdditiveMonoid.associative
                                                            (∂ p₁ t ⟫= p₂ ⟫= p₃)
                                                            (⋁ (λ x → ∂ (p₂ x) t) xs ⟫= p₃)
                                                            (⋁ (λ x → ∂ (p₃ x) t) (xs >>=′ f)) ⟩
      ∂ p₁ t ⟫= p₂ ⟫= p₃ ∣
      ⋁ (λ x → ∂ (p₂ x) t) xs ⟫= p₃ ∣
      ⋁ (λ x → ∂ (p₃ x) t) (xs >>=′ f)           ≅⟨ sym (right-distributive
                                                           (∂ p₁ t ⟫= p₂) (⋁ (λ x → ∂ (p₂ x) t) xs) p₃) ∣
                                                    (⋁ (λ x → ∂ (p₃ x) t) (xs >>=′ f) ∎) ⟩
      (∂ p₁ t ⟫= p₂ ∣
       ⋁ (λ x → ∂ (p₂ x) t) xs) ⟫= p₃ ∣
      ⋁ (λ x → ∂ (p₃ x) t) (xs >>=′ f)           ≅⟨ sym (∂-⟫= p₁ p₂) ⟫=′ (λ x → p₃ x ∎) ∣
                                                    (⋁ (λ x → ∂ (p₃ x) t) (xs >>=′ f) ∎) ⟩
      ∂ (p₁ ⟫= p₂) t ⟫= p₃ ∣
      ⋁ (λ x → ∂ (p₃ x) t) (xs >>=′ f)           ≅⟨ sym $ ∂-⟫= (p₁ ⟫= p₂) p₃ ⟩

      ∂ (p₁ ⟫= p₂ ⟫= p₃) t                       ∎)

  -- ⋁ distributes over _⟫=_.

  ⋁-⟫=-distrib :
    ∀ {Tok R₁ R₂ R₃} {f₁ : R₁ → List R₂} {f₂ : R₂ → List R₃}
    (p₁ : (x : R₁) → Parser Tok R₂ (f₁ x))
    (p₂ : (x : R₂) → Parser Tok R₃ (f₂ x)) (xs : List R₁) →
    ⋁ (λ x → p₁ x ⟫= p₂) xs ≅P ⋁ p₁ xs ⟫= p₂
  ⋁-⟫=-distrib p₁ p₂ xs =
    ⋁ (λ x → p₁ x ⟫= p₂) xs           ≅⟨ ⋁≅return⋆⟫= (λ x → p₁ x ⟫= p₂) xs ⟩
    return⋆ xs ⟫= (λ x → p₁ x ⟫= p₂)  ≅⟨ associative (return⋆ xs) p₁ p₂ ⟩
    return⋆ xs ⟫= p₁ ⟫= p₂            ≅⟨ sym $ ⋁≅return⋆⟫= p₁ xs ⟫=′ (λ x → p₂ x ∎) ⟩
    ⋁ p₁ xs ⟫= p₂                     ∎
