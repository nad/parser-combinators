------------------------------------------------------------------------
-- Pointwise lifting of (binary) initial bag operators to parsers
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

open import Data.List
import Data.List.Any as Any
open import Function.Related as Related using (⌊_⌋⇔; ⇔⌊_⌋)
open Any.Membership-≡ using (_∈_) renaming (_≈[_]_ to _List-≈[_]_)

module TotalParserCombinators.Pointwise
  (R₁ R₂ : Set) {R₃ : Set}

  -- An initial bag operator.
  (_∙_ : List R₁ → List R₂ → List R₃)

  -- The operator must preserve bag and set equality.
  (_∙-cong_ : ∀ {k xs₁ xs₁′ xs₂ xs₂′} →
              xs₁ List-≈[ ⌊ ⇔⌊ k ⌋ ⌋⇔ ] xs₁′ →
              xs₂ List-≈[ ⌊ ⇔⌊ k ⌋ ⌋⇔ ] xs₂′ →
              (xs₁ ∙ xs₂) List-≈[ ⌊ ⇔⌊ k ⌋ ⌋⇔ ] (xs₁′ ∙ xs₂′))
  where

open import Coinduction
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence using (_⇔_; module Equivalence)
open import Function.Inverse using (_↔_; module Inverse)

open import TotalParserCombinators.Congruence as C using (_≈[_]P_; _≅P_)
import TotalParserCombinators.Congruence.Sound as CS
open import TotalParserCombinators.Derivative as D
import TotalParserCombinators.InitialBag as I
open import TotalParserCombinators.Laws
open import TotalParserCombinators.Lib
open import TotalParserCombinators.Parser
open import TotalParserCombinators.Semantics using (_∈_·_)

------------------------------------------------------------------------
-- Lift

-- A lifting of the initial bag operator _∙_ to the level of parsers.
--
-- Note that this definition is closely related to Theorem 4.4 in
-- Brzozowski's paper "Derivatives of Regular Expressions".
--
-- Note also that _∙_ is allowed to pattern match on one of the input
-- indices, so it may not be obvious that lift preserves equality.
-- This fact is established explicitly below (by making use of
-- _∙-cong_).

lift : ∀ {Tok xs₁ xs₂} →
       Parser Tok R₁ xs₁ → Parser Tok R₂ xs₂ →
       Parser Tok R₃ (xs₁ ∙ xs₂)
lift p₁ p₂ =
    (token >>= λ t → ♯ lift (D t p₁) (D t p₂))
  ∣ return⋆ (initial-bag p₁ ∙ initial-bag p₂)

------------------------------------------------------------------------
-- Properties of lift

-- D distributes over lift.

D-lift : ∀ {Tok xs₁ xs₂ t}
         (p₁ : Parser Tok R₁ xs₁) (p₂ : Parser Tok R₂ xs₂) →
         D t (lift p₁ p₂) ≅P lift (D t p₁) (D t p₂)
D-lift {xs₁ = xs₁} {xs₂} {t} p₁ p₂ =
  D t (lift p₁ p₂)                               ≅⟨ D t (lift p₁ p₂) ∎ ⟩

  (return t >>= λ t → lift (D t p₁) (D t p₂)) ∣
    D t (return⋆ (xs₁ ∙ xs₂))                    ≅⟨ Monad.left-identity t (λ t → lift (D t p₁) (D t p₂)) ∣
                                                    D.D-return⋆ (xs₁ ∙ xs₂) ⟩
  lift (D t p₁) (D t p₂) ∣ fail                  ≅⟨ AdditiveMonoid.right-identity (lift (D t p₁) (D t p₂)) ⟩

  lift (D t p₁) (D t p₂)                         ∎
  where open C using (_≅⟨_⟩_; _∎; _∣_)

-- lift preserves equality.

lift-cong : ∀ {k Tok xs₁ xs₁′ xs₂ xs₂′}
              {p₁ : Parser Tok R₁ xs₁} {p₁′ : Parser Tok R₁ xs₁′}
              {p₂ : Parser Tok R₂ xs₂} {p₂′ : Parser Tok R₂ xs₂′} →
            p₁ ≈[ ⌊ ⇔⌊ k ⌋ ⌋⇔ ]P p₁′ → p₂ ≈[ ⌊ ⇔⌊ k ⌋ ⌋⇔ ]P p₂′ →
            lift p₁ p₂ ≈[ ⌊ ⇔⌊ k ⌋ ⌋⇔ ]P lift p₁′ p₂′
lift-cong {k} {xs₁ = xs₁} {xs₁′} {xs₂} {xs₂′} {p₁} {p₁′} {p₂} {p₂′}
  p₁≈p₁′ p₂≈p₂′ = lemma ∷ λ t → ♯ (
  D t (lift p₁ p₂)          ≅⟨ D-lift p₁ p₂ ⟩
  lift (D t p₁) (D t p₂)    ≈⟨ lift-cong (CS.D-cong p₁≈p₁′) (CS.D-cong p₂≈p₂′) ⟩
  lift (D t p₁′) (D t p₂′)  ≅⟨ sym (D-lift p₁′ p₂′) ⟩
  D t (lift p₁′ p₂′)        ∎)
  where
  open C using (_≅⟨_⟩_; _≈⟨_⟩_; _∎; sym; _∷_)

  lemma : (xs₁ ∙ xs₂) List-≈[ ⌊ ⇔⌊ k ⌋ ⌋⇔ ] (xs₁′ ∙ xs₂′)
  lemma = I.cong (CS.sound p₁≈p₁′) ∙-cong I.cong (CS.sound p₂≈p₂′)

-- Lifts a property from _∙_ to lift. For examples of its use, see
-- TotalParserCombinators.{And,AsymmetricChoice,Not}.

lift-property :
  (P : ∀ {ℓ} → (R₁ → Set ℓ) → (R₂ → Set ℓ) → (R₃ → Set ℓ) → Set ℓ)

  (P-cong :
   ∀ {ℓ}  {F₁  : R₁ → Set ℓ}  {F₂  : R₂ → Set ℓ}  {F₃  : R₃ → Set ℓ}
     {ℓ′} {F₁′ : R₁ → Set ℓ′} {F₂′ : R₂ → Set ℓ′} {F₃′ : R₃ → Set ℓ′} →
   (∀ x → F₁ x ↔ F₁′ x) → (∀ x → F₂ x ↔ F₂′ x) → (∀ x → F₃ x ↔ F₃′ x) →
   P F₁ F₂ F₃ ⇔ P F₁′ F₂′ F₃′) →

  (P-∙ :
     ∀ {xs₁ xs₂} →
     P (λ x → x ∈ xs₁) (λ x → x ∈ xs₂) (λ x → x ∈ (xs₁ ∙ xs₂))) →

  ∀ {Tok xs₁ xs₂ s}
  (p₁ : Parser Tok R₁ xs₁) (p₂ : Parser Tok R₂ xs₂) →
  P (λ x → x ∈ p₁ · s) (λ x → x ∈ p₂ · s) (λ x → x ∈ lift p₁ p₂ · s)

lift-property P P-cong P-∙ {s = []} p₁ p₂ =
  Equivalence.from
    (P (λ x → x ∈ p₁ · []) (λ x → x ∈ p₂ · [])
       (λ x → x ∈ lift p₁ p₂ · [])                            ≈⟨ P-cong (λ _ → I.correct) (λ _ → I.correct) (λ _ → I.correct) ⟩

     P (λ x → x ∈ initial-bag p₁) (λ x → x ∈ initial-bag p₂)
       (λ x → x ∈ (initial-bag p₁ ∙ initial-bag p₂))          ∎

    ) ⟨$⟩ P-∙
  where open Related.EquationalReasoning

lift-property P P-cong P-∙ {s = t ∷ s} p₁ p₂ =
   Equivalence.from
    (P (λ x → x ∈ p₁ · t ∷ s) (λ x → x ∈ p₂ · t ∷ s)
       (λ x → x ∈ lift p₁ p₂ · t ∷ s)                 ≈⟨ sym $ P-cong (λ _ → D.correct) (λ _ → D.correct) (λ _ → D.correct) ⟩

     P (λ x → x ∈ D t p₁ · s) (λ x → x ∈ D t p₂ · s)
       (λ x → x ∈ D t (lift p₁ p₂) · s)               ≈⟨ P-cong (λ _ → _ ∎) (λ _ → _ ∎) (λ _ → CS.sound (D-lift p₁ p₂)) ⟩

     P (λ x → x ∈ D t p₁ · s) (λ x → x ∈ D t p₂ · s)
       (λ x → x ∈ lift (D t p₁) (D t p₂) · s)         ∎

    ) ⟨$⟩ lift-property P P-cong P-∙ (D t p₁) (D t p₂)
  where open Related.EquationalReasoning
