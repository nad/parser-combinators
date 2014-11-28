------------------------------------------------------------------------
-- Recognisers form a Kleene algebra
------------------------------------------------------------------------

module TotalRecognisers.LeftRecursion.KleeneAlgebra (Tok : Set) where

open import Algebra
import Algebra.Properties.BooleanAlgebra
open import Coinduction
open import Data.Bool hiding (_∧_)
import Data.Bool.Properties as Bool
private
  module BoolCS = CommutativeSemiring Bool.commutativeSemiring-∨-∧
  module BoolBA = Algebra.Properties.BooleanAlgebra Bool.booleanAlgebra
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence as Eq using (_⇔_; equivalence)
open import Data.List as List
private
  module ListMonoid {A : Set} = Monoid (List.monoid A)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product as Prod
open import Relation.Binary.HeterogeneousEquality using (_≅_; refl)
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; refl; _≗_)
open import Relation.Nullary

import TotalRecognisers.LeftRecursion
open TotalRecognisers.LeftRecursion Tok hiding (left-zero)
import TotalRecognisers.LeftRecursion.Lib
open TotalRecognisers.LeftRecursion.Lib Tok
open ⊙ using (_⊙′_)
open KleeneStar₂

------------------------------------------------------------------------
-- The relation _≤_ is a partial order with respect to _≈_

module PartialOrder where

  reflexive : ∀ {n} {p : P n} → p ≤ p
  reflexive = id

  trans : ∀ {n₁ n₂ n₃} {p₁ : P n₁} {p₂ : P n₂} {p₃ : P n₃} →
          p₁ ≤ p₂ → p₂ ≤ p₃ → p₁ ≤ p₃
  trans p₁≤p₂ p₂≤p₃ = p₂≤p₃ ∘ p₁≤p₂

  antisym : ∀ {n₁ n₂} {p₁ : P n₁} {p₂ : P n₂} →
            p₁ ≤ p₂ → p₂ ≤ p₁ → p₁ ≈ p₂
  antisym p₁≤p₂ p₂≤p₁ = equivalence p₁≤p₂ p₂≤p₁

------------------------------------------------------------------------
-- The relation _≈_ is an equality, i.e. a congruential equivalence
-- relation

module Equivalence where

  reflexive : ∀ {n} {p : P n} → p ≈ p
  reflexive = Eq.id

  sym : ∀ {n₁ n₂} {p₁ : P n₁} {p₂ : P n₂} → p₁ ≈ p₂ → p₂ ≈ p₁
  sym p₁≈p₂ = Eq.sym p₁≈p₂

  trans : ∀ {n₁ n₂ n₃} {p₁ : P n₁} {p₂ : P n₂} {p₃ : P n₃} →
          p₁ ≈ p₂ → p₂ ≈ p₃ → p₁ ≈ p₃
  trans p₁≈p₂ p₂≈p₃ = Eq._∘_ p₂≈p₃ p₁≈p₂

♭♯-cong : ∀ {n₁ n₂} b₁ b₂ {p₁ : P n₁} {p₂ : P n₂} →
          p₁ ≈ p₂ → ♭? (♯? {b₁} p₁) ≈ ♭? (♯? {b₂} p₂)
♭♯-cong b₁ b₂ {p₁} {p₂} rewrite ♭?♯? b₁ {p = p₁} | ♭?♯? b₂ {p = p₂} = id

fail-cong : fail ≈ fail
fail-cong = Equivalence.reflexive

empty-cong : empty ≈ empty
empty-cong = Equivalence.reflexive

sat-cong : {f₁ f₂ : Tok → Bool} → f₁ ≗ f₂ → sat f₁ ≈ sat f₂
sat-cong f₁≗f₂ = equivalence (helper f₁≗f₂) (helper (P.sym ∘ f₁≗f₂))
  where
  helper : {f₁ f₂ : Tok → Bool} → f₁ ≗ f₂ → sat f₁ ≤ sat f₂
  helper f₁≗f₂ (sat ok) = sat (P.subst T (f₁≗f₂ _) ok)

∣-cong : ∀ {n₁ n₂ n₃ n₄}
           {p₁ : P n₁} {p₂ : P n₂} {p₃ : P n₃} {p₄ : P n₄} →
         p₁ ≈′ p₃ → p₂ ≈′ p₄ → p₁ ∣ p₂ ≈′ p₃ ∣ p₄
∣-cong (refl ∷ rest₁) (refl ∷ rest₂) =
  refl ∷ λ t → ♯ ∣-cong (♭ (rest₁ t)) (♭ (rest₂ t))

·-cong : ∀ {n₁ n₂ n₃ n₄}
           {p₁ : ∞⟨ n₂ ⟩P n₁} {p₂ : ∞⟨ n₁ ⟩P n₂}
           {p₃ : ∞⟨ n₄ ⟩P n₃} {p₄ : ∞⟨ n₃ ⟩P n₄} →
         ♭? p₁ ≈ ♭? p₃ → ♭? p₂ ≈ ♭? p₄ → p₁ · p₂ ≈ p₃ · p₄
·-cong p₁≈p₃ p₂≈p₄ =
  Eq.Equivalence.from ≈⇔≤≥ ⟨$⟩
    Prod.zip helper helper
             (Eq.Equivalence.to ≈⇔≤≥ ⟨$⟩ p₁≈p₃)
             (Eq.Equivalence.to ≈⇔≤≥ ⟨$⟩ p₂≈p₄)
  where
  helper : ∀ {n₁ n₂ n₃ n₄}
             {p₁ : ∞⟨ n₂ ⟩P n₁} {p₂ : ∞⟨ n₁ ⟩P n₂}
             {p₃ : ∞⟨ n₄ ⟩P n₃} {p₄ : ∞⟨ n₃ ⟩P n₄} →
           ♭? p₁ ≤ ♭? p₃ → ♭? p₂ ≤ ♭? p₄ → p₁ · p₂ ≤ p₃ · p₄
  helper ₁≤₃ ₂≤₄ (∈p₁ · ∈p₂) = ₁≤₃ ∈p₁ · ₂≤₄ ∈p₂

⊙-cong : ∀ {n₁ n₂ n₃ n₄}
           {p₁ : P n₁} {p₂ : P n₂} {p₃ : P n₃} {p₄ : P n₄} →
         p₁ ≈ p₃ → p₂ ≈ p₄ → p₁ ⊙ p₂ ≈ p₃ ⊙ p₄
⊙-cong {n₁} {n₂} {n₃} {n₄} ₁≈₃ ₂≈₄ =
  ·-cong (♭♯-cong n₂ n₄ ₁≈₃) (♭♯-cong n₁ n₃ ₂≈₄)

nonempty-cong : ∀ {n₁ n₂} {p₁ : P n₁} {p₂ : P n₂} →
                p₁ ≈′ p₂ → nonempty p₁ ≈′ nonempty p₂
nonempty-cong (_ ∷ rest) = refl ∷ rest

cast-cong : ∀ {n₁ n₂ n₁′ n₂′}
              {p₁ : P n₁} {p₂ : P n₂}
              {eq₁ : n₁ ≡ n₁′} {eq₂ : n₂ ≡ n₂′} →
            p₁ ≈′ p₂ → cast eq₁ p₁ ≈′ cast eq₂ p₂
cast-cong {eq₁ = refl} {refl} (init ∷ rest) = init ∷ rest

⋆-cong : ∀ {n₁ n₂} {p₁ : P n₁} {p₂ : P n₂} →
         p₁ ≈ p₂ → p₁ ⋆ ≈ p₂ ⋆
⋆-cong p₁≈p₂ = Eq.Equivalence.from ≈⇔≤≥ ⟨$⟩
                 Prod.map helper helper
                   (Eq.Equivalence.to ≈⇔≤≥ ⟨$⟩ p₁≈p₂)
  where
  helper : ∀ {n₁ n₂} {p₁ : P n₁} {p₂ : P n₂} →
           p₁ ≤ p₂ → p₁ ⋆ ≤ p₂ ⋆
  helper p₁≤p₂ (∣-left  empty)                 = ∣-left empty
  helper p₁≤p₂ (∣-right (nonempty ∈p₁ · ∈p₁⋆)) =
    ∣-right {p₁ = empty} (nonempty (p₁≤p₂ ∈p₁) · helper p₁≤p₂ ∈p₁⋆)

^-cong : ∀ {n₁ n₂ i₁ i₂} {p₁ : P n₁} {p₂ : P n₂} →
         p₁ ≈ p₂ → i₁ ≡ i₂ → p₁ ^ i₁ ≈ p₂ ^ i₂
^-cong {i₁ = i} p₁≈p₂ refl =
  Eq.Equivalence.from ≈⇔≤≥ ⟨$⟩
    Prod.map (helper i) (helper i)
             (Eq.Equivalence.to ≈⇔≤≥ ⟨$⟩ p₁≈p₂)
  where
  helper : ∀ {n₁ n₂} {p₁ : P n₁} {p₂ : P n₂} i →
           p₁ ≤ p₂ → p₁ ^ i ≤ p₂ ^ i
  helper           zero    p₁≤p₂ empty   = empty
  helper {n₁} {n₂} (suc i) p₁≤p₂ ∈p₁⊙p₁ⁱ
    with ⊙.sound ⟨ n₁ ^ i ⟩-nullable ∈p₁⊙p₁ⁱ
  ... | ∈p₁ ⊙′ ∈p₁ⁱ = ⊙.complete (p₁≤p₂ ∈p₁) (helper i p₁≤p₂ ∈p₁ⁱ)

------------------------------------------------------------------------
-- A variant of _≤_

infix 4 _≲_

-- If _∣_ is viewed as the join operation of a join-semilattice, then
-- the following definition of order is natural.

_≲_ : ∀ {n₁ n₂} → P n₁ → P n₂ → Set
p₁ ≲ p₂ = p₁ ∣ p₂ ≈ p₂

-- The order above coincides with _≤_.

≤⇔≲ : ∀ {n₁ n₂} (p₁ : P n₁) (p₂ : P n₂) → p₁ ≤ p₂ ⇔ p₁ ≲ p₂
≤⇔≲ {n₁} p₁ p₂ =
  equivalence
    (λ (p₁≤p₂ : p₁ ≤ p₂) {_} →
       equivalence (helper p₁≤p₂) (∣-right {n₁ = n₁}))
    (λ (p₁≲p₂ : p₁ ≲ p₂) s∈p₁ → Eq.Equivalence.to p₁≲p₂ ⟨$⟩ ∣-left s∈p₁)
  where
  helper : p₁ ≤ p₂ → p₁ ∣ p₂ ≤ p₂
  helper p₁≤p₂ (∣-left  s∈p₁) = p₁≤p₂ s∈p₁
  helper p₁≤p₂ (∣-right s∈p₂) = s∈p₂

------------------------------------------------------------------------
-- Recognisers form a *-continuous Kleene algebra

-- The definition of *-continuous Kleene algebras used here is the one
-- given by Kozen in "On Kleene Algebras and Closed Semirings", except
-- for the presence of the recogniser indices. Kozen used the order
-- _≲_ in his definition, but as shown above this order is equivalent
-- to _≤_.

-- Additive idempotent commutative monoid. (One of the identity lemmas
-- could be omitted.)

∣-commutative : ∀ {n₁ n₂} (p₁ : P n₁) (p₂ : P n₂) → p₁ ∣ p₂ ≈′ p₂ ∣ p₁
∣-commutative {n₁} {n₂} p₁ p₂ =
  BoolCS.+-comm n₁ n₂ ∷ λ t → ♯ ∣-commutative (D t p₁) (D t p₂)

fail-left-identity : ∀ {n} (p : P n) → fail ∣ p ≈′ p
fail-left-identity p = refl ∷ λ t → ♯ fail-left-identity (D t p)

fail-right-identity : ∀ {n} (p : P n) → p ∣ fail ≈′ p
fail-right-identity {n} p =
  proj₂ BoolCS.+-identity n ∷ λ t → ♯ fail-right-identity (D t p)

∣-associative : ∀ {n₁ n₂ n₃} (p₁ : P n₁) (p₂ : P n₂) (p₃ : P n₃) →
                p₁ ∣ (p₂ ∣ p₃) ≈′ (p₁ ∣ p₂) ∣ p₃
∣-associative {n₁} {n₂} {n₃} p₁ p₂ p₃ =
  P.sym (BoolCS.+-assoc n₁ n₂ n₃) ∷ λ t →
    ♯ ∣-associative (D t p₁) (D t p₂) (D t p₃)

∣-idempotent : ∀ {n} (p : P n) → p ∣ p ≈′ p
∣-idempotent {n} p =
  BoolBA.∨-idempotent n ∷ λ t → ♯ ∣-idempotent (D t p)

-- Multiplicative monoid.

empty-left-identity : ∀ {n} (p : P n) → empty ⊙ p ≈ p
empty-left-identity {n} p =
  equivalence helper (λ s∈p → ⊙.complete empty s∈p)
  where
  helper : empty ⊙ p ≤ p
  helper ∈empty⊙p with ⊙.sound n ∈empty⊙p
  ... | empty ⊙′ s∈p = s∈p

empty-right-identity : ∀ {n} (p : P n) → p ⊙ empty ≈ p
empty-right-identity {n} p =
  equivalence
    helper
    (λ s∈p → cast∈ (proj₂ ListMonoid.identity _) refl
                   (⊙.complete s∈p empty))
  where
  helper : ∀ {s} → s ∈ p ⊙ empty → s ∈ p
  helper ∈p⊙empty with ⊙.sound true ∈p⊙empty
  helper ∈p⊙empty | ∈p ⊙′ empty =
    cast∈ (P.sym (proj₂ ListMonoid.identity _)) refl ∈p

·-associative : ∀ {n₁ n₂ n₃} (p₁ : P n₁) (p₂ : P n₂) (p₃ : P n₃) →
                p₁ ⊙ (p₂ ⊙ p₃) ≈ (p₁ ⊙ p₂) ⊙ p₃
·-associative {n₁} {n₂} {n₃} p₁ p₂ p₃ = equivalence helper₁ helper₂
  where
  helper₁ : p₁ ⊙ (p₂ ⊙ p₃) ≤ (p₁ ⊙ p₂) ⊙ p₃
  helper₁ ∈⊙⊙ with ⊙.sound (n₂ ∧ n₃) ∈⊙⊙
  ... | _⊙′_ {s₁ = s₁} ∈p₁ ∈⊙ with ⊙.sound n₃ ∈⊙
  ...   | ∈p₂ ⊙′ ∈p₃ =
    cast∈ (ListMonoid.assoc s₁ _ _) refl $
      ⊙.complete (⊙.complete ∈p₁ ∈p₂) ∈p₃

  helper₂ : (p₁ ⊙ p₂) ⊙ p₃ ≤ p₁ ⊙ (p₂ ⊙ p₃)
  helper₂ ∈⊙⊙ with ⊙.sound n₃ ∈⊙⊙
  ... | ∈⊙ ⊙′ ∈p₃ with ⊙.sound n₂ ∈⊙
  ...   | _⊙′_ {s₁ = s₁} ∈p₁ ∈p₂ =
    cast∈ (P.sym $ ListMonoid.assoc s₁ _ _) refl $
      ⊙.complete ∈p₁ (⊙.complete ∈p₂ ∈p₃)

-- Distributivity.

left-distributive :
  ∀ {n₁ n₂ n₃} (p₁ : P n₁) (p₂ : P n₂) (p₃ : P n₃) →
  p₁ ⊙ (p₂ ∣ p₃) ≈ p₁ ⊙ p₂ ∣ p₁ ⊙ p₃
left-distributive {n₁} {n₂} {n₃} p₁ p₂ p₃ = equivalence helper₁ helper₂
  where
  helper₁ : p₁ ⊙ (p₂ ∣ p₃) ≤ p₁ ⊙ p₂ ∣ p₁ ⊙ p₃
  helper₁ ∈⊙∣ with ⊙.sound (n₂ ∨ n₃) ∈⊙∣
  ... | ∈p₁ ⊙′ ∣-left  ∈p₂ = ∣-left $ ⊙.complete ∈p₁ ∈p₂
  ... | ∈p₁ ⊙′ ∣-right ∈p₃ = ∣-right {n₁ = n₁ ∧ n₂} $ ⊙.complete ∈p₁ ∈p₃

  helper₂ : p₁ ⊙ p₂ ∣ p₁ ⊙ p₃ ≤ p₁ ⊙ (p₂ ∣ p₃)
  helper₂ (∣-left ∈⊙) with ⊙.sound n₂ ∈⊙
  ... | ∈p₁ ⊙′ ∈p₂ = ⊙.complete ∈p₁ (∣-left ∈p₂)
  helper₂ (∣-right ∈⊙) with ⊙.sound n₃ ∈⊙
  ... | ∈p₁ ⊙′ ∈p₃ = ⊙.complete ∈p₁ (∣-right {n₁ = n₂} ∈p₃)

right-distributive :
  ∀ {n₁ n₂ n₃} (p₁ : P n₁) (p₂ : P n₂) (p₃ : P n₃) →
  (p₁ ∣ p₂) ⊙ p₃ ≈ p₁ ⊙ p₃ ∣ p₂ ⊙ p₃
right-distributive {n₁} {n₂} {n₃} p₁ p₂ p₃ = equivalence helper₁ helper₂
  where
  helper₁ : (p₁ ∣ p₂) ⊙ p₃ ≤ p₁ ⊙ p₃ ∣ p₂ ⊙ p₃
  helper₁ ∈∣⊙ with ⊙.sound n₃ ∈∣⊙
  ... | ∣-left  ∈p₁ ⊙′ ∈p₃ = ∣-left $ ⊙.complete ∈p₁ ∈p₃
  ... | ∣-right ∈p₂ ⊙′ ∈p₃ = ∣-right {n₁ = n₁ ∧ n₃} $ ⊙.complete ∈p₂ ∈p₃

  helper₂ : p₁ ⊙ p₃ ∣ p₂ ⊙ p₃ ≤ (p₁ ∣ p₂) ⊙ p₃
  helper₂ (∣-left ∈⊙) with ⊙.sound n₃ ∈⊙
  ... | ∈p₁ ⊙′ ∈p₃ = ⊙.complete (∣-left ∈p₁) ∈p₃
  helper₂ (∣-right ∈⊙) with ⊙.sound n₃ ∈⊙
  ... | ∈p₂ ⊙′ ∈p₃ = ⊙.complete (∣-right {n₁ = n₁} ∈p₂) ∈p₃

-- Zero.

left-zero : ∀ {n} (p : P n) → fail ⊙ p ≈ fail
left-zero {n} p = equivalence helper (λ ())
  where
  helper : fail ⊙ p ≤ fail
  helper ∈fail⊙ with ⊙.sound n ∈fail⊙
  ... | () ⊙′ _

right-zero : ∀ {n} (p : P n) → p ⊙ fail ≈ fail
right-zero {n} p = equivalence helper (λ ())
  where
  helper : p ⊙ fail ≤ fail
  helper ∈⊙fail with ⊙.sound false ∈⊙fail
  ... | _ ⊙′ ()

-- *-continuity.

*-continuity-upper-bound :
  ∀ {n₁ n₂ n₃} (p₁ : P n₁) (p₂ : P n₂) (p₃ : P n₃) →
  ∀ i → p₁ ⊙ p₂ ^ i ⊙ p₃ ≤ p₁ ⊙ p₂ ⋆ ⊙ p₃
*-continuity-upper-bound {n₁} {n₂} {n₃} _ _ _ i ∈⊙ⁱ⊙
  with ⊙.sound n₃ ∈⊙ⁱ⊙
... | ∈⊙ⁱ ⊙′ ∈p₃ with ⊙.sound ⟨ n₂ ^ i ⟩-nullable ∈⊙ⁱ
...   | ∈p₁ ⊙′ ∈p₂ⁱ = ⊙.complete (⊙.complete ∈p₁ (^≤⋆ i ∈p₂ⁱ)) ∈p₃

*-continuity-least-upper-bound :
  ∀ {n₁ n₂ n₃ n} (p₁ : P n₁) (p₂ : P n₂) (p₃ : P n₃) (p : P n) →
  (∀ i → p₁ ⊙ p₂ ^ i ⊙ p₃ ≤ p) → p₁ ⊙ p₂ ⋆ ⊙ p₃ ≤ p
*-continuity-least-upper-bound {n₁} {n₂} {n₃} {n} p₁ p₂ p₃ p ub =
  helper ∘ _⟨$⟩_ (Eq.Equivalence.from $ ·-associative p₁ (p₂ ⋆) p₃)
  where
  helper : p₁ ⊙ (p₂ ⋆ ⊙ p₃) ≤ p
  helper ∈⊙⋆⊙ with ⊙.sound (true ∧ n₃) ∈⊙⋆⊙
  ... | _⊙′_ {s₁ = s₁} ∈p₁ ∈⋆⊙ with ⊙.sound n₃ ∈⋆⊙
  ...   | ∈p₂⋆ ⊙′ ∈p₃ with ⋆≤^ ∈p₂⋆
  ...     | (i , ∈p₂ⁱ) =
    cast∈ (ListMonoid.assoc s₁ _ _) refl $
      ub i $ ⊙.complete (⊙.complete ∈p₁ ∈p₂ⁱ) ∈p₃
