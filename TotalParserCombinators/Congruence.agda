------------------------------------------------------------------------
-- A language of parser equivalence proofs
------------------------------------------------------------------------

-- This module defines yet another equivalence relation for parsers.
-- This relation is an equality (a congruential equivalence relation)
-- by construction, and it is sound and complete with respect to the
-- previously defined equivalences (see
-- TotalParserCombinators.Congruence.Sound for the soundness proof).
-- This means that parser and language equivalence are also
-- equalities.

module TotalParserCombinators.Congruence where

open import Coinduction
open import Data.List
import Data.List.Any as Any
open import Data.Maybe
open import Function
open import Relation.Binary.PropositionalEquality using (_≡_; _≗_)

open Any.Membership-≡ using (bag) renaming (_≈[_]_ to _List-≈[_]_)

open import TotalParserCombinators.BreadthFirst.Derivative
open import TotalParserCombinators.CoinductiveEquality as CE
  using (_≈[_]c_; _∷_)
open import TotalParserCombinators.Lib
open import TotalParserCombinators.Parser
open import TotalParserCombinators.Semantics

infixl 50 [_-_-_-_]_⊛_ _<$>_
infix  10 [_-_-_-_]_>>=_
infixl  5 _∣_
infix   5 _∷_
infix   4 _≈[_]P_ ∞⟨_-_⟩_≈[_]P_ _≅P_ _≈P_
infix   2 _∎
infixr  2 _≈⟨_⟩_ _≅⟨_⟩_

------------------------------------------------------------------------
-- Equivalence proof programs

mutual

  _≅P_ : ∀ {Tok R xs₁ xs₂} → Parser Tok R xs₁ → Parser Tok R xs₂ → Set₁
  p₁ ≅P p₂ = p₁ ≈[ parser ]P p₂

  _≈P_ : ∀ {Tok R xs₁ xs₂} → Parser Tok R xs₁ → Parser Tok R xs₂ → Set₁
  p₁ ≈P p₂ = p₁ ≈[ language ]P p₂

  data _≈[_]P_ {Tok} :
         ∀ {R xs₁ xs₂} →
         Parser Tok R xs₁ → Kind → Parser Tok R xs₂ → Set₁ where

    -- This constructor, which corresponds to CE._∷_, ensures that the
    -- relation is complete.

    _∷_ : ∀ {k R xs₁ xs₂}
            {p₁ : Parser Tok R xs₁}
            {p₂ : Parser Tok R xs₂}
          (xs₁≈xs₂ : xs₁ List-≈[ k ] xs₂)
          (Dp₁≈Dp₂ : ∀ t → ∞ (D t p₁ ≈[ k ]P D t p₂)) →
          p₁ ≈[ k ]P p₂

    -- Equational reasoning.

    _∎     : ∀ {k R xs} (p : Parser Tok R xs) → p ≈[ k ]P p

    _≈⟨_⟩_ : ∀ {k R xs₁ xs₂ xs₃}
               (p₁ : Parser Tok R xs₁)
               {p₂ : Parser Tok R xs₂}
               {p₃ : Parser Tok R xs₃}
             (p₁≈p₂ : p₁ ≈[ k ]P p₂) (p₂≈p₃ : p₂ ≈[ k ]P p₃) →
             p₁ ≈[ k ]P p₃

    _≅⟨_⟩_ : ∀ {k R xs₁ xs₂ xs₃}
               (p₁ : Parser Tok R xs₁)
               {p₂ : Parser Tok R xs₂}
               {p₃ : Parser Tok R xs₃}
             (p₁≅p₂ : p₁ ≅P p₂) (p₂≈p₃ : p₂ ≈[ k ]P p₃) →
             p₁ ≈[ k ]P p₃

    sym : ∀ {k R xs₁ xs₂}
            {p₁ : Parser Tok R xs₁}
            {p₂ : Parser Tok R xs₂}
          (p₁≈p₂ : p₁ ≈[ k ]P p₂) → p₂ ≈[ k ]P p₁

    -- Congruences.

    return : ∀ {k R} {x₁ x₂ : R}
             (x₁≡x₂ : x₁ ≡ x₂) → return x₁ ≈[ k ]P return x₂

    fail : ∀ {k R} → fail {R = R} ≈[ k ]P fail {R = R}

    token : ∀ {k} → token ≈[ k ]P token

    _∣_ : ∀ {k R xs₁ xs₂ xs₃ xs₄}
            {p₁ : Parser Tok R xs₁}
            {p₂ : Parser Tok R xs₂}
            {p₃ : Parser Tok R xs₃}
            {p₄ : Parser Tok R xs₄}
          (p₁≈p₃ : p₁ ≈[ k ]P p₃) (p₂≈p₄ : p₂ ≈[ k ]P p₄) →
          p₁ ∣ p₂ ≈[ k ]P p₃ ∣ p₄

    _<$>_ : ∀ {k R₁ R₂} {f₁ f₂ : R₁ → R₂} {xs₁ xs₂}
              {p₁ : Parser Tok R₁ xs₁}
              {p₂ : Parser Tok R₁ xs₂}
            (f₁≗f₂ : f₁ ≗ f₂) (p₁≈p₂ : p₁ ≈[ k ]P p₂) →
            f₁ <$> p₁ ≈[ k ]P f₂ <$> p₂

    [_-_-_-_]_⊛_ :
      ∀ {k R₁ R₂} xs₁ xs₂ fs₁ fs₂
        {p₁ : ∞⟨ xs₁ ⟩Parser Tok (R₁ → R₂) (flatten fs₁)}
        {p₂ : ∞⟨ fs₁ ⟩Parser Tok  R₁       (flatten xs₁)}
        {p₃ : ∞⟨ xs₂ ⟩Parser Tok (R₁ → R₂) (flatten fs₂)}
        {p₄ : ∞⟨ fs₂ ⟩Parser Tok  R₁       (flatten xs₂)}
      (p₁≈p₃ : ∞⟨ xs₁ - xs₂ ⟩ p₁ ≈[ k ]P p₃)
      (p₂≈p₄ : ∞⟨ fs₁ - fs₂ ⟩ p₂ ≈[ k ]P p₄) →
      p₁ ⊛ p₂ ≈[ k ]P p₃ ⊛ p₄

    [_-_-_-_]_>>=_ :
      ∀ {k R₁ R₂} (f₁ f₂ : Maybe (R₁ → List R₂)) xs₁ xs₂
        {p₁ : ∞⟨ f₁ ⟩Parser Tok R₁ (flatten xs₁)}
        {p₂ : (x : R₁) → ∞⟨ xs₁ ⟩Parser Tok R₂ (apply f₁ x)}
        {p₃ : ∞⟨ f₂ ⟩Parser Tok R₁ (flatten xs₂)}
        {p₄ : (x : R₁) → ∞⟨ xs₂ ⟩Parser Tok R₂ (apply f₂ x)}
      (p₁≈p₃ : ∞⟨ f₁ - f₂ ⟩ p₁ ≈[ k ]P p₃)
      (p₂≈p₄ : ∀ x → ∞⟨ xs₁ - xs₂ ⟩ p₂ x ≈[ k ]P p₄ x) →
      p₁ >>= p₂ ≈[ k ]P p₃ >>= p₄

    nonempty : ∀ {k R xs₁ xs₂}
                 {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂}
               (p₁≈p₂ : p₁ ≈[ k ]P p₂) → nonempty p₁ ≈[ k ]P nonempty p₂

    cast : ∀ {k R xs₁ xs₂ xs₁′ xs₂′}
             {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂}
             {xs₁≈xs₁′ : xs₁ List-≈[ bag ] xs₁′}
             {xs₂≈xs₂′ : xs₂ List-≈[ bag ] xs₂′}
           (p₁≈p₂ : p₁ ≈[ k ]P p₂) →
           cast xs₁≈xs₁′ p₁ ≈[ k ]P cast xs₂≈xs₂′ p₂

  -- Certain proofs are coinductive if both sides are delayed.

  ∞⟨_-_⟩_≈[_]P_ :
    ∀ {Tok R xs₁ xs₂} {A : Set} (m₁ m₂ : Maybe A) →
    ∞⟨ m₁ ⟩Parser Tok R xs₁ → Kind → ∞⟨ m₂ ⟩Parser Tok R xs₂ → Set₁
  ∞⟨ nothing - nothing ⟩ p₁ ≈[ k ]P p₂ = ∞ (♭  p₁ ≈[ k ]P ♭  p₂)
  ∞⟨ _       - _       ⟩ p₁ ≈[ k ]P p₂ =    ♭? p₁ ≈[ k ]P ♭? p₂

------------------------------------------------------------------------
-- Completeness

complete : ∀ {k Tok R xs₁ xs₂}
             {p₁ : Parser Tok R xs₁}
             {p₂ : Parser Tok R xs₂} →
           p₁ ≈[ k ] p₂ → p₁ ≈[ k ]P p₂
complete = complete′ ∘ CE.complete
  where
  complete′ : ∀ {k Tok R xs₁ xs₂}
                {p₁ : Parser Tok R xs₁}
                {p₂ : Parser Tok R xs₂} →
              p₁ ≈[ k ]c p₂ → p₁ ≈[ k ]P p₂
  complete′ (xs₁≈xs₂ ∷ Dp₁≈Dp₂) =
    xs₁≈xs₂ ∷ λ t → ♯ complete′ (♭ (Dp₁≈Dp₂ t))
