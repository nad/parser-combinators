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

open import TotalParserCombinators.BreadthFirst hiding (complete)
open import TotalParserCombinators.Coinduction
open import TotalParserCombinators.CoinductiveEquality as CE
  using (_≈[_]′_; _∷_)
open import TotalParserCombinators.Lib
open import TotalParserCombinators.Parser
open import TotalParserCombinators.Semantics

infixl 50 _⊛_ _⊙′_ _<$>_
infixl 10 _≫=′_
infix  10 [_,_]_>>=_
infixl  5 _∣_
infix   5 _∷_
infix   4 _≈[_]P_ _≅P_ _≈P_
infix   2 _∎
infixr  2 _≈⟨_⟩_ _≅⟨_⟩_

-- Equivalence proof programs.

mutual

  _≅P_ : ∀ {Tok R xs₁ xs₂} → Parser Tok R xs₁ → Parser Tok R xs₂ → Set₁
  p₁ ≅P p₂ = p₁ ≈[ parser ]P p₂

  _≈P_ : ∀ {Tok R xs₁ xs₂} → Parser Tok R xs₁ → Parser Tok R xs₂ → Set₁
  p₁ ≈P p₂ = p₁ ≈[ language ]P p₂

  data _≈[_]P_ {Tok} :
         ∀ {R xs₁ xs₂} →
         Parser Tok R xs₁ → Kind → Parser Tok R xs₂ → Set₁ where

    -- The only coinductive constructor.

    _∷_ : ∀ {k R xs₁ xs₂}
            {p₁ : Parser Tok R xs₁}
            {p₂ : Parser Tok R xs₂}
          (xs₁≈xs₂ : xs₁ List-≈[ k ] xs₂)
          (∂p₁≈∂p₂ : ∀ t → ∞ (∂ p₁ t ≈[ k ]P ∂ p₂ t)) →
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

    ♭♯ : ∀ {k R R₁ R₂ xs₁ xs₂} (ys₁ : List R₁) (ys₂ : List R₂)
           {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂}
         (p₁≈p₂ : p₁ ≈[ k ]P p₂) →
         ♭? (♯? {n = ys₁} p₁) ≈[ k ]P ♭? (♯? {n = ys₂} p₂)

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

    _⊛_ : ∀ {k R₁ R₂ xs₁ xs₂ xs₃ xs₄}
            {p₁ : ∞? (Parser Tok (R₁ → R₂) xs₁) xs₂}
            {p₂ : ∞? (Parser Tok R₁        xs₂) xs₁}
            {p₃ : ∞? (Parser Tok (R₁ → R₂) xs₃) xs₄}
            {p₄ : ∞? (Parser Tok R₁        xs₄) xs₃}
          (p₁≈p₃ : ♭? p₁ ≈[ k ]P ♭? p₃) (p₂≈p₄ : ♭? p₂ ≈[ k ]P ♭? p₄) →
          p₁ ⊛ p₂ ≈[ k ]P p₃ ⊛ p₄

    _⊙′_ : ∀ {k R₁ R₂ xs₁ xs₂ xs₃ xs₄}
             {p₁ : Parser Tok (R₁ → R₂) xs₁}
             {p₂ : Parser Tok R₁        xs₂}
             {p₃ : Parser Tok (R₁ → R₂) xs₃}
             {p₄ : Parser Tok R₁        xs₄}
           (p₁≈p₃ : p₁ ≈[ k ]P p₃) (p₂≈p₄ : p₂ ≈[ k ]P p₄) →
           p₁ ⊙ p₂ ≈[ k ]P p₃ ⊙ p₄

    [_,_]_>>=_ : ∀ {k R₁ R₂ xs₁ xs₂} {f₁ f₂ : Maybe (R₁ → List R₂)}
                   (p₁ : ∞? (Parser Tok R₁ xs₁) f₁)
                   {p₂ : (x : R₁) → ∞? (Parser Tok R₂ (app f₁ x)) xs₁}
                   (p₃ : ∞? (Parser Tok R₁ xs₂) f₂)
                   {p₄ : (x : R₁) → ∞? (Parser Tok R₂ (app f₂ x)) xs₂}
                 (p₁≈p₃ : ♭? p₁ ≈[ k ]P ♭? p₃)
                 (p₂≈p₄ : ∀ x → ♭? (p₂ x) ≈[ k ]P ♭? (p₄ x)) →
                 p₁ >>= p₂ ≈[ k ]P p₃ >>= p₄

    _≫=′_ : ∀ {k R₁ R₂ xs₁ xs₂} {f₁ f₂ : R₁ → List R₂}
              {p₁ : Parser Tok R₁ xs₁}
              {p₂ : (x : R₁) → Parser Tok R₂ (f₁ x)}
              {p₃ : Parser Tok R₁ xs₂}
              {p₄ : (x : R₁) → Parser Tok R₂ (f₂ x)}
            (p₁≈p₃ : p₁ ≈[ k ]P p₃) (p₂≈p₄ : ∀ x → p₂ x ≈[ k ]P p₄ x) →
            p₁ ≫= p₂ ≈[ k ]P p₃ ≫= p₄

    nonempty : ∀ {k R xs₁ xs₂}
                 {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂}
               (p₁≈p₂ : p₁ ≈[ k ]P p₂) → nonempty p₁ ≈[ k ]P nonempty p₂

    cast : ∀ {k R xs₁ xs₂ xs₁′ xs₂′}
             {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂}
             {xs₁≈xs₁′ : xs₁ List-≈[ bag ] xs₁′}
             {xs₂≈xs₂′ : xs₂ List-≈[ bag ] xs₂′}
           (p₁≈p₂ : p₁ ≈[ k ]P p₂) →
           cast xs₁≈xs₁′ p₁ ≈[ k ]P cast xs₂≈xs₂′ p₂

-- Completeness.

complete : ∀ {k Tok R xs₁ xs₂}
             {p₁ : Parser Tok R xs₁}
             {p₂ : Parser Tok R xs₂} →
           p₁ ≈[ k ] p₂ → p₁ ≈[ k ]P p₂
complete = complete′ ∘ CE.complete
  where
  complete′ : ∀ {k Tok R xs₁ xs₂}
                {p₁ : Parser Tok R xs₁}
                {p₂ : Parser Tok R xs₂} →
              p₁ ≈[ k ]′ p₂ → p₁ ≈[ k ]P p₂
  complete′ (xs₁≈xs₂ ∷ ∂p₁≈∂p₂) =
    xs₁≈xs₂ ∷ λ t → ♯ complete′ (♭ (∂p₁≈∂p₂ t))
