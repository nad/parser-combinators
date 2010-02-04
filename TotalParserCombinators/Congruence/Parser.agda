------------------------------------------------------------------------
-- A language of parser equivalence proofs
------------------------------------------------------------------------

-- This module defines yet another equivalence relation for parsers.
-- This relation is an equality (a congruential equivalence relation)
-- by construction, and it is sound and complete with respect to
-- parser equivalence (see
-- TotalParserCombinators.Congruence.Parser.Sound for the soundness
-- proof). This means that parser equivalence is also an equality.

module TotalParserCombinators.Congruence.Parser where

open import Coinduction
open import Data.List
import Data.List.Any as Any
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; _≗_)

private
  open module BagS {A : Set} =
    Setoid (Any.Membership-≡.Bag-equality {A})
      using () renaming (_≈_ to _Bag-≈_)

open import TotalParserCombinators.BreadthFirst hiding (complete)
open import TotalParserCombinators.Coinduction
open import TotalParserCombinators.CoinductiveEquality
open import TotalParserCombinators.Lib
open import TotalParserCombinators.Parser
open import TotalParserCombinators.Semantics

infixl 50 _⊛_ _⊙′_ _<$>_
infixl 10 _>>=_ _≫=′_ _>>=!_
infixl  5 _∣_
infix   5 _∷_
infix   4 _≅P_
infix   2 _∎
infixr  2 _≅⟨_⟩_

-- Equivalence proof programs.

data _≅P_ {Tok} : ∀ {R xs₁ xs₂} →
                  Parser Tok R xs₁ → Parser Tok R xs₂ → Set₁ where

  -- The only coinductive constructor.

  _∷_ : ∀ {R xs₁ xs₂}
          {p₁ : Parser Tok R xs₁}
          {p₂ : Parser Tok R xs₂}
        (xs₁≈xs₂ : xs₁ Bag-≈ xs₂)
        (∂p₁≅∂p₂ : ∀ t → ∞ (∂ p₁ t ≅P ∂ p₂ t)) →
        p₁ ≅P p₂

  -- Equational reasoning.

  _∎     : ∀ {R xs} (p : Parser Tok R xs) → p ≅P p

  _≅⟨_⟩_ : ∀ {R xs₁ xs₂ xs₃}
             (p₁ : Parser Tok R xs₁)
             {p₂ : Parser Tok R xs₂}
             {p₃ : Parser Tok R xs₃}
           (p₁≅p₂ : p₁ ≅P p₂) (p₂≅p₃ : p₂ ≅P p₃) → p₁ ≅P p₃

  sym : ∀ {R xs₁ xs₂}
          {p₁ : Parser Tok R xs₁}
          {p₂ : Parser Tok R xs₂}
        (p₁≅p₂ : p₁ ≅P p₂) → p₂ ≅P p₁

  -- Congruences.

  ♭♯ : ∀ {R R₁ R₂ xs₁ xs₂} (ys₁ : List R₁) (ys₂ : List R₂)
         {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂}
       (p₁≅p₂ : p₁ ≅P p₂) →
       ♭? (♯? {xs = ys₁} p₁) ≅P ♭? (♯? {xs = ys₂} p₂)

  return : ∀ {R} {x₁ x₂ : R}
           (x₁≡x₂ : x₁ ≡ x₂) → return x₁ ≅P return x₂

  fail : ∀ {R} → fail {R = R} ≅P fail {R = R}

  token : token ≅P token

  _∣_ : ∀ {R xs₁ xs₂ xs₃ xs₄}
          {p₁ : Parser Tok R xs₁}
          {p₂ : Parser Tok R xs₂}
          {p₃ : Parser Tok R xs₃}
          {p₄ : Parser Tok R xs₄}
        (p₁≅p₃ : p₁ ≅P p₃) (p₂≅p₄ : p₂ ≅P p₄) → p₁ ∣ p₂ ≅P p₃ ∣ p₄

  _<$>_ : ∀ {R₁ R₂} {f₁ f₂ : R₁ → R₂} {xs₁ xs₂}
            {p₁ : Parser Tok R₁ xs₁}
            {p₂ : Parser Tok R₁ xs₂}
          (f₁≗f₂ : f₁ ≗ f₂) (p₁≅p₂ : p₁ ≅P p₂) →
          f₁ <$> p₁ ≅P f₂ <$> p₂

  _⊛_ : ∀ {R₁ R₂ xs₁ xs₂ xs₃ xs₄}
          {p₁ : ∞? (Parser Tok (R₁ → R₂) xs₁) xs₂}
          {p₂ : ∞? (Parser Tok R₁        xs₂) xs₁}
          {p₃ : ∞? (Parser Tok (R₁ → R₂) xs₃) xs₄}
          {p₄ : ∞? (Parser Tok R₁        xs₄) xs₃}
        (p₁≅p₃ : ♭? p₁ ≅P ♭? p₃) (p₂≅p₄ : ♭? p₂ ≅P ♭? p₄) →
        p₁ ⊛ p₂ ≅P p₃ ⊛ p₄

  _⊙′_ : ∀ {R₁ R₂ xs₁ xs₂ xs₃ xs₄}
           {p₁ : Parser Tok (R₁ → R₂) xs₁}
           {p₂ : Parser Tok R₁        xs₂}
           {p₃ : Parser Tok (R₁ → R₂) xs₃}
           {p₄ : Parser Tok R₁        xs₄}
         (p₁≅p₃ : p₁ ≅P p₃) (p₂≅p₄ : p₂ ≅P p₄) → p₁ ⊙ p₂ ≅P p₃ ⊙ p₄

  _>>=_ : ∀ {R₁ R₂ xs₁ xs₂} {f₁ f₂ : R₁ → List R₂}
            {p₁ : Parser Tok R₁ xs₁}
            {p₂ : (x : R₁) → ∞? (Parser Tok R₂ (f₁ x)) xs₁}
            {p₃ : Parser Tok R₁ xs₂}
            {p₄ : (x : R₁) → ∞? (Parser Tok R₂ (f₂ x)) xs₂}
          (p₁≅p₃ : p₁ ≅P p₃)
          (p₂≅p₄ : ∀ x → ♭? (p₂ x) ≅P ♭? (p₄ x)) →
          p₁ >>= p₂ ≅P p₃ >>= p₄

  _≫=′_ : ∀ {R₁ R₂ xs₁ xs₂} {f₁ f₂ : R₁ → List R₂}
            {p₁ : Parser Tok R₁ xs₁}
            {p₂ : (x : R₁) → Parser Tok R₂ (f₁ x)}
            {p₃ : Parser Tok R₁ xs₂}
            {p₄ : (x : R₁) → Parser Tok R₂ (f₂ x)}
          (p₁≅p₃ : p₁ ≅P p₃) (p₂≅p₄ : ∀ x → p₂ x ≅P p₄ x) →
          p₁ ≫= p₂ ≅P p₃ ≫= p₄

  _>>=!_ : ∀ {R₁ R₂ xs₁ xs₂}
             {p₁ : ∞ (Parser Tok R₁ xs₁)}
             {p₂ : R₁ → ∞? (Parser Tok R₂ []) xs₁}
             {p₃ : ∞ (Parser Tok R₁ xs₂)}
             {p₄ : R₁ → ∞? (Parser Tok R₂ []) xs₂}
           (p₁≅p₃ : ♭ p₁ ≅P ♭ p₃)
           (p₂≅p₄ : ∀ x → ♭? (p₂ x) ≅P ♭? (p₄ x)) →
           p₁ >>=! p₂ ≅P p₃ >>=! p₄

  nonempty : ∀ {R xs₁ xs₂}
               {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂}
             (p₁≅p₂ : p₁ ≅P p₂) → nonempty p₁ ≅P nonempty p₂

  cast : ∀ {R xs₁ xs₂ xs₁′ xs₂′}
           {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂}
           {xs₁≈xs₁′ : xs₁ Bag-≈ xs₁′} {xs₂≈xs₂′ : xs₂ Bag-≈ xs₂′}
         (p₁≅p₂ : p₁ ≅P p₂) → cast xs₁≈xs₁′ p₁ ≅P cast xs₂≈xs₂′ p₂

-- Completeness.

complete : ∀ {Tok R xs₁ xs₂}
             {p₁ : Parser Tok R xs₁}
             {p₂ : Parser Tok R xs₂} →
           p₁ ≅ p₂ → p₁ ≅P p₂
complete = complete′ ∘ ParserEquivalence.complete
  where
  complete′ : ∀ {Tok R xs₁ xs₂}
                {p₁ : Parser Tok R xs₁}
                {p₂ : Parser Tok R xs₂} →
              p₁ ≅′ p₂ → p₁ ≅P p₂
  complete′ (xs₁≈xs₂ ∷ ∂p₁≅∂p₂) =
    xs₁≈xs₂ ∷ λ t → ♯ complete′ (♭ (∂p₁≅∂p₂ t))
