------------------------------------------------------------------------
-- Various parser combinator laws
------------------------------------------------------------------------

-- Note that terms like "monad" and "Kleene algebra" are interpreted
-- liberally in the modules listed below.

module TotalParserCombinators.Laws where

open import Algebra
open import Category.Monad
open import Coinduction
open import Data.List as List
import Data.List.Any as Any
import Data.List.Any.BagAndSetEquality as Eq
open import Data.Maybe
open import Function
import Level
open import Relation.Binary.PropositionalEquality as P using (_≡_)

open Any.Membership-≡ using (bag) renaming (_≈[_]_ to _List-≈[_]_)
private
  module BagMonoid {k} {A : Set} =
    CommutativeMonoid (Eq.commutativeMonoid k A)
  open module ListMonad = RawMonad {f = Level.zero} List.monad
    using () renaming (_⊛_ to _⊛′_)

open import TotalParserCombinators.Derivative using (D)
open import TotalParserCombinators.Congruence
  hiding (return; fail; token)
open import TotalParserCombinators.Lib hiding (module Return⋆)
open import TotalParserCombinators.Parser

------------------------------------------------------------------------
-- Reexported modules

-- Laws related to _∣_.

import TotalParserCombinators.Laws.AdditiveMonoid
module AdditiveMonoid = TotalParserCombinators.Laws.AdditiveMonoid

-- Laws related to D.

import TotalParserCombinators.Laws.Derivative
module D = TotalParserCombinators.Laws.Derivative
  hiding (left-zero-⊛; right-zero-⊛;
          left-zero->>=; right-zero->>=)

-- Laws related to return⋆.

import TotalParserCombinators.Laws.ReturnStar
module Return⋆ = TotalParserCombinators.Laws.ReturnStar

-- Laws related to _⊛_.

import TotalParserCombinators.Laws.ApplicativeFunctor
module ApplicativeFunctor =
  TotalParserCombinators.Laws.ApplicativeFunctor

-- Laws related to _>>=_.

import TotalParserCombinators.Laws.Monad
module Monad = TotalParserCombinators.Laws.Monad

-- Do the parser combinators form a Kleene algebra?

import TotalParserCombinators.Laws.KleeneAlgebra
module KleeneAlgebra = TotalParserCombinators.Laws.KleeneAlgebra

------------------------------------------------------------------------
-- Some laws for _<$>_

module <$> where

  open D

  -- _<$>_ could have been defined using return and _⊛_.

  return-⊛ : ∀ {Tok R₁ R₂ xs} {f : R₁ → R₂} (p : Parser Tok R₁ xs) →
             f <$> p ≅P return f ⊛ p
  return-⊛ {xs = xs} {f} p =
    BagMonoid.reflexive (lemma xs) ∷ λ t → ♯ (
      f <$> D t p         ≅⟨ return-⊛ (D t p) ⟩
      return f ⊛ D t p    ≅⟨ sym $ D-return-⊛ f p ⟩
      D t (return f ⊛ p)  ∎)
    where
    lemma : ∀ xs → List.map f xs ≡ [ f ] ⊛′ xs
    lemma []       = P.refl
    lemma (x ∷ xs) = P.cong (_∷_ (f x)) $ lemma xs

  -- fail is a zero for _<$>_.

  zero : ∀ {Tok R₁ R₂} {f : R₁ → R₂} →
         f <$> fail {Tok = Tok} ≅P fail
  zero {f = f} =
    f <$> fail       ≅⟨ return-⊛ fail ⟩
    return f ⊛ fail  ≅⟨ ApplicativeFunctor.right-zero (return f) ⟩
    fail             ∎

  -- A variant of ApplicativeFunctor.homomorphism.

  homomorphism : ∀ {Tok R₁ R₂} (f : R₁ → R₂) {x} →
                 f <$> return {Tok = Tok} x ≅P return (f x)
  homomorphism f {x} =
    f <$> return x       ≅⟨ return-⊛ {f = f} (return x) ⟩
    return f ⊛ return x  ≅⟨ ApplicativeFunctor.homomorphism f x ⟩
    return (f x)         ∎

------------------------------------------------------------------------
-- A law for nonempty

module Nonempty where

  -- fail is a zero for nonempty.

  zero : ∀ {Tok R} → nonempty {Tok = Tok} {R = R} fail ≅P fail
  zero = BagMonoid.refl ∷ λ t → ♯ (fail ∎)

  -- nonempty can be defined in terms of token, _>>=_ and D.

  private

    nonempty′ : ∀ {Tok R xs} (p : Parser Tok R xs) → Parser Tok R []
    nonempty′ p = token >>= λ t → D t p

  nonempty-definable : ∀ {Tok R xs} (p : Parser Tok R xs) →
                       nonempty p ≅P nonempty′ p
  nonempty-definable p = BagMonoid.refl ∷ λ t → ♯ (
    D t p              ≅⟨ sym $ Monad.left-identity t (λ t′ → D t′ p) ⟩
    ret-D t            ≅⟨ sym $ AdditiveMonoid.right-identity (ret-D t) ⟩
    ret-D t ∣ fail     ≅⟨ (ret-D t ∎) ∣ sym (Monad.left-zero _) ⟩
    D t (nonempty′ p)  ∎)
    where ret-D = λ (t : _) → return t >>= (λ t′ → D t′ p)

------------------------------------------------------------------------
-- A law for cast

module Cast where

  -- Casts can be erased.

  correct : ∀ {Tok R xs₁ xs₂}
              {xs₁≈xs₂ : xs₁ List-≈[ bag ] xs₂}
              {p : Parser Tok R xs₁} →
            cast xs₁≈xs₂ p ≅P p
  correct {xs₁≈xs₂ = xs₁≈xs₂} {p} =
    BagMonoid.sym xs₁≈xs₂ ∷ λ t → ♯ (D t p ∎)

------------------------------------------------------------------------
-- A law for subst

module Subst where

  -- Uses of subst can be erased.

  correct : ∀ {Tok R xs₁ xs₂}
              (xs₁≡xs₂ : xs₁ ≡ xs₂)
              {p : Parser Tok R xs₁} →
            P.subst (Parser Tok R) xs₁≡xs₂ p ≅P p
  correct P.refl {p} = p ∎

  correct∞ : ∀ {Tok R xs₁ xs₂ A} {m : Maybe A}
              (xs₁≡xs₂ : xs₁ ≡ xs₂)
              (p : ∞⟨ m ⟩Parser Tok R xs₁) →
             ♭? (P.subst (∞⟨ m ⟩Parser Tok R) xs₁≡xs₂ p) ≅P ♭? p
  correct∞ P.refl p = ♭? p ∎
