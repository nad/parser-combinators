------------------------------------------------------------------------
-- Asymmetric choice
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

module TotalParserCombinators.AsymmetricChoice where

open import Data.Empty
open import Data.List
open import Data.List.Any as Any using (here)
open import Data.Product
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence using (module Equivalent)
open import Function.Inverse as Inv using (_⇿_)
open import Function.Inverse.TypeIsomorphisms
import Relation.Binary.PropositionalEquality as P
import Relation.Binary.Sigma.Pointwise as Σ

open Any.Membership-≡ using (_∈_) renaming (_≈[_]_ to _List-≈[_]_)

open import TotalParserCombinators.BreadthFirst
open import TotalParserCombinators.Congruence using (_≈[_]P_; _≅P_)
open import TotalParserCombinators.Parser
import TotalParserCombinators.Pointwise as Pointwise
open import TotalParserCombinators.Semantics using (_∈_·_)

------------------------------------------------------------------------
-- An initial bag operator

-- first-nonempty returns the left-most non-empty initial bag, if any.

first-nonempty : {R : Set} → List R → List R → List R
first-nonempty [] ys = ys
first-nonempty xs ys = xs

-- first-nonempty preserves equality.

first-nonempty-cong :
  ∀ {k R} {xs₁ xs₁′ xs₂ xs₂′ : List R} →
  xs₁ List-≈[ k ] xs₁′ → xs₂ List-≈[ k ] xs₂′ →
  first-nonempty xs₁ xs₂ List-≈[ k ] first-nonempty xs₁′ xs₂′
first-nonempty-cong {xs₁ = []}    {[]}    eq₁ eq₂ = eq₂
first-nonempty-cong {xs₁ = _ ∷ _} {_ ∷ _} eq₁ eq₂ = eq₁
first-nonempty-cong {xs₁ = []} {_ ∷ _} eq₁ eq₂
  with Equivalent.from (Inv.⇒⇔ eq₁) ⟨$⟩ here P.refl
... | ()
first-nonempty-cong {xs₁ = _ ∷ _} {[]} eq₁ eq₂
  with Equivalent.to (Inv.⇒⇔ eq₁) ⟨$⟩ here P.refl
... | ()

-- first-nonempty is correct.

first-nonempty-left :
  ∀ {k R} {xs₁ xs₂ : List R} →
  (∃ λ y → y ∈ xs₁) → first-nonempty xs₁ xs₂ List-≈[ k ] xs₁
first-nonempty-left {xs₁ = []}    (_ , ())
first-nonempty-left {xs₁ = _ ∷ _} _        = _ ∎
  where open Inv.EquationalReasoning

first-nonempty-right :
  ∀ {k R} {xs₁ xs₂ : List R} →
  (∄ λ y → y ∈ xs₁) → first-nonempty xs₁ xs₂ List-≈[ k ] xs₂
first-nonempty-right {xs₁ = x ∷ _} ∉x∷ = ⊥-elim $ ∉x∷ (x , here P.refl)
first-nonempty-right {xs₁ = []}    _   = _ ∎
  where open Inv.EquationalReasoning

------------------------------------------------------------------------
-- Asymmetric choice

-- _◃_ is defined as a pointwise lifting of first-nonempty.

private
  module AC {R} = Pointwise R R first-nonempty first-nonempty-cong

-- p₁ ◃ p₂ returns a result if either p₁ or p₂ does. For a given
-- string results are returned either from p₁ or from p₂, not both.

infixl 5 _◃_ _◃-cong_

_◃_ : ∀ {Tok R xs₁ xs₂} →
      Parser Tok R xs₁ → Parser Tok R xs₂ →
      Parser Tok R (first-nonempty xs₁ xs₂)
_◃_ = AC.lift

-- D distributes over _◃_.

D-◃ : ∀ {Tok R xs₁ xs₂ t}
      (p₁ : Parser Tok R xs₁) (p₂ : Parser Tok R xs₂) →
      D t (p₁ ◃ p₂) ≅P D t p₁ ◃ D t p₂
D-◃ = AC.D-lift

-- _◃_ preserves equality.

_◃-cong_ : ∀ {k Tok R xs₁ xs₁′ xs₂ xs₂′}
             {p₁  : Parser Tok R xs₁} {p₁′ : Parser Tok R xs₁′}
             {p₂  : Parser Tok R xs₂} {p₂′ : Parser Tok R xs₂′} →
           p₁ ≈[ k ]P p₁′ → p₂ ≈[ k ]P p₂′ → p₁ ◃ p₂ ≈[ k ]P p₁′ ◃ p₂′
_◃-cong_ = AC.lift-cong

-- If p₁ accepts s, then p₁ ◃ p₂ behaves as p₁ when applied to s.

left : ∀ {Tok R xs₁ xs₂ x s}
       (p₁ : Parser Tok R xs₁) (p₂ : Parser Tok R xs₂) →
       (∃ λ y → y ∈ p₁ · s) → x ∈ p₁ ◃ p₂ · s ⇿ x ∈ p₁ · s
left {x = x} =
  AC.lift-property
    (λ F _ H → ∃ F → H x ⇿ F x)
    (λ F⇿F′ _ H⇿H′ →
       Σ.cong (λ {x} → Inv.⇿⇒ (F⇿F′ x))
         →-cong-⇔
       Isomorphism-cong (H⇿H′ x) (F⇿F′ x))
    (λ ∈xs₁ → first-nonempty-left ∈xs₁)

-- If p₁ does not accept s, then p₁ ◃ p₂ behaves as p₂ when applied to
-- s.

right : ∀ {Tok R xs₁ xs₂ x s}
        (p₁ : Parser Tok R xs₁) (p₂ : Parser Tok R xs₂) →
        (∄ λ y → y ∈ p₁ · s) → x ∈ p₁ ◃ p₂ · s ⇿ x ∈ p₂ · s
right {x = x} =
  AC.lift-property
    (λ F G H → ∄ F → H x ⇿ G x)
    (λ F⇿F′ G⇿G′ H⇿H′ →
       ¬-cong-⇔ (Σ.cong λ {x} → Inv.⇿⇒ (F⇿F′ x))
         →-cong-⇔
       Isomorphism-cong (H⇿H′ x) (G⇿G′ x))
    (λ ∉xs₁ → first-nonempty-right ∉xs₁)
