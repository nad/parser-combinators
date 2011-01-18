------------------------------------------------------------------------
-- Parsing of matching parentheses, along with a correctness proof
------------------------------------------------------------------------

-- A solution to an exercise set by Helmut Schwichtenberg.

module TotalRecognisers.LeftRecursion.MatchingParentheses where

open import Algebra
open import Coinduction
open import Data.Bool
open import Data.List as List
open import Data.Product
open import Function.Equivalence as Eq
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Relation.Nullary
open import Relation.Nullary.Decidable as Dec

private
  module ListMonoid {A : Set} = Monoid (List.monoid A)

import TotalRecognisers.LeftRecursion as LR
import TotalRecognisers.LeftRecursion.Lib as Lib

-- Parentheses.

data Paren : Set where
  ⟦ ⟧ : Paren

-- Equality of parentheses is decidable.

_≟-Paren_ : Decidable (_≡_ {A = Paren})
⟦ ≟-Paren ⟦ = yes P.refl
⟦ ≟-Paren ⟧ = no λ()
⟧ ≟-Paren ⟦ = no λ()
⟧ ≟-Paren ⟧ = yes P.refl

open LR Paren
private
  open module Tok = Lib.Tok Paren _≟-Paren_ using (tok)

-- Adds surrounding parentheses.

bracket : List Paren → List Paren
bracket xs = [ ⟦ ] ++ xs ++ [ ⟧ ]

-- Strings of matching parentheses.

data Parenthesised : List Paren → Set where
  nil : Parenthesised []
  app : ∀ {xs ys} (p₁ : Parenthesised xs) (p₂ : Parenthesised ys) →
        Parenthesised (xs ++ ys)
  par : ∀ {xs} (p : Parenthesised xs) →
        Parenthesised (bracket xs)

-- Our goal: decide Parenthesised.

Goal : Set
Goal = ∀ xs → Dec (Parenthesised xs)

-- The obvious grammar for parenthesised is cyclic, and my framework
-- cannot handle cyclic grammars, so let us define an alternative
-- axiomatisation instead. (Just as Helmut did in his solution.)

data Parenthesised′ : List Paren → Set where
  nil     : Parenthesised′ []
  app-par : ∀ {xs ys} (p₁ : Parenthesised′ xs) (p₂ : Parenthesised′ ys) →
            Parenthesised′ (xs ++ bracket ys)

-- This axiomatisation is equivalent to the one above.

P⇔P′ : ∀ {xs} → Parenthesised xs ⇔ Parenthesised′ xs
P⇔P′ = equivalent to from
  where
  app′ : ∀ {xs ys} → Parenthesised′ xs → Parenthesised′ ys →
         Parenthesised′ (xs ++ ys)
  app′ {xs = xs} p nil
    rewrite proj₂ ListMonoid.identity xs =
    p
  app′ {xs = xs} p (app-par {xs = ys} {ys = zs} p₁ p₂)
    rewrite P.sym (ListMonoid.assoc xs ys (bracket zs)) =
    app-par (app′ p p₁) p₂

  to : ∀ {xs} → Parenthesised xs → Parenthesised′ xs
  to nil         = nil
  to (app p₁ p₂) = app′ (to p₁) (to p₂)
  to (par p)     = app-par nil (to p)

  from : ∀ {xs} → Parenthesised′ xs → Parenthesised xs
  from nil             = nil
  from (app-par p₁ p₂) = app (from p₁) (par (from p₂))

-- A (left recursive) grammar for matching parentheses.

parenthesised : P _
parenthesised =
    empty
  ∣ ♯ parenthesised · (♯ (tok ⟦ · ♯ parenthesised) · ♯ tok ⟧)

-- We can decide membership of parenthesised.

decide-parenthesised : ∀ xs → Dec (xs ∈ parenthesised)
decide-parenthesised xs = xs ∈? parenthesised

-- Membership of parenthesised is equivalent to satisfaction of
-- Parenthesised′.

∈p⇔P′ : ∀ {xs} → (xs ∈ parenthesised) ⇔ Parenthesised′ xs
∈p⇔P′ = equivalent to from
  where
  to : ∀ {xs} → xs ∈ parenthesised → Parenthesised′ xs
  to (∣-left empty)                  = nil
  to (∣-right (p₁ · (⟦∈ · p₂ · ⟧∈)))
    rewrite Tok.sound ⟦∈ | Tok.sound ⟧∈ =
    app-par (to p₁) (to p₂)

  from : ∀ {xs} → Parenthesised′ xs → xs ∈ parenthesised
  from nil             = ∣-left empty
  from (app-par p₁ p₂) =
    ∣-right {n₁ = true}
      (from p₁ · (Tok.complete · from p₂ · Tok.complete))

-- And thus we reach our goal.

goal : Goal
goal xs = Dec.map (Eq.sym P⇔P′ ∘ ∈p⇔P′) (decide-parenthesised xs)

-- Some examples.

ex₁ : Dec (Parenthesised [])
ex₁ = goal _ -- = yes nil

ex₂ : Dec (Parenthesised (⟦ ∷ ⟧ ∷ []))
ex₂ = goal _ -- = yes (app nil (par nil))

ex₃ : Dec (Parenthesised (⟦ ∷ ⟧ ∷ ⟦ ∷ ⟧ ∷ []))
ex₃ = goal _ -- = yes (app (app nil (par nil)) (par nil))

ex₄ : Dec (Parenthesised (⟦ ∷ ⟧ ∷ ⟦ ∷ []))
ex₄ = goal _ -- = no (λ x → …)
