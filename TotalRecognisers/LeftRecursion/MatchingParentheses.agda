------------------------------------------------------------------------
-- Parsing of matching parentheses, along with a correctness proof
------------------------------------------------------------------------

-- A solution to an exercise set by Helmut Schwichtenberg.

module TotalRecognisers.LeftRecursion.MatchingParentheses where

open import Algebra
open import Coinduction
open import Data.Bool
open import Data.List
open import Data.List.Properties
open import Data.Product
open import Function.Equivalence
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Relation.Nullary
open import Relation.Nullary.Decidable as Decidable

private
  module ListMonoid {A : Set} = Monoid (++-monoid A)

import TotalRecognisers.LeftRecursion as LR
import TotalRecognisers.LeftRecursion.Lib as Lib

-- Parentheses.

data Paren : Set where
  ⟦ ⟧ : Paren

-- Strings of matching parentheses.

data Matching : List Paren → Set where
  nil : Matching []
  app : ∀ {xs ys}
        (p₁ : Matching xs) (p₂ : Matching ys) → Matching (xs ++ ys)
  par : ∀ {xs} (p : Matching xs) → Matching ([ ⟦ ] ++ xs ++ [ ⟧ ])

-- Our goal: decide Matching.

Goal : Set
Goal = ∀ xs → Dec (Matching xs)

-- Equality of parentheses is decidable.

_≟-Paren_ : Decidable (_≡_ {A = Paren})
⟦ ≟-Paren ⟦ = yes P.refl
⟦ ≟-Paren ⟧ = no λ()
⟧ ≟-Paren ⟦ = no λ()
⟧ ≟-Paren ⟧ = yes P.refl

open LR Paren hiding (_∷_)
private
  open module Tok = Lib.Tok Paren _≟-Paren_ using (tok)

-- A (left and right recursive) grammar for matching parentheses. Note
-- the use of nonempty; without the two occurrences of nonempty the
-- grammar would not be well-formed.

matching : P _
matching =
    empty
  ∣ ♯ nonempty matching · ♯ nonempty matching
  ∣ ♯ (tok ⟦ · ♯ matching) · ♯ tok ⟧

-- We can decide membership of matching.

decide-matching : ∀ xs → Dec (xs ∈ matching)
decide-matching xs = xs ∈? matching

-- Membership of matching is equivalent to satisfaction of Matching.

∈m⇔M : ∀ {xs} → (xs ∈ matching) ⇔ Matching xs
∈m⇔M = equivalence to from
  where
  to : ∀ {xs} → xs ∈ matching → Matching xs
  to (∣-left (∣-left empty))                        = nil
  to (∣-left (∣-right (nonempty p₁ · nonempty p₂))) = app (to p₁) (to p₂)
  to (∣-right (⟦∈ · p · ⟧∈))
    rewrite Tok.sound ⟦∈ | Tok.sound ⟧∈             = par (to p)

  from : ∀ {xs} → Matching xs → xs ∈ matching
  from nil                                    = ∣-left (∣-left empty)
  from (app {xs = []}                  p₁ p₂) = from p₂
  from (app {xs = x ∷ xs} {ys = []}    p₁ p₂) rewrite proj₂ ListMonoid.identity xs = from p₁
  from (app {xs = _ ∷ _}  {ys = _ ∷ _} p₁ p₂) = ∣-left (∣-right {n₁ = true} (nonempty (from p₁) · nonempty (from p₂)))
  from (par p)                                = ∣-right {n₁ = true} (Tok.complete · from p · Tok.complete)

-- And thus we reach our goal.

goal : Goal
goal xs = Decidable.map ∈m⇔M (decide-matching xs)

-- Some examples.

ex₁ : Dec (Matching [])
ex₁ = goal _ -- = yes nil

ex₂ : Dec (Matching (⟦ ∷ ⟧ ∷ []))
ex₂ = goal _ -- = yes (par nil)

ex₃ : Dec (Matching (⟦ ∷ ⟧ ∷ ⟦ ∷ ⟧ ∷ []))
ex₃ = goal _ -- = yes (app (par nil) (par nil))

ex₄ : Dec (Matching (⟦ ∷ ⟧ ∷ ⟦ ∷ []))
ex₄ = goal _ -- = no (λ x → …)
