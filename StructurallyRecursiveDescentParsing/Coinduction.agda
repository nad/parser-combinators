------------------------------------------------------------------------
-- Helper functions related to coinduction
------------------------------------------------------------------------

module StructurallyRecursiveDescentParsing.Coinduction where

open import Coinduction
open import Data.Bool
open import Data.List
open import Relation.Binary.PropositionalEquality1

-- Possibly coinductive if the argument list is empty.

data ∞? (A : Set₁) {B : Set} : List B → Set₁ where
  delayed :        (x : ∞₁ A) → ∞? A []
  forced  : ∀ {xs} (x :    A) → ∞? A xs

♯? : ∀ {A B} (xs : List B) → A → ∞? A xs
♯? _ = forced

♭? : ∀ {A B} {xs : List B} → ∞? A xs → A
♭? (delayed x) = ♭₁ x
♭? (forced  x) = x

-- A lemma.

♭?♯? : ∀ {A B} (xs : List B) {x : A} → ♭? (♯? xs x) ≡₁ x
♭?♯? []      = refl
♭?♯? (_ ∷ _) = refl
