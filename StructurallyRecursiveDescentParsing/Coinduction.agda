------------------------------------------------------------------------
-- Helper functions related to coinduction
------------------------------------------------------------------------

module StructurallyRecursiveDescentParsing.Coinduction where

open import Coinduction
open import Data.Bool
open import Relation.Binary.PropositionalEquality1

-- Coinductive if the argument is true.

∞? : Bool → Set1 → Set1
∞? true  A = ∞₁ A
∞? false A =    A

♯? : ∀ b {A} → A → ∞? b A
♯? true  x = ♯₁ x
♯? false x =    x

♭? : ∀ b {A} → ∞? b A → A
♭? true  x = ♭₁ x
♭? false x =    x

-- Some lemmas.

♭?♯? : ∀ b {A} {x : A} → ♭? b (♯? b x) ≡₁ x
♭?♯? true  = refl
♭?♯? false = refl
