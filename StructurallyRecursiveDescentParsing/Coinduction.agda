------------------------------------------------------------------------
-- Helper functions related to coinduction
------------------------------------------------------------------------

module StructurallyRecursiveDescentParsing.Coinduction where

open import Coinduction
open import Data.Bool
open import Relation.Binary.PropositionalEquality1

-- Coinductive if the argument is false.

∞? : Bool → Set1 → Set1
∞? true  A =    A
∞? false A = ∞₁ A

♯? : ∀ b {A} → A → ∞? b A
♯? true  x =    x
♯? false x = ♯₁ x

♭? : ∀ b {A} → ∞? b A → A
♭? true  x =    x
♭? false x = ♭₁ x
