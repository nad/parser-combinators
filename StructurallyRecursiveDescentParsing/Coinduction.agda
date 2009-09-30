------------------------------------------------------------------------
-- Helper functions related to coinduction
------------------------------------------------------------------------

module StructurallyRecursiveDescentParsing.Coinduction where

open import Coinduction
open import Data.Bool
open import Data.List
open import Relation.Binary.PropositionalEquality1

-- Coinductive if the argument list is empty.

data ∞? (A : Set₁) {B : Set} : List B → Set₁ where
  ⟪_⟫ :          (x : ∞₁ A) → ∞? A []
  ⟨_⟩ : ∀ {y ys} (x :    A) → ∞? A (y ∷ ys)

♯? : ∀ {A B} {xs : List B} → A → ∞? A xs
♯? {xs = []}    x = ⟪ ♯₁ x ⟫
♯? {xs = _ ∷ _} x = ⟨    x ⟩

♭? : ∀ {A B} {xs : List B} → ∞? A xs → A
♭? ⟪ x ⟫ = ♭₁ x
♭? ⟨ x ⟩ =    x

-- A lemma.

♭?♯? : ∀ {A B} (xs : List B) {x : A} → ♭? (♯? {xs = xs} x) ≡₁ x
♭?♯? []      = refl
♭?♯? (_ ∷ _) = refl
