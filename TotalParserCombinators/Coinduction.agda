------------------------------------------------------------------------
-- Helper types and functions related to coinduction
------------------------------------------------------------------------

module TotalParserCombinators.Coinduction where

open import Coinduction
open import Data.List  using (List);  open Data.List.List
open import Data.Maybe using (Maybe); open Data.Maybe.Maybe
open import Relation.Binary.PropositionalEquality

-- A tiny universe of type constructors.

data TypeConstr : Set where
  list maybe : TypeConstr

El : TypeConstr → Set → Set
El list  A = List  A
El maybe A = Maybe A

-- Coinductive if the index is [].

data ∞?L (A : Set₁) {B : Set} : List B → Set₁ where
  ⟨_⟩  : ∀ {y ys} (x :   A) → ∞?L A (y ∷ ys)
  ⟪_⟫  :          (x : ∞ A) → ∞?L A []

-- Coinductive if the index is nothing.

data ∞?M (A : Set₁) {B : Set} : Maybe B → Set₁ where
  ⟨_⟩ : ∀ {y} (x :   A) → ∞?M A (just y)
  ⟪_⟫ :       (x : ∞ A) → ∞?M A nothing

-- Coinductive if the index is [] or nothing.

∞? : ∀ {t} → Set₁ → {B : Set} → El t B → Set₁
∞? {list}  = ∞?L
∞? {maybe} = ∞?M

-- Delays if necessary.

♯? : ∀ {t A B} {n : El t B} → A → ∞? A n
♯? {list}  {n = []}      x = ⟪ ♯ x ⟫
♯? {list}  {n = y ∷ ys}  x = ⟨   x ⟩
♯? {maybe} {n = nothing} x = ⟪ ♯ x ⟫
♯? {maybe} {n = just y}  x = ⟨   x ⟩

-- Forces if necessary.

♭? : ∀ {t A B} {n : El t B} → ∞? A n → A
♭? {list}  ⟨ x ⟩ =   x
♭? {list}  ⟪ x ⟫ = ♭ x
♭? {maybe} ⟨ x ⟩ =   x
♭? {maybe} ⟪ x ⟫ = ♭ x

-- A lemma.

♭?♯? : ∀ {t A B} (n : El t B) {x : A} → ♭? (♯? {n = n} x) ≡ x
♭?♯? {list}  []       = refl
♭?♯? {list}  (x ∷ xs) = refl
♭?♯? {maybe} nothing  = refl
♭?♯? {maybe} (just x) = refl
