------------------------------------------------------------------------
-- This module proves that the recognisers correspond exactly to
-- decidable predicates of type List Bool → Bool (when the alphabet is
-- Bool)
------------------------------------------------------------------------

-- This result could be generalised to other finite alphabets.

module TotalRecognisers.Simple.ExpressiveStrength where

open import Coinduction
open import Data.Bool
open import Data.Empty
open import Data.Function
open import Data.List
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Decidable

import TotalRecognisers.Simple
open TotalRecognisers.Simple Bool _≟_

-- One direction of the correspondence has already been established:
-- For every grammar there is an equivalent decidable predicate.

grammar⇒pred : ∀ {n} (p : P n) →
               ∃ λ (f : List Bool → Bool) → ∀ s → s ∈ p ⇔ f s ≡ true
grammar⇒pred p = (λ s → decToBool (s ∈? p))
              , λ s → (helper₁ s , helper₂ s)
  where
  helper₁ : ∀ s → s ∈ p → decToBool (s ∈? p) ≡ true
  helper₁ s s∈p with s ∈? p
  ... | yes _  = refl
  ... | no s∉p = ⊥-elim (s∉p s∈p)

  helper₂ : ∀ s → decToBool (s ∈? p) ≡ true → s ∈ p
  helper₂ s eq   with s ∈? p
  helper₂ s refl | yes s∈p = s∈p
  helper₂ s ()   | no  _

-- For every decidable predicate there is a corresponding grammar.
-- Note that these grammars are all "infinite LL(0)".

pred⇒grammar : (f : List Bool → Bool) →
               ∃ λ (p : P (f [])) → ∀ s → s ∈ p ⇔ f s ≡ true
pred⇒grammar f = (grammar f , λ s → (sound f , complete f s))
  where
  accept-if-true : ∀ b → P b
  accept-if-true true  = ε
  accept-if-true false = ∅

  grammar : (f : List Bool → Bool) → P (f [])
  grammar f = tok true  · ♯ grammar (f ∘ _∷_ true )
            ∣ tok false · ♯ grammar (f ∘ _∷_ false)
            ∣ accept-if-true (f [])

  accept-if-true-sound :
    ∀ b {s} → s ∈ accept-if-true b → s ≡ [] × b ≡ true
  accept-if-true-sound true  ε  = (refl , refl)
  accept-if-true-sound false ()

  accept-if-true-complete : ∀ {b} → b ≡ true → [] ∈ accept-if-true b
  accept-if-true-complete refl = ε

  sound : ∀ f {s} → s ∈ grammar f → f s ≡ true
  sound f (∣ʳ s∈) with accept-if-true-sound (f []) s∈
  ... | (refl , eq) = eq
  sound f (∣ˡ (∣ˡ (tok · s∈))) = sound (f ∘ _∷_ true ) s∈
  sound f (∣ˡ (∣ʳ (tok · s∈))) = sound (f ∘ _∷_ false) s∈

  complete : ∀ f s → f s ≡ true → s ∈ grammar f
  complete f [] eq =
    ∣ʳ {n₁ = false} $ accept-if-true-complete eq
  complete f (true ∷ bs) eq =
    ∣ˡ {n₁ = false} $ ∣ˡ {n₁ = false} $
      tok · complete (f ∘ _∷_ true ) bs eq
  complete f (false ∷ bs) eq =
    ∣ˡ {n₁ = false} $ ∣ʳ {n₁ = false} $
      tok · complete (f ∘ _∷_ false) bs eq
