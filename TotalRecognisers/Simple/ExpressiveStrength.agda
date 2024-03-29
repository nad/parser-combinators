------------------------------------------------------------------------
-- This module proves that the recognisers correspond exactly to
-- decidable predicates of type List Bool → Bool (when the alphabet is
-- Bool)
------------------------------------------------------------------------

-- This result could be generalised to other finite alphabets.

module TotalRecognisers.Simple.ExpressiveStrength where

open import Codata.Musical.Notation
open import Data.Bool
open import Data.Bool.Properties
open import Function.Base
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence
  using (_⇔_; equivalence; module Equivalence)
open import Data.List
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable

import TotalRecognisers.Simple
open TotalRecognisers.Simple Bool _≟_

-- One direction of the correspondence has already been established:
-- For every grammar there is an equivalent decidable predicate.

grammar⇒pred : ∀ {n} (p : P n) →
               ∃ λ (f : List Bool → Bool) → ∀ s → s ∈ p ⇔ T (f s)
grammar⇒pred p =
  ((λ s → ⌊ s ∈? p ⌋) , λ _ → equivalence fromWitness toWitness)

-- For every decidable predicate there is a corresponding grammar.
-- Note that these grammars are all "infinite LL(1)".

pred⇒grammar : (f : List Bool → Bool) →
               ∃ λ (p : P (f [])) → ∀ s → s ∈ p ⇔ T (f s)
pred⇒grammar f =
  (grammar f , λ s → equivalence (sound f) (complete f s))
  where
  accept-if-true : ∀ b → P b
  accept-if-true true  = empty
  accept-if-true false = fail

  grammar : (f : List Bool → Bool) → P (f [])
  grammar f = tok true  · ♯ grammar (f ∘ _∷_ true )
            ∣ tok false · ♯ grammar (f ∘ _∷_ false)
            ∣ accept-if-true (f [])

  accept-if-true-sound :
    ∀ b {s} → s ∈ accept-if-true b → s ≡ [] × T b
  accept-if-true-sound true  empty = (refl , _)
  accept-if-true-sound false ()

  accept-if-true-complete : ∀ {b} → T b → [] ∈ accept-if-true b
  accept-if-true-complete ok with Equivalence.to T-≡ ⟨$⟩ ok
  ... | refl = empty

  sound : ∀ f {s} → s ∈ grammar f → T (f s)
  sound f (∣-right s∈) with accept-if-true-sound (f []) s∈
  ... | (refl , ok) = ok
  sound f (∣-left (∣-left  (tok · s∈))) = sound (f ∘ _∷_ true ) s∈
  sound f (∣-left (∣-right (tok · s∈))) = sound (f ∘ _∷_ false) s∈

  complete : ∀ f s → T (f s) → s ∈ grammar f
  complete f [] ok =
    ∣-right {n₁ = false} $ accept-if-true-complete ok
  complete f (true ∷ bs) ok =
    ∣-left {n₁ = false} $ ∣-left {n₁ = false} $
      tok · complete (f ∘ _∷_ true ) bs ok
  complete f (false ∷ bs) ok =
    ∣-left {n₁ = false} $ ∣-right {n₁ = false} $
      tok · complete (f ∘ _∷_ false) bs ok
