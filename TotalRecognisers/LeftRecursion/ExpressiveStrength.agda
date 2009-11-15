------------------------------------------------------------------------
-- This module proves that the recognisers correspond exactly to
-- decidable predicates of type List Bool → Bool (when the alphabet is
-- Bool)
------------------------------------------------------------------------

-- This result could be generalised to other finite alphabets.

module TotalRecognisers.LeftRecursion.ExpressiveStrength where

open import Coinduction
open import Data.Bool hiding (_∧_)
open import Data.Bool.Properties
open import Data.Function
open import Data.List
open import Data.List.Reverse
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Decidable

import TotalRecognisers.LeftRecursion
open TotalRecognisers.LeftRecursion Bool
import TotalRecognisers.LeftRecursion.Lib
private
  open module Tok = TotalRecognisers.LeftRecursion.Lib.Tok Bool _≟_
         using (tok)

------------------------------------------------------------------------
-- A boring lemma

private

  lemma : (f : List Bool → Bool) →
          (false ∧ f [ true ] ∨ false ∧ f [ false ]) ∨ f [] ≡ f []
  lemma f = cong₂ (λ b₁ b₂ → (b₁ ∨ b₂) ∨ f [])
                  (left-zero (f [ true  ]))
                  (left-zero (f [ false ]))

------------------------------------------------------------------------
-- Expressive strength

-- One direction of the correspondence has already been established:
-- For every grammar there is an equivalent decidable predicate.

grammar⇒pred : ∀ {n} (p : P n) →
               ∃ λ (f : List Bool → Bool) → ∀ s → s ∈ p ⇔ T (f s)
grammar⇒pred p =
  ((λ s → decToBool (s ∈? p)) , λ _ → (fromWitness , toWitness))

-- For every decidable predicate there is a corresponding grammar.
-- Note that these grammars are all "infinite LL(0)".

pred⇒grammar : (f : List Bool → Bool) →
               ∃ λ (p : P (f [])) → ∀ s → s ∈ p ⇔ T (f s)
pred⇒grammar f = (p f , λ s → (p-sound f , p-complete f s))
  where
  accept-if-true : ∀ b → P b
  accept-if-true true  = ε
  accept-if-true false = ∅

  p : (f : List Bool → Bool) → P (f [])
  p f = cast (lemma f)
      ( ♯? (tok true ) · ⟪ ♯ p (f ∘ _∷_ true ) ⟫
      ∣ ♯? (tok false) · ⟪ ♯ p (f ∘ _∷_ false) ⟫
      ∣ accept-if-true (f [])
      )

  accept-if-true-sound :
    ∀ b {s} → s ∈ accept-if-true b → s ≡ [] × T b
  accept-if-true-sound true  ε  = (refl , _)
  accept-if-true-sound false ()

  accept-if-true-complete : ∀ {b} → T b → [] ∈ accept-if-true b
  accept-if-true-complete ok with proj₁ T-≡ ok
  ... | refl = ε

  p-sound : ∀ f {s} → s ∈ p f → T (f s)
  p-sound f (cast (∣ʳ s∈)) with accept-if-true-sound (f []) s∈
  ... | (refl , ok) = ok
  p-sound f (cast (∣ˡ (∣ˡ (t∈ · s∈)))) with Tok.sound (drop-♭♯ (f [ true  ]) t∈)
  ... | refl = p-sound (f ∘ _∷_ true ) s∈
  p-sound f (cast (∣ˡ (∣ʳ (t∈ · s∈)))) with Tok.sound (drop-♭♯ (f [ false ]) t∈)
  ... | refl = p-sound (f ∘ _∷_ false) s∈

  p-complete : ∀ f s → T (f s) → s ∈ p f
  p-complete f [] ok =
    cast (∣ʳ {n₁ = false ∧ f [ true ] ∨ false ∧ f [ false ]} $
      accept-if-true-complete ok)
  p-complete f (true  ∷ bs) ok =
    cast (∣ˡ $ ∣ˡ $
      add-♭♯ (f [ true  ]) Tok.complete ·
      p-complete (f ∘ _∷_ true ) bs ok)
  p-complete f (false ∷ bs) ok =
    cast (∣ˡ $ ∣ʳ {n₁ = false ∧ f [ true ]} $
      add-♭♯ (f [ false ]) Tok.complete ·
      p-complete (f ∘ _∷_ false) bs ok)

-- An alternative proof which uses a left recursive definition of the
-- grammar to avoid the use of a cast.

pred⇒grammar′ : (f : List Bool → Bool) →
                ∃ λ (p : P (f [])) → ∀ s → s ∈ p ⇔ T (f s)
pred⇒grammar′ f = (p f , λ s → (p-sound f , p-complete f s))
  where
  extend : ∀ {A B} → (List A → B) → A → (List A → B)
  extend f x = λ xs → f (xs ∷ʳ x)

  accept-if-true : ∀ b → P b
  accept-if-true true  = ε
  accept-if-true false = ∅

  p : (f : List Bool → Bool) → P (f [])
  p f = ⟪ ♯ p (extend f true ) ⟫ · ♯? (tok true )
      ∣ ⟪ ♯ p (extend f false) ⟫ · ♯? (tok false)
      ∣ accept-if-true (f [])

  accept-if-true-sound :
    ∀ b {s} → s ∈ accept-if-true b → s ≡ [] × T b
  accept-if-true-sound true  ε  = (refl , _)
  accept-if-true-sound false ()

  accept-if-true-complete : ∀ {b} → T b → [] ∈ accept-if-true b
  accept-if-true-complete ok with proj₁ T-≡ ok
  ... | refl = ε

  p-sound : ∀ f {s} → s ∈ p f → T (f s)
  p-sound f (∣ʳ s∈) with accept-if-true-sound (f []) s∈
  ... | (refl , ok) = ok
  p-sound f (∣ˡ (∣ˡ (s∈ · t∈))) with Tok.sound (drop-♭♯ (f [ true  ]) t∈)
  ... | refl = p-sound (extend f true ) s∈
  p-sound f (∣ˡ (∣ʳ (s∈ · t∈))) with Tok.sound (drop-♭♯ (f [ false ]) t∈)
  ... | refl = p-sound (extend f false) s∈

  p-complete′ : ∀ f {s} → Reverse s → T (f s) → s ∈ p f
  p-complete′ f [] ok =
    ∣ʳ {n₁ = false} $ accept-if-true-complete ok
  p-complete′ f (bs ∶ rs ∶ʳ true ) ok =
    ∣ˡ {n₁ = false} $ ∣ˡ {n₁ = false} $
      p-complete′ (extend f true ) rs ok ·
      add-♭♯ (f [ true  ]) Tok.complete
  p-complete′ f (bs ∶ rs ∶ʳ false) ok =
    ∣ˡ {n₁ = false} $ ∣ʳ {n₁ = false} $
      p-complete′ (extend f false) rs ok ·
      add-♭♯ (f [ false ]) Tok.complete

  p-complete : ∀ f s → T (f s) → s ∈ p f
  p-complete f s = p-complete′ f (reverseView s)
