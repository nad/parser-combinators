------------------------------------------------------------------------
-- A breadth-first backend which uses the derivative operator
------------------------------------------------------------------------

module TotalParserCombinators.BreadthFirst where

open import Data.List
import Data.List.Any as Any
open import Data.Product
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Inverse using (_↔_; module Inverse)
open import Relation.Binary.HeterogeneousEquality as H
  using () renaming (_≅_ to _≅H_)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

open Any.Membership-≡

open import TotalParserCombinators.Congruence using (_≅P_; _∎)
import TotalParserCombinators.Congruence.Sound as CS
open import TotalParserCombinators.Derivative as D using (D)
import TotalParserCombinators.InitialBag as I
open import TotalParserCombinators.Parser
open import TotalParserCombinators.Semantics
open import TotalParserCombinators.Simplification as S using (simplify)

------------------------------------------------------------------------
-- A parametrised backend

-- The function f is applied before the derivative.

module Parse
  {Tok}
  (f : ∀ {R xs} → Parser Tok R xs → ∃ λ xs′ → Parser Tok R xs′)
  (f-correct : ∀ {R xs} (p : Parser Tok R xs) → proj₂ (f p) ≅P p)
  where

  -- The parsing function.

  parse : ∀ {R xs} → Parser Tok R xs → List Tok → List R
  parse {xs = xs} p []      = xs
  parse           p (t ∷ s) = parse (D t $ proj₂ $ f p) s

  -- A variant of f-correct.

  f-correct′ : ∀ {R xs} (p : Parser Tok R xs) → proj₂ (f p) ≅ p
  f-correct′ = CS.sound ∘ f-correct

  -- The backend is sound with respect to the semantics.

  sound : ∀ {R xs x} {p : Parser Tok R xs} (s : List Tok) →
          x ∈ parse p s → x ∈ p · s
  sound []      x∈p = I.sound _ x∈p
  sound (t ∷ s) x∈p =
    Inverse.to (f-correct′ _) ⟨$⟩ D.sound _ (sound s x∈p)

  -- The backend is complete with respect to the semantics.

  complete : ∀ {R xs x} {p : Parser Tok R xs} (s : List Tok) →
             x ∈ p · s → x ∈ parse p s
  complete []      x∈p = I.complete x∈p
  complete (t ∷ s) x∈p =
    complete s $ D.complete $ Inverse.from (f-correct′ _) ⟨$⟩ x∈p

  -- The backend does not introduce any unneeded ambiguity.
  --
  -- The proof complete is a left inverse of sound, so the (finite) type
  -- x ∈ parse p s contains at most as many proofs as x ∈ p · s. In
  -- other words, the output of parse p s can only contain n copies of x
  -- if there are at least n distinct parse trees in x ∈ p · s.

  complete∘sound : ∀ {R xs x} s
                   (p : Parser Tok R xs) (x∈p : x ∈ parse p s) →
                   complete s (sound s x∈p) ≡ x∈p
  complete∘sound []      p x∈p = I.complete∘sound p x∈p
  complete∘sound (t ∷ s) p x∈p
    rewrite Inverse.left-inverse-of (f-correct′ p)
              (D.sound (proj₂ (f p)) (sound s x∈p))
          | D.complete∘sound (proj₂ (f p)) (sound s x∈p) =
    complete∘sound s (D t $ proj₂ $ f p) x∈p

  -- The backend does not remove any ambiguity.
  --
  -- The proof complete is a right inverse of sound, which implies that
  -- the (finite) type x ∈ parse p s contains at least as many proofs as
  -- x ∈ p · s. In other words, if the output of parse p s contains n
  -- copies of x, then there are at most n distinct parse trees in
  -- x ∈ p · s.

  sound∘complete : ∀ {R xs x} {p : Parser Tok R xs}
                   (s : List Tok) (x∈p : x ∈ p · s) →
                   sound s (complete s x∈p) ≡ x∈p
  sound∘complete []      x∈p = I.sound∘complete x∈p
  sound∘complete (t ∷ s) x∈p
    rewrite sound∘complete s $
                  D.complete $ Inverse.from (f-correct′ _) ⟨$⟩ x∈p
          | D.sound∘complete $ Inverse.from (f-correct′ _) ⟨$⟩ x∈p
    = Inverse.right-inverse-of (f-correct′ _) x∈p

  -- The backend is correct.

  correct : ∀ {R xs x s} {p : Parser Tok R xs} →
            x ∈ p · s ↔ x ∈ parse p s
  correct {s = s} {p} = record
    { to         = P.→-to-⟶ $ complete s
    ; from       = P.→-to-⟶ $ sound s
    ; inverse-of = record
      { left-inverse-of  = sound∘complete s
      ; right-inverse-of = complete∘sound s p
      }
    }

------------------------------------------------------------------------
-- Specific instantiations

-- Parsing without simplification.

parse : ∀ {Tok R xs} → Parser Tok R xs → List Tok → List R
parse = Parse.parse ,_ _∎

parse-correct : ∀ {Tok R xs x s} {p : Parser Tok R xs} →
                x ∈ p · s ↔ x ∈ parse p s
parse-correct = Parse.correct _ _∎

-- Parsing with simplification.

parse-with-simplification :
  ∀ {Tok R xs} → Parser Tok R xs → List Tok → List R
parse-with-simplification = Parse.parse (λ p → , simplify p) S.correct

parse-with-simplification-correct :
  ∀ {Tok R xs x s} {p : Parser Tok R xs} →
  x ∈ p · s ↔ x ∈ parse-with-simplification p s
parse-with-simplification-correct = Parse.correct _ S.correct

------------------------------------------------------------------------
-- An observation

-- The worst-case complexity of parse (without simplification) is /at
-- least/ exponential in the size of the input string. There is a
-- (finite) parser p whose derivative is p ∣ p (for any token). The
-- n-th derivative thus contains (at least) 2^n outermost occurrences
-- of _∣_, and these occurrences have to be traversed to compute the
-- initial bag of the n-th derivative.

parse-inefficient :
  ∀ {Tok R} → ∃ λ (p : Parser Tok R []) → ∀ t → D t p ≅H p ∣ p
parse-inefficient {R = R} =
  (fail {R = R} >>= (λ _ → fail) , λ t → H.refl)
