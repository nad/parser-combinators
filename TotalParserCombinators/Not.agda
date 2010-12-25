------------------------------------------------------------------------
-- Not
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

module TotalParserCombinators.Not where

open import Data.Bool
open import Data.Empty
open import Data.List
open import Data.List.Any as Any using (here; there)
open import Data.Product
open import Data.Unit
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence using (module Equivalent)
open import Function.Inverse as Inv using (_⇿_)
import Function.Inverse.TypeIsomorphisms as Iso
open import Level
open import Relation.Binary.PropositionalEquality as P using (_≡_)
import Relation.Binary.Sigma.Pointwise as Σ

open Any.Membership-≡ using (_∈_) renaming (_≈[_]_ to _List-≈[_]_)

open import TotalParserCombinators.BreadthFirst hiding (correct)
open import TotalParserCombinators.Congruence as C using (_≈[_]P_; _≅P_)
open import TotalParserCombinators.Parser
import TotalParserCombinators.Pointwise as Pointwise
open import TotalParserCombinators.Semantics using (_∈_·_)

------------------------------------------------------------------------
-- An initial bag operator

-- not-index xs is non-empty iff xs is empty.

not-index : {R : Set} → List R → List ⊤
not-index xs = if null xs then [ tt ] else []

-- not-index preserves equality.

not-index-cong : ∀ {k R} {xs xs′ : List R} →
                 xs List-≈[ k ] xs′ →
                 not-index xs List-≈[ k ] not-index xs′
not-index-cong {xs = []   } {xs′ = []   } eq = Inv.⇿⇒ Inv.id
not-index-cong {xs = _ ∷ _} {xs′ = _ ∷ _} eq = Inv.⇿⇒ Inv.id
not-index-cong {xs = []   } {xs′ = _ ∷ _} eq
  with Equivalent.from (Inv.⇒⇔ eq) ⟨$⟩ here P.refl
... | ()
not-index-cong {xs = _ ∷ _} {xs′ = []   } eq
  with Equivalent.to   (Inv.⇒⇔ eq) ⟨$⟩ here P.refl
... | ()

-- not-index is correct, assuming that propositional equality is
-- extensional.

not-index-correct :
  P.Extensionality zero zero →
  ∀ {R} (xs : List R) → tt ∈ not-index xs ⇿ ∄ λ x → x ∈ xs
not-index-correct ext [] = record
  { to         = P.→-to-⟶ to
  ; from       = P.→-to-⟶ from
  ; inverse-of = record
    { left-inverse-of  = from∘to
    ; right-inverse-of = to∘from
    }
  }
  where
  to : tt ∈ [ tt ] → ∄ λ x → x ∈ []
  to _ (_ , ())

  from : (∄ λ x → x ∈ []) → tt ∈ [ tt ]
  from _ = here P.refl

  to∘from : (p : ∄ λ x → x ∈ []) → to (from p) ≡ p
  to∘from p = ext helper
    where
    helper : (∈[] : ∃ λ x → x ∈ []) → to (from p) ∈[] ≡ p ∈[]
    helper (_ , ())

  from∘to : (p : tt ∈ [ tt ]) → from (to p) ≡ p
  from∘to (here P.refl) = P.refl
  from∘to (there ())

not-index-correct ext (x ∷ xs) = record
  { to         = P.→-to-⟶ to
  ; from       = P.→-to-⟶ from
  ; inverse-of = record
    { left-inverse-of  = λ ()
    ; right-inverse-of = to∘from
    }
  }
  where
  ys = x ∷ xs

  to : tt ∈ [] → ∄ λ y → y ∈ ys
  to ()

  from : (∄ λ y → y ∈ ys) → tt ∈ []
  from y∉∷ with y∉∷ (, here P.refl)
  ... | ()

  to∘from : (p : ∄ λ y → y ∈ ys) → to (from p) ≡ p
  to∘from y∉∷ with y∉∷ (, here P.refl)
  ... | ()

------------------------------------------------------------------------
-- Not

-- ¬_ is defined as a pointwise lifting of not-index.

private
  module Not {R : Set} =
    Pointwise ⊥ R (const not-index) (const not-index-cong)

infix 60 ¬_ ¬-cong_

-- ¬ p returns a result if p doesn't.

¬_ : ∀ {Tok R xs} → Parser Tok R xs → Parser Tok ⊤ (not-index xs)
¬_ = Not.lift fail

-- D distributes over ¬_.

D-¬ : ∀ {Tok R xs t} (p : Parser Tok R xs) → D t (¬ p) ≅P ¬ D t p
D-¬ = Not.D-lift fail

-- ¬_ preserves equality.

¬-cong_ : ∀ {k Tok R xs xs′}
            {p : Parser Tok R xs} {p′ : Parser Tok R xs′} →
          p ≈[ k ]P p′ → ¬ p ≈[ k ]P ¬ p′
¬-cong_ = Not.lift-cong C.fail

-- ¬_ is correct (assuming that propositional equality is
-- extensional).

correct : (∀ {ℓ} → P.Extensionality ℓ zero) →
          ∀ {Tok R xs s} (p : Parser Tok R xs) →
          tt ∈ ¬ p · s ⇿ ∄ λ x → x ∈ p · s
correct ext =
  Not.lift-property
    (λ _ G H → H tt ⇿ ∄ G)
    (λ _ G⇿G′ H⇿H′ →
       Iso.Isomorphism-cong
         (H⇿H′ tt)
         (Iso.¬-cong ext ext $ Σ.cong λ {x} → G⇿G′ x))
    (not-index-correct ext _)
    fail
