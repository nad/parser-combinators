------------------------------------------------------------------------
-- Do the parser combinators form a Kleene algebra?
------------------------------------------------------------------------

module TotalParserCombinators.Laws.KleeneAlgebra where

open import Algebra
open import Data.List as List
open import Data.Nat using (ℕ)
open import Data.Product using (_,_; proj₂)
open import Function using (_$_)
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence
  using (_⇔_; equivalent; module Equivalent)
import Relation.Binary.PropositionalEquality as P
open import Relation.Nullary

open import TotalParserCombinators.Lib
open import TotalParserCombinators.Parser
open import TotalParserCombinators.Semantics
  hiding (_>>=_) renaming (return to return′; _⊛_ to _⊛′_)

------------------------------------------------------------------------
-- A variant of _≲_

infix 4 _≲′_

-- The AdditiveMonoid module shows that _∣_ can be viewed as the join
-- operation of a join-semilattice (if language equivalence is used).
-- This means that the following definition of order is natural.

_≲′_ : ∀ {Tok R xs₁ xs₂} → Parser Tok R xs₁ → Parser Tok R xs₂ → Set₁
p₁ ≲′ p₂ = p₁ ∣ p₂ ≈ p₂

-- This order coincides with _≲_.

≲⇔≲′ : ∀ {Tok R xs₁ xs₂}
       (p₁ : Parser Tok R xs₁) (p₂ : Parser Tok R xs₂) →
       p₁ ≲ p₂ ⇔ p₁ ≲′ p₂
≲⇔≲′ {xs₁ = xs₁} p₁ p₂ =
  equivalent
    (λ (p₁≲p₂ : p₁ ≲ p₂) {_} → equivalent (helper p₁≲p₂) (∣-right xs₁))
    (λ (p₁≲′p₂ : p₁ ≲′ p₂) s∈p₁ → Equivalent.to p₁≲′p₂ ⟨$⟩ ∣-left s∈p₁)
  where
  helper : p₁ ≲ p₂ → p₁ ∣ p₂ ≲ p₂
  helper p₁≲p₂ (∣-left       s∈p₁) = p₁≲p₂ s∈p₁
  helper p₁≲p₂ (∣-right .xs₁ s∈p₂) = s∈p₂

------------------------------------------------------------------------
-- A limited notion of *-continuity

-- Least upper bounds.

record _LeastUpperBoundOf_
         {Tok R xs} {f : ℕ → List R}
         (lub : Parser Tok R xs)
         (p : (n : ℕ) → Parser Tok R (f n)) : Set₁ where
  field
    upper-bound : ∀ n → p n ≲ lub
    least       : ∀ {ys} {ub : Parser Tok R ys} →
                  (∀ n → p n ≲ ub) → lub ≲ ub

-- For argument parsers which are not nullable we can prove that the
-- Kleene star operator is *-continuous.

*-continuous :
  ∀ {Tok R₁ R₂ R₃ fs xs}
  (p₁ : Parser Tok (List R₁ → R₂ → R₃) fs)
  (p₂ : Parser Tok R₁ [])
  (p₃ : Parser Tok R₂ xs) →
  (p₁ ⊛ p₂ ⋆ ⊛ p₃) LeastUpperBoundOf (λ n → p₁ ⊛ p₂ ↑ n ⊛ p₃)
*-continuous {Tok} {R₁ = R₁} {R₃ = R₃} {fs} {xs} p₁ p₂ p₃ =
  record { upper-bound = upper-bound; least = least }
  where
  upper-bound : ∀ n → p₁ ⊛ p₂ ↑ n ⊛ p₃ ≲ p₁ ⊛ p₂ ⋆ ⊛ p₃
  upper-bound n (∈p₁ ⊛′ ∈p₂ⁿ ⊛′ ∈p₃) =
    [ ○ - ○ ] [ ○ - ○ ] ∈p₁ ⊛ Exactly.↑≲⋆ n ∈p₂ⁿ ⊛ ∈p₃

  least : ∀ {ys} {p : Parser Tok R₃ ys} →
          (∀ i → p₁ ⊛ p₂ ↑ i ⊛ p₃ ≲ p) → p₁ ⊛ p₂ ⋆ ⊛ p₃ ≲ p
  least ub (∈p₁ ⊛′ ∈p₂⋆ ⊛′ ∈p₃) with Exactly.⋆≲∃↑ ∈p₂⋆
  ... | (n , ∈p₂ⁿ) = ub n ([ ○ - ○ ] [ ○ - ○ ] ∈p₁ ⊛ ∈p₂ⁿ ⊛ ∈p₃)

------------------------------------------------------------------------
-- The parser combinators do not form a Kleene algebra

-- If we allow arbitrary argument parsers, then we cannot prove the
-- following (variant of a) Kleene algebra axiom.

not-Kleene-algebra :
  ∀ {Tok} →
  Tok →
  (f : ∀ {R xs} → Parser Tok R xs → List (List R)) →
  (_⋆′ : ∀ {R xs} (p : Parser Tok R xs) →
         Parser Tok (List R) (f p)) →
  ¬ (∀ {R xs} {p : Parser Tok R xs} →
     return [] ∣ (p >>= λ x → (p ⋆′) >>= λ xs → return (x ∷ xs))
       ≲ (p ⋆′))
not-Kleene-algebra {Tok} t f _⋆′ fold =
  KleeneStar.unrestricted-incomplete t f _⋆′ ⋆′-complete
  where
  ⋆′-complete : ∀ {xs ys s} {p : Parser Tok Tok ys} →
                xs ∈[ p ]⋆· s → xs ∈ p ⋆′ · s
  ⋆′-complete []         = fold (∣-left return′)
  ⋆′-complete (∈p ∷ ∈p⋆) =
    fold (∣-right [ [] ]
            ([ ○ - ○ ] ∈p >>=
                       fix ([ ○ - ○ ] ⋆′-complete ∈p⋆ >>= return′)))
    where
    fix = cast∈ P.refl P.refl $
                proj₂ (Monoid.identity $ List.monoid Tok) _

-- This shows that the parser combinators do not form a Kleene
-- algebra (interpreted liberally) using _⊛_ for composition, return
-- for unit, etc. However, it should be straightforward to build a
-- recogniser library, based on the parser combinators, which does
-- satisfy the Kleene algebra axioms (see
-- TotalRecognisers.LeftRecursion.KleeneAlgebra).
