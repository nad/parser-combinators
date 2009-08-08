------------------------------------------------------------------------
-- Operators
------------------------------------------------------------------------

module Mixfix.Operator where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Vec  using (Vec)
open import Data.Product using (∃; ∃₂; _,_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.String using (String)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Mixfix.Fixity

-- Name parts.

NamePart : Set
NamePart = String

-- Operators. The parameter arity is the internal arity of the
-- operator, i.e. the number of arguments taken between the first and
-- last name parts.

record Operator (fix : Fixity) (arity : ℕ) : Set where
  field nameParts : Vec NamePart (1 + arity)

open Operator public

-- Predicate filtering out operators of the given fixity and
-- associativity.

hasFixity : ∀ fix → ∃₂ Operator → Maybe (∃ (Operator fix))
hasFixity fix (fix' , op) with fix ≟ fix'
hasFixity fix (.fix , op) | yes refl = just op
hasFixity fix (fix' , op) | _        = nothing
