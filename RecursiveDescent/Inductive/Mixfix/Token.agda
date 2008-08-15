------------------------------------------------------------------------
-- Tokens used by the mixfix operator parser
------------------------------------------------------------------------

module RecursiveDescent.Inductive.Mixfix.Token where

open import Data.String
open import Data.Function
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

NamePart : Set
NamePart = String

data Token : Set where
  namePart : (n : NamePart) -> Token
  atom     : Token
  ⟨        : Token  -- Open  parenthesis.
  ⟩        : Token  -- Close parenthesis.

tokenSetoid : DecSetoid
tokenSetoid = ≡-decSetoid eq?
  where
  n≢a : forall {n} -> namePart n ≢ atom
  n≢a ()

  n≢⟨ : forall {n} -> namePart n ≢ ⟨
  n≢⟨ ()

  n≢⟩ : forall {n} -> namePart n ≢ ⟩
  n≢⟩ ()

  a≢⟨ : atom ≢ ⟨
  a≢⟨ ()

  a≢⟩ : atom ≢ ⟩
  a≢⟩ ()

  ⟨≢⟩ : ⟨ ≢ ⟩
  ⟨≢⟩ ()

  drop-namePart : forall {n n'} -> namePart n ≡ namePart n' -> n ≡ n'
  drop-namePart ≡-refl = ≡-refl

  eq? : Decidable (_≡_ {Token})
  eq? (namePart n) (namePart n') with n ≟ n'
  eq? (namePart n) (namePart .n) | yes ≡-refl = yes ≡-refl
  eq? (namePart n) (namePart n') | no ≢       = no (≢ ∘ drop-namePart)
  eq? (namePart n) atom          = no n≢a
  eq? (namePart n) ⟨             = no n≢⟨
  eq? (namePart n) ⟩             = no n≢⟩
  eq? atom         (namePart y)  = no (n≢a ∘ ≡-sym)
  eq? atom         atom          = yes ≡-refl
  eq? atom         ⟨             = no a≢⟨
  eq? atom         ⟩             = no a≢⟩
  eq? ⟨            (namePart y)  = no (n≢⟨ ∘ ≡-sym)
  eq? ⟨            atom          = no (a≢⟨ ∘ ≡-sym)
  eq? ⟨            ⟨             = yes ≡-refl
  eq? ⟨            ⟩             = no ⟨≢⟩
  eq? ⟩            (namePart n)  = no (n≢⟩ ∘ ≡-sym)
  eq? ⟩            atom          = no (a≢⟩ ∘ ≡-sym)
  eq? ⟩            ⟨             = no (⟨≢⟩ ∘ ≡-sym)
  eq? ⟩            ⟩             = yes ≡-refl
