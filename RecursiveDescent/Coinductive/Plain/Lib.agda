------------------------------------------------------------------------
-- A library of parser combinators
------------------------------------------------------------------------

module RecursiveDescent.Coinductive.Plain.Lib where

open import Utilities
open import RecursiveDescent.Coinductive.Plain

open import Data.Bool
open import Data.Nat
open import Data.Product.Record
open import Data.Product using () renaming (_,_ to pair)
open import Data.List
open import Data.Function
open import Data.Maybe
open import Data.Unit
import Data.Char as C
open import Relation.Nullary
open import Relation.Binary hiding (NonEmpty)
open import Relation.Binary.PropositionalEquality
open import Logic

------------------------------------------------------------------------
-- Applicative functor parsers

-- We could get these for free with better library support.

infixl 50 _<⊛_ _⊛>_ _<$>_ _<$_

_<$>_ : forall {tok r₁ r₂} ->
        (r₁ -> r₂) -> Parser tok r₁ -> Parser tok r₂
f <$> x = return f ⊛ x

_<⊛_ : forall {tok r₁ r₂} ->
       Parser tok r₁ -> Parser tok r₂ -> Parser tok r₁
x <⊛ y = const <$> x ⊛ y

_⊛>_ : forall {tok r₁ r₂} ->
       Parser tok r₁ -> Parser tok r₂ -> Parser tok r₂
x ⊛> y = flip const <$> x ⊛ y

_<$_ : forall {tok r₁ r₂} ->
       r₁ -> Parser tok r₂ -> Parser tok r₁
x <$ y = const x <$> y

------------------------------------------------------------------------
-- Parsers for sequences

infix 60 _⋆ _+

mutual

  _⋆ : forall {tok r} ->
       (p : Parser tok r) -> {ne : NonEmpty p} ->
       Parser tok [ r ]
  _⋆ p {ne} = return [] ∣ _+ p {ne}

  _+ : forall {tok r} ->
       (p : Parser tok r) -> {ne : NonEmpty p} ->
       Parser tok [ r ]
  _+ p {ne} = _∷_ <$> p ⊛ _⋆ p {ne}

  -- Note that these definitions are not obviously productive.
  -- Furthermore the indices are not obviously terminating. (The
  -- NonEmpty p argument ensures productivity and termination.
  -- However, the argument is currently not used in any way, so
  -- evaluation of open terms can probably fail to terminate.)

-- p sepBy sep parses one or more ps separated by seps.

_sepBy_ : forall {tok r r'} ->
          Parser tok r -> (p : Parser tok r') {ne : NonEmpty p} ->
          Parser tok [ r ]
_sepBy_ p sep {ne} = _∷_ <$> p ⊛ _⋆ (sep ⊛> p) {ne'}
  where
  ne' : NonEmpty (sep ⊛> p)
  ne' with proj₁ (index sep) | witnessToTruth ne
  ne' | ._ | ≡-refl = {! !}

chain₁ :  forall {tok r}
       -> Assoc
       -> (p : Parser tok r) -> {ne : NonEmpty p}
       -> Parser tok (r -> r -> r)
       -> Parser tok r
chain₁ a p {ne} op =
  chain₁-combine a <$> _⋆ (pair <$> p ⊛ op) {ne'} ⊛ p
  where
  ne' : NonEmpty (pair <$> p ⊛ op)
  ne' = {! !}

chain :  forall {tok r}
      -> Assoc
      -> (p : Parser tok r) -> {ne : NonEmpty p}
      -> Parser tok (r -> r -> r)
      -> r
      -> Parser tok r
chain a p {ne} op x = return x ∣ chain₁ a p {ne} op

------------------------------------------------------------------------
-- sat and friends

sat : forall {tok r} -> (tok -> Maybe r) -> Parser tok r
sat {tok} {r} p = symbol !>>= \c -> ok (p c)
  where
  ok : Maybe r -> Parser tok r
  ok nothing  = fail
  ok (just x) = return x

sat' : forall {tok} -> (tok -> Bool) -> Parser tok ⊤
sat' p = sat (boolToMaybe ∘ p)

any : forall {tok} -> Parser tok tok
any = sat just

------------------------------------------------------------------------
-- Parsing a given token (symbol)

module Sym (a : DecSetoid) where

  open DecSetoid a using (_≟_) renaming (carrier to tok)

  sym : tok -> Parser tok tok
  sym x = sat p
    where
    p : tok -> Maybe tok
    p y with x ≟ y
    ... | yes _ = just y
    ... | no  _ = nothing

------------------------------------------------------------------------
-- Character parsers

digit : Parser C.Char ℕ
digit = 0 <$ sym '0'
      ∣ 1 <$ sym '1'
      ∣ 2 <$ sym '2'
      ∣ 3 <$ sym '3'
      ∣ 4 <$ sym '4'
      ∣ 5 <$ sym '5'
      ∣ 6 <$ sym '6'
      ∣ 7 <$ sym '7'
      ∣ 8 <$ sym '8'
      ∣ 9 <$ sym '9'
  where open Sym C.decSetoid

number : Parser C.Char ℕ
number = toNum <$> digit +
  where
  toNum = foldr (\n x -> 10 * x + n) 0 ∘ reverse
