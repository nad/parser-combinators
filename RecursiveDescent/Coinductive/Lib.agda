------------------------------------------------------------------------
-- A library of parser combinators
------------------------------------------------------------------------

module RecursiveDescent.Coinductive.Lib where

open import Utilities
open import RecursiveDescent.Coinductive

open import Data.Bool
open import Data.Nat
open import Data.Product.Record using (_,_)
open import Data.Product renaming (_,_ to pair)
open import Data.List
open import Data.Function
open import Data.Maybe
open import Data.Unit
import Data.Char as C
open import Relation.Nullary
open import Relation.Binary

------------------------------------------------------------------------
-- Applicative functor parsers

-- We could get these for free with better library support.

infixl 50 _⊛_ _<⊛_ _⊛>_ _<$>_ _<$_

-- Note that all the resulting indices can be inferred.

_⊛_ : forall {tok i₁ i₂ r₁ r₂} ->
      Parser tok i₁ (r₁ -> r₂) -> Parser tok i₂ r₁ -> Parser tok _ r₂
p₁ ⊛ p₂ = p₁ >>= \f -> p₂ >>= \x -> return (f x)

_<$>_ : forall {tok r₁ r₂ i} ->
        (r₁ -> r₂) -> Parser tok i r₁ -> Parser tok _ r₂
f <$> x = return f ⊛ x

_<⊛_ : forall {tok i₁ i₂ r₁ r₂} ->
       Parser tok i₁ r₁ -> Parser tok i₂ r₂ -> Parser tok _ r₁
x <⊛ y = const <$> x ⊛ y

_⊛>_ : forall {tok i₁ i₂ r₁ r₂} ->
       Parser tok i₁ r₁ -> Parser tok i₂ r₂ -> Parser tok _ r₂
x ⊛> y = flip const <$> x ⊛ y

_<$_ : forall {tok r₁ r₂ i} ->
       r₁ -> Parser tok i r₂ -> Parser tok _ r₁
x <$ y = const x <$> y

------------------------------------------------------------------------
-- Parsers for sequences

infix 60 _⋆ _+

mutual

  _⋆ : forall {tok r d} ->
       Parser tok (false , d) r     ->
       Parser tok _           [ r ]
  p ⋆ = return [] ∣ p +

  _+ : forall {tok r d} ->
       Parser tok (false , d) r     ->
       Parser tok _           [ r ]
  p + = _∷_ <$> p ⊛ p ⋆

  -- Are these definitions productive? _∣_ and _⊛_ are not
  -- constructors... Unfolding we get (unless I've made some mistake)
  --
  --   p ⋆ = alt₁ false (ret []) (p +)
  --
  -- and
  --
  --   p + = bind₁ (bind₀ (ret _∷_) (\f -> bind₁ p (\x -> ret (f x))))
  --               (\f -> bind₀ (p ⋆) (\x -> ret (f x)))
  --
  -- These definitions are guarded.

-- p sepBy sep parses one or more ps separated by seps.

_sepBy_ : forall {tok r r' i d} ->
          Parser tok i r -> Parser tok (false , d) r' ->
          Parser tok _ [ r ]
p sepBy sep = _∷_ <$> p ⊛ (sep ⊛> p) ⋆

chain₁ :  forall {tok d₁ i₂ r}
       -> Assoc
       -> Parser tok (false , d₁) r
       -> Parser tok i₂ (r -> r -> r)
       -> Parser tok _ r
chain₁ a p op = chain₁-combine a <$> (pair <$> p ⊛ op) ⋆ ⊛ p

chain :  forall {tok d₁ i₂ r}
      -> Assoc
      -> Parser tok (false , d₁) r
      -> Parser tok i₂ (r -> r -> r)
      -> r
      -> Parser tok _ r
chain a p op x = return x ∣ chain₁ a p op

------------------------------------------------------------------------
-- sat and friends

sat : forall {tok r} ->
      (tok -> Maybe r) -> Parser tok _ r
sat {tok} {r} p = symbol !>>= \c -> ok (p c)
  where
  okIndex : Maybe r -> Index
  okIndex nothing  = _
  okIndex (just _) = _

  ok : (x : Maybe r) -> Parser tok (okIndex x) r
  ok nothing  = fail
  ok (just x) = return x

sat' : forall {tok} -> (tok -> Bool) -> Parser tok _ ⊤
sat' p = sat (boolToMaybe ∘ p)

any : forall {tok} -> Parser tok _ tok
any = sat just

------------------------------------------------------------------------
-- Parsing a given token (symbol)

module Sym (a : DecSetoid) where

  open DecSetoid a using (_≟_) renaming (carrier to tok)

  sym : tok -> Parser tok _ tok
  sym x = sat p
    where
    p : tok -> Maybe tok
    p y with x ≟ y
    ... | yes _ = just y
    ... | no  _ = nothing

------------------------------------------------------------------------
-- Character parsers

digit : Parser C.Char _ ℕ
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

number : Parser C.Char _ ℕ
number = toNum <$> digit +
  where
  toNum = foldr (\n x -> 10 * x + n) 0 ∘ reverse
