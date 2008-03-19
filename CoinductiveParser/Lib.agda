------------------------------------------------------------------------
-- A library of parser combinators
------------------------------------------------------------------------

module CoinductiveParser.Lib where

open import Parser.Lib.Types
open import CoinductiveParser
open import CoinductiveParser.Index

open import Data.Bool
open import Data.Nat
open import Data.Product.Record hiding (_×_)
open import Data.Product renaming (_,_ to <_∣_>)
open import Data.List
open import Data.Function
open import Data.Maybe
import Data.Char as C
open import Relation.Nullary
open import Relation.Binary

------------------------------------------------------------------------
-- Applicative functor parsers

-- We could get these for free with better library support.

infixl 4 _⊛_ _<⊛_ _⊛>_ _<$>_ _<$_

-- Parser together with return and _⊛_ form a (generalised)
-- applicative functor. (Warning: I have not checked that the laws are
-- actually satisfied.)

-- Note that all the resulting indices can be inferred.

_⊛_ : forall {tok r₁ r₂ i₁ i₂} ->
      Parser tok i₁ (r₁ -> r₂) -> Parser tok i₂ r₁ ->
      Parser tok _ r₂ -- (i₁ ·I (i₂ ·I 1I))
f ⊛ x = f >>= \f' -> x >>= \x' -> return (f' x')

_<$>_ : forall {tok r₁ r₂ i} ->
        (r₁ -> r₂) -> Parser tok i r₁ -> Parser tok _ r₂ -- (i ·I 1I)
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
  -- constructors... Unfolding (and ignoring some casts) we get
  -- (unless I've made some mistake)
  --
  --   p ⋆ = parser \k -> Base._∣_ (k []) (unP (p +) k)
  --
  -- and
  --
  --   p + = parser (\k -> unP p     (\x  ->
  --                       unP (p ⋆) (\xs -> k (x ∷ xs))))
  --       = parser (\k -> unP p     (\x  -> Base._∣_ (k (x ∷ []))
  --                      (unP (p +) (\xs -> k (x ∷ xs))))).
  --
  -- Assume that p + is applied to the continuation k =
  -- const Base.fail. We get
  --
  --   unP (p +) k = unP p (\x -> unP (p +) (\xs -> Base.fail)).
  --
  -- Note that this implies that the definitions above are not
  -- (obviously) productive! Perhaps our type system ensures that
  -- unP p ... unfolds to a guarded application (since p does not
  -- accept the empty string), but I don't expect that any automatic
  -- productivity checker will spot this (not in the near future,
  -- anyway). It seems as if we need to use a type system which allows
  -- us to encode productivity in the types.

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
chain₁ a p op = comb a <$> (<_∣_> <$> p ⊛ op) ⋆ ⊛ p
  where
  comb : forall {r} -> Assoc -> [ r × (r -> r -> r) ] -> r -> r
  comb right xs y = foldr app y xs
    where
    app : forall {r} -> r × (r -> r -> r) -> r -> r
    app < x ∣ _•_ > y = x • y
  comb left xs y = helper (reverse xs) y
    where
    helper : forall {r} -> [ r × (r -> r -> r) ] -> r -> r
    helper []                 y = y
    helper (< x ∣ _•_ > ∷ ps) y = helper ps x • y

chain :  forall {tok d₁ i₂ r}
      -> Assoc
      -> Parser tok (false , d₁) r
      -> Parser tok i₂ (r -> r -> r)
      -> r
      -> Parser tok _ r
chain a p op x = return x ∣ chain₁ a p op

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
