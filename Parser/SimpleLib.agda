------------------------------------------------------------------------
-- Library parsers which do not require the complicated setup used in
-- Parser.Lib
------------------------------------------------------------------------

-- This module also provides an example of a parser for which the
-- Index cannot be inferred.

module Parser.SimpleLib where

open import Parser

open import Data.Nat
open import Data.Vec
open import Data.Vec1 renaming ([] to []₁; _∷_ to _∷₁_)
open import Relation.Nullary
open import Data.Product.Record
open import Data.Bool
open import Data.Function
open import Data.Maybe
open import Data.Unit
open import Logic

------------------------------------------------------------------------
-- Applicative functor parsers

-- We could get these for free with better library support.

infixl 50 _⊛_ _<⊛_ _⊛>_ _<$>_ _<$_

_⊛_ : forall {tok nt i₁ i₂ r₁ r₂} ->
      Parser tok nt i₁ (r₁ -> r₂) ->
      Parser tok nt i₂ r₁ ->
      Parser tok nt _  r₂
p₁ ⊛ p₂ = p₁ >>= \f -> p₂ >>= \x -> return (f x)

_<$>_ : forall {tok nt i r₁ r₂} ->
        (r₁ -> r₂) ->
        Parser tok nt i r₁ ->
        Parser tok nt _ r₂
f <$> x = return f ⊛ x

_<⊛_ : forall {tok nt i₁ i₂ r₁ r₂} ->
       Parser tok nt i₁ r₁ ->
       Parser tok nt i₂ r₂ ->
       Parser tok nt _ r₁
x <⊛ y = const <$> x ⊛ y

_⊛>_ : forall {tok nt i₁ i₂ r₁ r₂} ->
       Parser tok nt i₁ r₁ ->
       Parser tok nt i₂ r₂ ->
       Parser tok nt _ r₂
x ⊛> y = flip const <$> x ⊛ y

_<$_ : forall {tok nt i r₁ r₂} ->
       r₁ ->
       Parser tok nt i r₂ ->
       Parser tok nt _ r₁
x <$ y = const x <$> y

------------------------------------------------------------------------
-- Parsing sequences

-- Note that the resulting index here cannot be inferred...

private

  exactly' : forall {tok nt c r} n ->
             Parser tok nt (false , c) r ->
             Parser tok nt (false , node leaf c) (Vec r (suc n))
  exactly' zero    p = singleton <$> p
  exactly' (suc n) p = _∷_ <$> p ⊛ exactly' n p

-- ...so we might as well generalise the function a little.
-- exactly n p parses n occurrences of p.

exactly-index : Index -> ℕ -> Index
exactly-index i zero    = _
exactly-index i (suc n) = _

exactly : forall {tok nt i r} n ->
          Parser tok nt i r ->
          Parser tok nt (exactly-index i n) (Vec r n)
exactly zero    p = return []
exactly (suc n) p = _∷_ <$> p ⊛ exactly n p

-- A function with a similar type:

sequence : forall {tok nt i r n} ->
           Vec₁ (Parser tok nt i r) n ->
           Parser tok nt (exactly-index i n) (Vec r n)
sequence []₁       = return []
sequence (p ∷₁ ps) = _∷_ <$> p ⊛ sequence ps

------------------------------------------------------------------------
-- sat and friends

sat : forall {tok nt r} ->
      (tok -> Maybe r) -> Parser tok nt 0I r
sat {tok} {nt} {r} p = symbol !>>= \c -> ok (p c)
  where
  okIndex : Maybe r -> Index
  okIndex nothing  = _
  okIndex (just _) = _

  ok : (x : Maybe r) -> Parser tok nt (okIndex x) r
  ok nothing  = fail
  ok (just x) = return x

sat' : forall {tok nt} -> (tok -> Bool) -> Parser tok nt 0I ⊤
sat' p = sat (boolToMaybe ∘ p)

any : forall {tok nt} -> Parser tok nt 0I tok
any = sat just

