------------------------------------------------------------------------
-- Library parsers which do not require the complicated setup used in
-- RecursiveDescent.Inductive.Plain.Lib
------------------------------------------------------------------------

-- This module also provides an example of a parser for which the
-- Index cannot be inferred.

module RecursiveDescent.Inductive.Plain.SimpleLib where

open import RecursiveDescent.Inductive.Plain

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

infixl 50 _<⊛_ _⊛>_ _<$>_ _<$_

_<$>_ : forall {tok nt r₁ r₂} ->
        (r₁ -> r₂) ->
        Parser tok nt r₁ ->
        Parser tok nt r₂
f <$> x = return f ⊛ x

_<⊛_ : forall {tok nt r₁ r₂} ->
       Parser tok nt r₁ ->
       Parser tok nt r₂ ->
       Parser tok nt r₁
x <⊛ y = const <$> x ⊛ y

_⊛>_ : forall {tok nt r₁ r₂} ->
       Parser tok nt r₁ ->
       Parser tok nt r₂ ->
       Parser tok nt r₂
x ⊛> y = flip const <$> x ⊛ y

_<$_ : forall {tok nt r₁ r₂} ->
       r₁ ->
       Parser tok nt r₂ ->
       Parser tok nt r₁
x <$ y = const x <$> y

------------------------------------------------------------------------
-- Parsing sequences

exactly : forall {tok nt r} n ->
          Parser tok nt r ->
          Parser tok nt (Vec r n)
exactly zero    p = return []
exactly (suc n) p = _∷_ <$> p ⊛ exactly n p

sequence : forall {tok nt r n} ->
           Vec₁ (Parser tok nt r) n ->
           Parser tok nt (Vec r n)
sequence []₁       = return []
sequence (p ∷₁ ps) = _∷_ <$> p ⊛ sequence ps

------------------------------------------------------------------------
-- sat and friends

sat : forall {tok nt r} ->
      (tok -> Maybe r) -> Parser tok nt r
sat {tok} {nt} {r} p = symbol !>>= \c -> ok (p c)
  where
  ok : Maybe r -> Parser tok nt r
  ok nothing  = fail
  ok (just x) = return x

sat' : forall {tok nt} -> (tok -> Bool) -> Parser tok nt ⊤
sat' p = sat (boolToMaybe ∘ p)

any : forall {tok nt} -> Parser tok nt tok
any = sat just
