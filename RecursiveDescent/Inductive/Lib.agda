------------------------------------------------------------------------
-- Some defined parsers, collected in a library
------------------------------------------------------------------------

-- Recursive parsers cannot be defined simply as functions, but have
-- to be defined in terms of a grammar.

-- Non-recursive parsers can either be defined directly or by using a
-- grammar. The grammar version may be harder to use in some cases,
-- but has the potential advantage of increased sharing/less memory
-- usage.

module RecursiveDescent.Inductive.Lib (tok : Set) where

open import RecursiveDescent.Index
open import RecursiveDescent.Inductive
open import RecursiveDescent.Inductive.SimpleLib
open import Utilities

open import Data.Bool
open import Data.List
open import Data.Nat
open import Data.Product.Record using (_,_)
open import Data.Product renaming (_,_ to pair)

-- The index of atLeast can only be partly inferred.

atLeast-index : Corners -> ℕ -> Index
atLeast-index c zero    = _
atLeast-index c (suc n) = _

private

  -- Note that the parsers are parameterised on other parsers.

  data NT (nt : ParserType) : ParserType where
    many     : forall {c r} ->
               Parser tok nt (false , c) r ->
               NT nt _ [ r ]
    many₁    : forall {c r} ->
               Parser tok nt (false , c) r ->
               NT nt _ [ r ]
    atLeast' : forall {c r} (n : ℕ) ->
               Parser tok nt (false , c) r ->
               NT nt (atLeast-index c n) [ r ]
    chain≥'  : forall {c₁ i₂ r} (n : ℕ) ->
               Assoc ->
               Parser tok nt (false , c₁) r ->
               Parser tok nt i₂ (r -> r -> r) ->
               NT nt _ r

Nonterminal : ParserType -> ParserType
Nonterminal = NT

module Combinators
         {nt} (lib : forall {i r} -> Nonterminal nt i r -> nt i r)
         where

  infix 55 _⋆ _+

  _⋆ : forall {c r} ->
       Parser tok nt (false , c) r ->
       Parser tok nt _ [ r ]
  p ⋆ = ! lib (many p)

  _+ : forall {c r} ->
       Parser tok nt (false , c) r ->
       Parser tok nt _ [ r ]
  p + = ! lib (many₁ p)

  -- At least n occurrences of p.

  atLeast : forall {c r} (n : ℕ) ->
            Parser tok nt (false , c) r ->
            Parser tok nt _ [ r ]
  atLeast n p = ! lib (atLeast' n p)

  -- Chains at least n occurrences of op, in an a-associative
  -- manner. The ops are surrounded by ps.

  chain≥ : forall {c₁ i₂ r} (n : ℕ) ->
           Assoc ->
           Parser tok nt (false , c₁) r ->
           Parser tok nt i₂ (r -> r -> r) ->
           Parser tok nt _ r
  chain≥ n a p op = ! lib (chain≥' n a p op)

  library : forall {i r} -> Nonterminal nt i r -> Parser tok nt i r
  library (many  p)            = return [] ∣ p +
  library (many₁ p)            = _∷_ <$> p ⊛ p ⋆
  library (atLeast' zero    p) = p ⋆
  library (atLeast' (suc n) p) = _∷_ <$> p ⊛ atLeast n p
  library (chain≥' n a p op)   = chain₁-combine a <$>
                                   atLeast n (pair <$> p ⊛ op) ⊛ p
