------------------------------------------------------------------------
-- Some defined parsers, collected in a library
------------------------------------------------------------------------

-- Recursive parsers cannot be defined simply as functions, but have
-- to be defined in terms of a grammar.

-- Non-recursive parsers can either be defined directly or by using a
-- grammar. The grammar version may be harder to use in some cases,
-- but has the potential advantage of increased sharing/less memory
-- usage.

module RecursiveDescent.Inductive.Indexed.Lib (tok : Set) where

open import RecursiveDescent.Inductive.Indexed
open import RecursiveDescent.Inductive.Indexed.SimpleLib
open import Utilities
open import Data.Bool
open import Data.List
open import Data.Product.Record using (_,_)
open import Data.Product renaming (_,_ to pair)

-- Some parameterised parsers.

private

  data NT (nt : ParserType) : ParserType where
    many    :  forall {c r}
            -> Parser tok nt (false , c) r
            -> NT nt _ [ r ]
    many₁   :  forall {c r}
            -> Parser tok nt (false , c) r
            -> NT nt _ [ r ]
    chain'  :  forall {c₁ i₂ r}
            -> Assoc
            -> Parser tok nt (false , c₁) r
            -> Parser tok nt i₂ (r -> r -> r)
            -> r
            -> NT nt _ r
    chain₁' :  forall {c₁ i₂ r}
            -> Assoc
            -> Parser tok nt (false , c₁) r
            -> Parser tok nt i₂ (r -> r -> r)
            -> NT nt _ r

Nonterminal : ParserType -> ParserType
Nonterminal = NT

module Combinators
         {nt : _}
         (lib : forall {i r} -> Nonterminal nt i r -> nt i r)
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

  chain :  forall {c₁ i₂ r}
        -> Assoc
        -> Parser tok nt (false , c₁) r
        -> Parser tok nt i₂ (r -> r -> r)
        -> r
        -> Parser tok nt _ r
  chain a p op x = ! lib (chain' a p op x)

  chain₁ :  forall {c₁ i₂ r}
         -> Assoc
         -> Parser tok nt (false , c₁) r
         -> Parser tok nt i₂ (r -> r -> r)
         -> Parser tok nt _ r
  chain₁ a p op = ! lib (chain₁' a p op)

  library : forall {i r} -> Nonterminal nt i r -> Parser tok nt i r
  library (many  p)          = return [] ∣ p +
  library (many₁ p)          = _∷_ <$> p ⊛ p ⋆
  library (chain'  a p op x) = return x ∣ chain₁ a p op
  library (chain₁' a p op)   = chain₁-combine a <$>
                                 (pair <$> p ⊛ op) ⋆ ⊛ p
