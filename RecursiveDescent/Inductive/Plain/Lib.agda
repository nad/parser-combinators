------------------------------------------------------------------------
-- Some defined parsers, collected in a library
------------------------------------------------------------------------

-- Recursive parsers cannot be defined simply as functions, but have
-- to be defined in terms of a grammar.

-- Non-recursive parsers can either be defined directly or by using a
-- grammar. The grammar version may be harder to use in some cases,
-- but has the potential advantage of increased sharing/less memory
-- usage.

module RecursiveDescent.Inductive.Plain.Lib (tok : Set) where

open import RecursiveDescent.Inductive.Plain
open import RecursiveDescent.Inductive.Plain.SimpleLib
open import Utilities
open import Data.Bool
open import Data.List
open import Data.Product.Record using (_,_)
open import Data.Product renaming (_,_ to pair)

-- Some parameterised parsers.

private

  data NT (nt : ParserType) : ParserType where
    many    :  forall {r}
            -> (p : Parser tok nt r) -> {ne : NonEmpty p}
            -> NT nt _ [ r ]
    many₁   :  forall {r}
            -> (p : Parser tok nt r) -> {ne : NonEmpty p}
            -> NT nt _ [ r ]
    chain'  :  forall {r}
            -> Assoc
            -> (p : Parser tok nt r) -> {ne : NonEmpty p}
            -> Parser tok nt (r -> r -> r)
            -> r
            -> NT nt _ r
    chain₁' :  forall {r}
            -> Assoc
            -> (p : Parser tok nt r) -> {ne : NonEmpty p}
            -> Parser tok nt (r -> r -> r)
            -> NT nt _ r

Nonterminal : ParserType -> ParserType
Nonterminal = NT

module Combinators
         {nt : _}
         (lib : forall {i r} -> Nonterminal nt i r -> nt i r)
         where

  infix 55 _⋆ _+

  _⋆ : forall {r} ->
       (p : Parser tok nt r) -> {ne : NonEmpty p} ->
       Parser tok nt [ r ]
  p ⋆ = ! lib (many p)

  _+ : forall {r} ->
       (p : Parser tok nt r) -> {ne : NonEmpty p} ->
       Parser tok nt [ r ]
  p + = ! lib (many₁ p)

  chain :  forall {r}
        -> Assoc
        -> (p : Parser tok nt r) -> {ne : NonEmpty p}
        -> Parser tok nt (r -> r -> r)
        -> r
        -> Parser tok nt r
  chain a p op x = ! lib (chain' a p op x)

  chain₁ :  forall {r}
         -> Assoc
         -> (p : Parser tok nt r) -> {ne : NonEmpty p}
         -> Parser tok nt (r -> r -> r)
         -> Parser tok nt r
  chain₁ a p op = ! lib (chain₁' a p op)

  library : LibraryGrammar Nonterminal tok nt
  library (many  p {ne})          = ∷= return [] ∣ _+ p {ne}
  library (many₁ p {ne})          = ∷= _∷_ <$> p ⊛ _⋆ p {ne}
  library (chain'  a p {ne} op x) = ∷= return x ∣ chain₁ a p {ne} op
  library (chain₁' a p {ne} op)   = ∷= chain₁-combine a <$>
                                         _⋆ (pair <$> p ⊛ op) {{! !}} ⊛ p
