------------------------------------------------------------------------
-- Some defined parsers, collected in a library
------------------------------------------------------------------------

-- Recursive parsers cannot be defined simply as functions, but have
-- to be defined in terms of a grammar.

-- Non-recursive parsers can either be defined directly or by using a
-- grammar. The grammar version may be harder to use in some cases,
-- but has the potential advantage of increased sharing/less memory
-- usage.

module Parser.Lib (tok : Set) where

open import Parser
open import Parser.Lib.Types
open import Data.Bool
open import Data.List
open import Data.Product.Record hiding (_×_)
open import Data.Product renaming (_,_ to <_∣_>)

-- Some parameterised parsers.

private

  data NT (nt : ParserType) : ParserType where
    many    :  forall {d r}
            -> Parser tok nt (false , d) r
            -> NT nt _ [ r ]
    many₁   :  forall {d r}
            -> Parser tok nt (false , d) r
            -> NT nt _ [ r ]
    chain'  :  forall {d₁ i₂ r}
            -> Assoc
            -> Parser tok nt (false , d₁) r
            -> Parser tok nt i₂ (r -> r -> r)
            -> r
            -> NT nt _ r
    chain₁' :  forall {d₁ i₂ r}
            -> Assoc
            -> Parser tok nt (false , d₁) r
            -> Parser tok nt i₂ (r -> r -> r)
            -> NT nt _ r

Nonterminal : ParserType -> ParserType
Nonterminal = NT

module Combinators
         {nt : _}
         (lib : forall {i r} -> Nonterminal nt i r -> nt i r)
         where

  infix 55 _⋆ _+

  _⋆ : forall {d r} ->
       Parser tok nt (false , d) r ->
       Parser tok nt _ [ r ]
  p ⋆ = ! lib (many p)

  _+ : forall {d r} ->
       Parser tok nt (false , d) r ->
       Parser tok nt _ [ r ]
  p + = ! lib (many₁ p)

  chain :  forall {d₁ i₂ r}
        -> Assoc
        -> Parser tok nt (false , d₁) r
        -> Parser tok nt i₂ (r -> r -> r)
        -> r
        -> Parser tok nt _ r
  chain a p op x = ! lib (chain' a p op x)

  chain₁ :  forall {d₁ i₂ r}
         -> Assoc
         -> Parser tok nt (false , d₁) r
         -> Parser tok nt i₂ (r -> r -> r)
         -> Parser tok nt _ r
  chain₁ a p op = ! lib (chain₁' a p op)

  library : forall {i r} -> Nonterminal nt i r -> Parser tok nt i r
  library (many  p)          = ε [] ∣ p +
  library (many₁ p)          = _∷_ $ p · p ⋆
  library (chain'  a p op x) = ε x ∣ chain₁ a p op
  library (chain₁' a p op)   = comb a $ (<_∣_> $ p · op) ⋆ · p
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
