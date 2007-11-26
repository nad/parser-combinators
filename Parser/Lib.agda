module Parser.Lib (tok : Set) where

open import Parser
open import Parser.Lib.Types
open import Data.Bool
open import Data.List
open import Data.Product.Record hiding (_×_)
open import Data.Product renaming (_,_ to <_∣_>)

-- Some parameterised parsers.

private

  data Name' (name : ParserType) : ParserType where
    many    :  forall {d r}
            -> Parser tok name (false , d) r
            -> Name' name _ [ r ]
    many₁   :  forall {d r}
            -> Parser tok name (false , d) r
            -> Name' name _ [ r ]
    chain'  :  forall {d₁ i₂ r}
            -> Assoc
            -> Parser tok name (false , d₁) r
            -> Parser tok name i₂ (r -> r -> r)
            -> r
            -> Name' name _ r
    chain₁' :  forall {d₁ i₂ r}
            -> Assoc
            -> Parser tok name (false , d₁) r
            -> Parser tok name i₂ (r -> r -> r)
            -> Name' name _ r

Name : ParserType -> ParserType
Name = Name'

module Combinators
         {name : _}
         (lib : forall {i r} -> Name name i r -> name i r)
         where

  infix 55 _⋆ _+

  _⋆ : forall {d r} ->
       Parser tok name (false , d) r ->
       Parser tok name _ [ r ]
  p ⋆ = ! lib (many p)

  _+ : forall {d r} ->
       Parser tok name (false , d) r ->
       Parser tok name _ [ r ]
  p + = ! lib (many₁ p)

  chain :  forall {d₁ i₂ r}
        -> Assoc
        -> Parser tok name (false , d₁) r
        -> Parser tok name i₂ (r -> r -> r)
        -> r
        -> Parser tok name _ r
  chain a p op x = ! lib (chain' a p op x)

  chain₁ :  forall {d₁ i₂ r}
         -> Assoc
         -> Parser tok name (false , d₁) r
         -> Parser tok name i₂ (r -> r -> r)
         -> Parser tok name _ r
  chain₁ a p op = ! lib (chain₁' a p op)

  -- Note that non-recursive parsers can either be defined directly or
  -- by using a constructor. The constructor version has the advantage
  -- of increased sharing.

  library : forall {i r} -> Name name i r -> Parser tok name i r
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
