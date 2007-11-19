module Parser.Lib (tok : Set) where

open import Parser
open import Data.Bool

-- Some parameterised parsers.

private
  data Name' (name : ParserType) : ParserType where
    many  :  forall {d}
          -> Parser tok name false d
          -> Name' name _ _
    many₁ :  forall {d}
          -> Parser tok name false d
          -> Name' name _ _

Name : ParserType -> ParserType
Name = Name'

module Combinators
         {name : _}
         (lib : forall {e d} -> Name name e d -> name e d)
         where

  infix 55 _⋆ _+

  _⋆ : forall {d} -> Parser tok name false d -> Parser tok name _ _
  _⋆ p = ! lib (many p)

  _+ : forall {d} -> Parser tok name false d -> Parser tok name _ _
  _+ p = ! lib (many₁ p)

  library : forall {e d} -> Name name e d -> Parser tok name e d
  library (many  p) = ε ∣ p +
  library (many₁ p) = p · p ⋆
