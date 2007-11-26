------------------------------------------------------------------------
-- Some character parsers
------------------------------------------------------------------------

-- This code also illustrates how a library can make use of another
-- library.

module Parser.Char where

open import Parser
open import Data.Nat
import Data.Char as C
open import Data.List
open import Data.Function hiding (_$_)
import Parser.Lib as Lib
private
  module L = Lib C.Char

-- Some parameterised parsers.

private
  data Name' (name : ParserType) : ParserType where
    lib'    : forall {i r} -> L.Name name i r -> Name' name i r
    digit'  : Name' name _ ℕ
    number' : Name' name _ ℕ

Name : ParserType -> ParserType
Name = Name'

module Combinators
         {name : _}
         (lib : forall {i r} -> Name name i r -> name i r)
         where

  open module LC = L.Combinators (lib ∘₁ lib')

  digit : Parser C.Char name _ ℕ
  digit = ! lib digit'

  number : Parser C.Char name _ ℕ
  number = ! lib number'

  charLib : forall {i r} -> Name name i r -> Parser C.Char name i r
  charLib (lib' p) = library p
  charLib digit'   = 0 <$ token '0'
                   ∣ 1 <$ token '1'
                   ∣ 2 <$ token '2'
                   ∣ 3 <$ token '3'
                   ∣ 4 <$ token '4'
                   ∣ 5 <$ token '5'
                   ∣ 6 <$ token '6'
                   ∣ 7 <$ token '7'
                   ∣ 8 <$ token '8'
                   ∣ 9 <$ token '9'
    where open module T = Token C.decSetoid
  charLib number' = toNum $ digit +
    where toNum = foldr (\n x -> 10 * x + n) 0 ∘ reverse
