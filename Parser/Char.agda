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
  data NT (nt : ParserType) : ParserType where
    lib'    : forall {i r} -> L.Nonterminal nt i r -> NT nt i r
    digit'  : NT nt _ ℕ
    number' : NT nt _ ℕ

Nonterminal : ParserType -> ParserType
Nonterminal = NT

module Combinators
         {nt : _}
         (lib : forall {i r} -> Nonterminal nt i r -> nt i r)
         where

  open L.Combinators (lib ∘₁ lib')

  digit : Parser C.Char nt _ ℕ
  digit = ! lib digit'

  number : Parser C.Char nt _ ℕ
  number = ! lib number'

  charLib : forall {i r} -> Nonterminal nt i r -> Parser C.Char nt i r
  charLib (lib' p) = library p
  charLib digit'   = 0 <$ sym '0'
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
  charLib number' = toNum <$> digit +
    where toNum = foldr (\n x -> 10 * x + n) 0 ∘ reverse
