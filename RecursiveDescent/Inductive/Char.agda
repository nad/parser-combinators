------------------------------------------------------------------------
-- Some character parsers
------------------------------------------------------------------------

-- This code also illustrates how a library can make use of another
-- library.

module RecursiveDescent.Inductive.Char where

open import RecursiveDescent.Inductive
open import Data.Unit
open import Data.Nat
open import Data.Bool
import Data.Char as C
open C using (Char; _==_)
open import Data.List
open import Data.Function hiding (_$_)
import RecursiveDescent.Inductive.Token
open import RecursiveDescent.Inductive.SimpleLib
import RecursiveDescent.Inductive.Lib as Lib
private
  module L = Lib Char

-- Some parameterised parsers.

private
  data NT (nt : ParserType) : ParserType where
    lib'        : forall {i r} -> L.Nonterminal nt i r -> NT nt i r
    digit'      : NT nt _ ℕ
    number'     : NT nt _ ℕ
    whitespace' : NT nt _ ⊤

Nonterminal : ParserType -> ParserType
Nonterminal = NT

module Combinators
         {nt : _}
         (lib : forall {i r} -> Nonterminal nt i r -> nt i r)
         where

  open L.Combinators (lib ∘₁ lib')

  digit : Parser Char nt _ ℕ
  digit = ! lib digit'

  number : Parser Char nt _ ℕ
  number = ! lib number'

  whitespace : Parser Char nt _ ⊤
  whitespace = ! lib whitespace'

  open RecursiveDescent.Inductive.Token C.decSetoid

  charLib : forall {i r} -> Nonterminal nt i r -> Parser Char nt i r
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
  charLib number' = toNum <$> digit +
    where toNum = foldr (\n x -> 10 * x + n) 0 ∘ reverse
  -- whitespace recognises an incomplete but useful list of whitespace
  -- characters.
  charLib whitespace' = sat' isSpace
    where
    isSpace = \c ->
      (c == ' ') ∨ (c == '\t') ∨ (c == '\n') ∨ (c == '\r')
