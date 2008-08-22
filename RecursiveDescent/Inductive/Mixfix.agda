------------------------------------------------------------------------
-- Parsing of mixfix operators
------------------------------------------------------------------------

module RecursiveDescent.Inductive.Mixfix where

import Data.Vec as Vec
import Data.List as List
open List using (List; []; _∷_; foldr; foldl)
import Data.Vec1 as Vec1
open Vec1 using (Vec₁)
open import Data.Product renaming (_,_ to pair)
open import Data.Product.Record using (_,_)
open import Data.Bool
open import Data.Unit
open import Data.Nat
open import Data.Function hiding (_⟨_⟩_)
import Data.String as String

open import RecursiveDescent.Inductive.Mixfix.FA
open import RecursiveDescent.Inductive.Mixfix.Expr
open import RecursiveDescent.Index
open import RecursiveDescent.Inductive
open import RecursiveDescent.Inductive.SimpleLib
import RecursiveDescent.Inductive.Lib as Lib
import RecursiveDescent.Inductive.Token as Tok
open Tok String.decSetoid

-- Nonterminals.

data NT : ParserType where
  lib : forall {i r} (p : Lib.Nonterminal NamePart NT i r) -> NT _ r

  -- Expressions.
  expr : (g : PrecedenceGraph) -> NT _ Expr

open Lib.Combinators NamePart lib

-- A vector containing parsers recognising the name parts of the
-- operator.

nameParts : forall {fix arity} -> Operator fix arity ->
            Vec₁ (Parser NamePart NT _ NamePart) (1 + arity)
nameParts (operator ns) = Vec1.map₀₁ sym ns

-- Internal parts (all name parts plus internal expressions) of
-- operators of the given precedence, fixity and associativity.

internal : (g : PrecedenceGraph)
           (ops : List (∃₂ Operator))
           (fix : Fixity) ->
           Parser NamePart NT _ (Internal fix)
internal g ops fix =
  choiceMap (\op -> (\args -> proj₂ op ∙ args) <$>
                      (! expr g between nameParts (proj₂ op)))
            (List.gfilter (hasFixity fix) ops)

module Dummy (g : PrecedenceGraph) where

  precs-corners : PrecedenceGraph -> Corners
  precs-corners []       = _
  precs-corners (t ∷ ts) = _

  prec-corners : PrecedenceTree -> Corners
  prec-corners (node ops ts) = _

  mutual

    -- Operator applications where the outermost operator has one of
    -- the given precedences. (Reason for not using choiceMap: to
    -- please the termination checker.)

    precs : (ts : PrecedenceGraph) ->
            Parser NamePart NT (false , precs-corners ts) Expr
    precs []       = fail
    precs (t ∷ ts) = prec t ∣ precs ts

    -- Operator applications where the outermost operator has the given
    -- precedence.

    prec : (t : PrecedenceTree) ->
           Parser NamePart NT (false , prec-corners t) Expr
    prec (node ops ts) =
        ⟪_⟫                <$>  ⟦ closed ⟧
      ∣ flip (foldr ⟪_⟩_)  <$>  ⟦ prefx ⟧ + ⊛ ↑
      ∣ foldl _⟨_⟫         <$>  ↑ ⊛ ⟦ postfx ⟧ +
      ∣ _⟨_⟩_              <$>  ↑ ⊛ ⟦ infx non ⟧ ⊛ ↑
      ∣ flip (foldr _$_)   <$>  (_⟨_⟩_ <$> ↑ ⊛ ⟦ infx right ⟧) + ⊛ ↑
      ∣ foldl (flip _$_)   <$>  ↑ ⊛ (⟨_⟩_,_ <$> ⟦ infx left ⟧ ⊛ ↑) +
      where
      ⟨_⟩_,_ = \op e₂ e₁ -> e₁ ⟨ op ⟩ e₂

      -- ⟦ fix ⟧ parses the internal parts of operators with the
      -- current precedence level and fixity fix.
      ⟦_⟧ = internal g ops

      -- Operator applications where the outermost operator binds
      -- tighter than the current precedence level.
      ↑ = precs ts

open Dummy public

-- The grammar.

grammar : Grammar NamePart NT
grammar (lib p)  = library p
grammar (expr g) = precs g g
