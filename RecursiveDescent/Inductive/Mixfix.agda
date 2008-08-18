------------------------------------------------------------------------
-- Parsing of mixfix operators
------------------------------------------------------------------------

module RecursiveDescent.Inductive.Mixfix where

import Data.Graph.Acyclic as G
open G using (_[_])
import Data.Vec as Vec
import Data.List as List
open List using ([]; _∷_; foldr; foldl) renaming ([_] to List)
import Data.Vec1 as Vec1
open Vec1 using (Vec₁)
open import Data.Product renaming (_,_ to pair)
open import Data.Product.Record using (_,_)
open import Data.Bool
open import Data.Unit
open import Data.Nat
open import Data.Function
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
  expr : forall {n} (g : PrecedenceGraph n) -> NT _ Expr

open Lib.Combinators NamePart lib

-- A vector containing parsers recognising the name parts of the
-- operator.

nameParts : forall {fa m} -> Operator fa m ->
            Vec₁ (Parser NamePart NT _ NamePart) (1 + m)
nameParts (oper ns) = Vec1.map₀₁ sym ns

-- Internal parts (all name parts plus internal expressions) of
-- operators of the given precedence, fixity and associativity.

internal : forall {n} (g : PrecedenceGraph n)
           (p : Precedence n) (fa : FA) ->
           Parser NamePart NT _ (∃ (OpApp fa))
internal g p fa =
  choiceMap (\op -> (\args -> , (proj₂ op ⟨ args ⟩)) <$>
                      (! expr g between nameParts (proj₂ op))) ops
  where
  -- All matching operators.
  ops = List.gfilter (hasFA fa) (G.label $ G.head $ g [ p ])

-- The code below represents precedences using trees where the root is
-- a precedence level and the children contain all higher precedence
-- levels. This representation ensures that the code is structurally
-- recursive.

PrecedenceTree : ℕ -> Set
PrecedenceTree n = G.Tree (Precedence n × List (∃₂ Operator)) ⊤

module Dummy {n} (g : PrecedenceGraph n) where

  precs-corners : List (⊤ × PrecedenceTree n) -> Corners
  precs-corners []       = _
  precs-corners (t ∷ ts) = _

  prec-corners : ⊤ × PrecedenceTree n -> Corners
  prec-corners (pair _ (G.node (pair p ops) ts)) = _

  mutual

    -- Operator applications where the outermost operator has one of
    -- the given precedences. (Reason for not using choiceMap: to
    -- please the termination checker.)

    precs : (ts : List (⊤ × PrecedenceTree n)) ->
            Parser NamePart NT (false , precs-corners ts) Expr
    precs []       = fail
    precs (t ∷ ts) = prec t ∣ precs ts

    -- Operator applications where the outermost operator has the given
    -- precedence.

    prec : (t : ⊤ × PrecedenceTree n) ->
           Parser NamePart NT (false , prec-corners t) Expr
    prec (pair _ (G.node (pair p ops) ts)) =
        app                <$>  ⟦ closed ⟧
      ∣ flip (foldr app)   <$>  ⟦ prefx ⟧ + ⊛ ↑
      ∣ foldl (flip app)   <$>  ↑ ⊛ ⟦ postfx ⟧ +
      ∣ flip app           <$>  ↑ ⊛ ⟦ infx non ⟧ ⊛ ↑
      ∣ flip (foldr appr)  <$>  (↑ ⊗ ⟦ infx right ⟧) + ⊛ ↑
      ∣ foldl appl         <$>  ↑ ⊛ (⟦ infx left ⟧ ⊗ ↑) +
      where
      -- ⟦ fa ⟧ parses the internal parts of operators with the
      -- current precedence level and fixity/associativity fa.
      ⟦_⟧ = internal g p

      -- Operator applications where the outermost operator binds
      -- tighter than the current precedence level.
      ↑ = precs ts

      appl = \e₁ ope₂ -> app (proj₁ ope₂) e₁ (proj₂ ope₂)
      appr = \e₁op e₂ -> app (proj₂ e₁op) (proj₁ e₁op) e₂

open Dummy public

-- The grammar.

grammar : Grammar NamePart NT
grammar (lib p)  = library p
grammar (expr g) =
  precs g (Vec.toList $ Vec.map ,_ $ G.toForest $ G.number g)