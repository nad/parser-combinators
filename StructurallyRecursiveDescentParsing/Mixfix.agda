------------------------------------------------------------------------
-- Parsing of mixfix operators
------------------------------------------------------------------------

-- This module defines a grammar for the precedence graph g.

open import StructurallyRecursiveDescentParsing.Mixfix.Expr

module StructurallyRecursiveDescentParsing.Mixfix
         (g : PrecedenceGraph)
         where

import Data.Vec as Vec
import Data.List as List
open List using (List; []; _∷_; foldr; foldl)
import Data.Vec1 as Vec1
open Vec1 using (Vec₁)
open import Data.Product
open import Data.Bool
open import Data.Unit
open import Data.Nat
open import Data.Function hiding (_⟨_⟩_)
import Data.String as String

open import StructurallyRecursiveDescentParsing.Mixfix.Fixity
open import StructurallyRecursiveDescentParsing
open Token String.decSetoid

-- Note that, even though grammar below is not recursive, these
-- functions are (mutually). Fortunately the recursion is structural,
-- though. Note also that the reason for not using the implementation
--
--   grammar (nodes ts) = choiceMap (λ t → ! node t) ts
--
-- is that this would lead to a definition of node-corners which
-- was not structurally recursive.

nodes-corners : PrecedenceGraph → Corners
nodes-corners []       = _
nodes-corners (p ∷ ps) = _

node-corners : PrecedenceTree → Corners
node-corners (precedence ops ps) = _

-- Nonterminals.

data NT : NonTerminalType where
  -- Expressions.
  expr : NT _ Expr

  -- Expressions corresponding to zero or more nodes in the precedence
  -- graph: operator applications where the outermost operator has one
  -- of the precedences ps. The graph g is used for internal
  -- expressions.
  nodes : (ps : PrecedenceGraph) → NT (false ◇ nodes-corners ps) Expr

  -- Expressions corresponding to one node in the precedence graph:
  -- operator applications where the outermost operator has
  -- precedence p. The graph g is used for internal expressions.
  node : (p : PrecedenceTree) → NT (false ◇ node-corners p) Expr

-- The parser type used in this module.

P : Index → Set → Set1
P = Parser NT NamePart

-- A vector containing parsers recognising the name parts of the
-- operator.

nameParts : ∀ {fix arity} → Operator fix arity →
            Vec₁ (P _ NamePart) (1 + arity)
nameParts (operator ns) = Vec1.map₀₁ theToken ns

-- Internal parts (all name parts plus internal expressions) of
-- operators of the given precedence and fixity.

internal : ∀ {fix} (ops : List (∃ (Operator fix))) → P _ (Internal fix)
internal =
  choiceMap (λ op' → let op = proj₂ op' in
                     _∙_ op <$> (! expr between nameParts op))

-- The grammar.

grammar : Grammar NT NamePart
grammar expr                       = ! (nodes g)
grammar (nodes [])                 = fail
grammar (nodes (p ∷ ps))           = ! (node p) ∣ ! (nodes ps)
grammar (node (precedence ops ps)) =
     ⟪_⟫              <$>      [ closed   ]
  ∣ _⟨_⟩_             <$>  ↑ ⊛ [ infx non ] ⊛ ↑
  ∣ flip (foldr _$_)  <$>      preRight +   ⊛ ↑
  ∣ foldl (flip _$_)  <$>  ↑ ⊛ postLeft +
  where
  -- [ fix ] parses the internal parts of operators with the
  -- current precedence level and fixity fix.
  [_] = λ (fix : Fixity) → internal (ops fix)

  -- Operator applications where the outermost operator binds
  -- tighter than the current precedence level.
  ↑ = ! (nodes ps)

  -- Right associative and prefix operators.
  preRight =  ⟪_⟩_ <$> [ prefx ]
           ∣ _⟨_⟩_ <$> ↑ ⊛ [ infx right ]

  -- Left associative and postfix operators.
  postLeft = flip _⟨_⟫                   <$> [ postfx ]
           ∣ (λ op e₂ e₁ → e₁ ⟨ op ⟩ e₂) <$> [ infx left ] ⊛ ↑

-- Expression parsers.

expression : ∀ {NT} → Parser NT NamePart _ Expr
expression = ⟦ ! expr ⟧ grammar

parseExpr : List NamePart → List Expr
parseExpr = parseComplete grammar (! expr)
