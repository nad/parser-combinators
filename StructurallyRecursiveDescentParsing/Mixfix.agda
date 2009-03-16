------------------------------------------------------------------------
-- Parsing of mixfix operators
------------------------------------------------------------------------

-- This module defines a grammar for the precedence graph g.

open import StructurallyRecursiveDescentParsing.Mixfix.Expr

module StructurallyRecursiveDescentParsing.Mixfix
         (g : PrecedenceGraph)
         where

open import Coinduction
open import Data.List using (List; []; _∷_; foldr; foldl)
open import Data.Product
open import Data.Bool
open import Data.Function using (_$_; flip)
import Data.String as String

open import StructurallyRecursiveDescentParsing.Type
open import StructurallyRecursiveDescentParsing.Simple
open import StructurallyRecursiveDescentParsing.Mixfix.Fixity
import StructurallyRecursiveDescentParsing.Mixfix.Lib as Lib
open Lib String.decSetoid

-- The following definition uses a lexicographic combination of
-- guarded corecursion and structural recursion. The only "corecursive
-- call", where the size of the inductive input can increase
-- arbitrarily, is the use of expr in the expression ♯₁ expr.

mutual

  -- Expressions.

  expr : ParserProg false Expr
  expr = nodes g

  -- Expressions corresponding to zero or more nodes in the precedence
  -- graph: operator applications where the outermost operator has one
  -- of the precedences ps. The graph g is used for internal
  -- expressions.

  nodes : PrecedenceGraph → ParserProg false Expr
  nodes []       = fail
  nodes (p ∷ ps) = node p ∣ nodes ps

  -- Expressions corresponding to one node in the precedence graph:
  -- operator applications where the outermost operator has
  -- precedence p. The graph g is used for internal expressions.

  node : PrecedenceTree → ParserProg false Expr
  node (precedence ops ps) =
       ⟪_⟫              <$>      [ closed   ]
    ∣ _⟨_⟩_             <$>  ↑ ⊛ [ infx non ] ⊛ ↑
    ∣ flip (foldr _$_)  <$>      preRight +   ⊛ ↑
    ∣ foldl (flip _$_)  <$>  ↑ ⊛ postLeft +
    where
    -- [ fix ] parses the internal parts of operators with the
    -- current precedence level and fixity fix.
    [_] = λ (fix : Fixity) → internals (ops fix)

    -- Operator applications where the outermost operator binds
    -- tighter than the current precedence level.
    ↑ = nodes ps

    -- Right associative and prefix operators.
    preRight =  ⟪_⟩_ <$> [ prefx ]
             ∣ _⟨_⟩_ <$> ↑ ⊛ [ infx right ]

    -- Left associative and postfix operators.
    postLeft = flip _⟨_⟫                   <$> [ postfx ]
             ∣ (λ op e₂ e₁ → e₁ ⟨ op ⟩ e₂) <$> [ infx left ] ⊛ ↑

  -- Internal parts (all name parts plus internal expressions) of
  -- operators of the given precedence and fixity.

  internals : ∀ {fix} →
              List (∃ (Operator fix)) → ParserProg false (Internal fix)
  internals []               = fail
  internals ((_ , op) ∷ ops) =
      _∙_ op <$> ((♯₁ expr) between nameParts op)
    ∣ internals ops

-- Expression parsers.

expression : Parser NamePart false Expr
expression = ⟦ expr ⟧

parseExpr : List NamePart → List Expr
parseExpr = parseComplete expression
