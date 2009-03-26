------------------------------------------------------------------------
-- Parsing of mixfix operators
------------------------------------------------------------------------

-- This module defines a grammar for the precedence graph g.

open import StructurallyRecursiveDescentParsing.Mixfix.Expr as Expr

module StructurallyRecursiveDescentParsing.Mixfix
         (g : PrecedenceGraph)
         where

open import Coinduction
open import Data.List using (List; []; _∷_; _∈_; here; there)
open import Data.List.NonEmpty using (foldr; foldl)
open import Data.Product
open import Data.Bool
open import Data.Function using (flip)
import Data.String as String

open Expr.PrecedenceCorrect g

open import StructurallyRecursiveDescentParsing.Type
open import StructurallyRecursiveDescentParsing.Simple
open import StructurallyRecursiveDescentParsing.Mixfix.Fixity
import StructurallyRecursiveDescentParsing.Mixfix.Lib as Lib
open Lib String.decSetoid

-- The following definition uses a lexicographic combination of
-- guarded corecursion and structural recursion. The only "corecursive
-- call", where the size of the inductive input can increase
-- arbitrarily, is the one in expr.

mutual

  -- Expressions.

  expr : ∞₁ (ParserProg false (Expr g))
  expr = ♯₁ nodes g

  -- Expressions corresponding to zero or more nodes in the precedence
  -- graph: operator applications where the outermost operator has one
  -- of the precedences ps. The graph g is used for internal
  -- expressions.

  nodes : (ps : PrecedenceGraph) → ParserProg false (Expr ps)
  nodes []       = fail
  nodes (p ∷ ps) = (λ e → here ∙ proj₂ e) <$> node p
                 ∣ weakenE                <$> nodes ps

  -- Expressions corresponding to one node in the precedence graph:
  -- operator applications where the outermost operator has
  -- precedence p. The graph g is used for internal expressions.

  node : (p : Precedence) → ParserProg false (∃ (ExprIn p))
  node (precedence ops sucs) =
      ⟪_⟫    <$>      [ closed   ]
    ∥ _⟨_⟩_  <$>  ↟ ⊛ [ infx non ] ⊛ ↟
    ∥ appʳ   <$>      preRight +   ⊛ ↟
    ∥ appˡ   <$>  ↟ ⊛ postLeft +
    ∥ fail
    module Node where
    -- [ fix ] parses the internal parts of operators with the
    -- current precedence level and fixity fix.
    [_] = λ (fix : Fixity) → inner (ops fix)

    -- Operator applications where the outermost operator binds
    -- tighter than the current precedence level.
    ↟ = nodes sucs

    -- Right associative and prefix operators.
    preRight =  ⟪_⟩_  <$> [ prefx ]
             ∣ _⟨_⟩ʳ_ <$> ↟ ⊛ [ infx right ]

    -- Left associative and postfix operators.
    postLeft = flip _⟨_⟫                    <$> [ postfx ]
             ∣ (λ op e₂ e₁ → e₁ ⟨ op ⟩ˡ e₂) <$> [ infx left ] ⊛ ↟

    -- Post-processing for the non-empty lists returned by _+.
    appʳ = λ fs e → foldr (λ f e → f (similar e)) (λ f → f (tighter e)) fs
    appˡ = λ e fs → foldl (λ e f → f (similar e)) (λ f → f (tighter e)) fs

  -- Internal parts (all name parts plus internal expressions) of
  -- operators of the given precedence and fixity.

  inner : ∀ {fix} (ops : List (∃ (Operator fix))) →
          ParserProg false (Inner ops)
  inner []               = fail
  inner ((_ , op) ∷ ops) =
      _∙_ here <$> (expr between nameParts op)
    ∣ weakenI  <$> inner ops

-- Expression parsers.

expression : Parser NamePart false (Expr g)
expression = ⟦ ♭₁ expr ⟧

parseExpr : List NamePart → List (Expr g)
parseExpr = parseComplete expression
