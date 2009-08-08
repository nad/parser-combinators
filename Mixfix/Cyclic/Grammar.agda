------------------------------------------------------------------------
-- Parsing of mixfix operators
------------------------------------------------------------------------

-- This module defines a grammar for the precedence graph g.

open import Mixfix.Cyclic.Expr as Expr

module Mixfix.Cyclic.Grammar (g : PrecedenceGraph) where

open import Coinduction
  using () renaming (∞₁ to ∞; ♯₁_ to ♯_; ♭₁ to ♭)
open import Data.Function using (flip; _$_)
open import Data.List using (List; []; _∷_)
open import Data.List.Any as Any using (here; there)
open Any.Membership-≡ using (_∈_)
open import Data.Product
open import Relation.Binary.PropositionalEquality

open PrecedenceGraph   g
open PrecedenceCorrect g

import StructurallyRecursiveDescentParsing.Parser as Parser
open import Mixfix.Fixity
open import Mixfix.Operator
open import Mixfix.Cyclic.Lib renaming (ParserProg to Parser)

-- The following definition uses a lexicographic combination of
-- guarded corecursion and structural recursion.

mutual

  -- Expressions.

  expr : ∞ (Parser (Expr anyPrecedence))
  expr = ♯ precs anyPrecedence

  -- Expressions corresponding to zero or more nodes in the precedence
  -- graph: operator applications where the outermost operator has one
  -- of the precedences ps. The graph g is used for internal
  -- expressions.

  precs : (ps : List Precedence) → Parser (Expr ps)
  precs []       = fail
  precs (p ∷ ps) = (λ e → here refl ∙ proj₂ e) <$> prec p
                 ∣ weakenE                     <$> precs ps

  -- Expressions corresponding to one node in the precedence graph:
  -- operator applications where the outermost operator has
  -- precedence p. The graph g is used for internal expressions.

  -- The code would be more readable if the delay constructors (♯_)
  -- could be omitted.

  prec : (p : Precedence) → Parser (∃ (ExprIn p))
  prec p = closedOps ∥ nonAssoc ∥ preRight ∥ postLeft ∥ fail
    module Prec where
    -- [ fix ] parses the internal parts of operators with the
    -- current precedence level and fixity fix.
    [_] = λ (fix : Fixity) → inner (ops p fix)

    -- Operator applications where the outermost operator binds
    -- tighter than the current precedence level.
    p↑ = precs (↑ p)

    -- Closed operators.
    closedOps : Parser (ExprIn p non)
    closedOps = ⟪_⟫ <$> [ closed ]

    -- Non-associative infix operators.
    nonAssoc : Parser (ExprIn p non)
    nonAssoc = (♯ (♯ _⟨_⟩_ <$> p↑) ⊛ (♯ [ infx non ])) ⊛ (♯ p↑)

    -- Right associative and prefix operators.
    preRight : Parser (ExprIn p right)
    preRight =
      (♯ (     ⟪_⟩_  <$>          [ prefx      ]
         ∣ (♯ _⟨_⟩ʳ_ <$> p↑) ⊛ (♯ [ infx right ])
         ))
      ⊛
      (♯ ( similar <$> preRight
         ∣ tighter <$> p↑
         ))

    -- Left associative and postfix operators.
    postLeft : Parser (ExprIn p left)
    postLeft =
      (♯ flip _$_
         <$>
         ( similar <$> postLeft
         ∣ tighter <$> p↑
         ))
      ⊛
      (♯ (    (λ op    e₁ → e₁ ⟨ op ⟫    ) <$> [ postfx    ]
         ∣ (♯ (λ op e₂ e₁ → e₁ ⟨ op ⟩ˡ e₂) <$> [ infx left ]) ⊛ (♯ p↑)
         ))

  -- Internal parts (all name parts plus internal expressions) of
  -- operators of the given precedence and fixity.

  inner : ∀ {fix} (ops : List (∃ (Operator fix))) →
          Parser (Inner ops)
  inner []               = fail
  inner ((_ , op) ∷ ops) =
      (λ args → here refl ∙ args) <$> (expr between nameParts op)
    ∣ weakenI                     <$> inner ops

-- Expression parsers.

expression : Parser.Parser NamePart (Expr anyPrecedence) []
expression = ⟦ ♭ expr ⟧
