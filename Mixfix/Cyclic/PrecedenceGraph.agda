------------------------------------------------------------------------
-- Potentially cyclic precedence graphs
------------------------------------------------------------------------

module Mixfix.Cyclic.PrecedenceGraph where

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Vec as Vec using (allFin)
open import Data.List using (List)
open import Data.Product using (∃)

open import Mixfix.Fixity
open import Mixfix.Operator
open import Mixfix.Expr hiding (module PrecedenceGraph)

-- Precedence graphs are represented by the number of precedence
-- levels, plus functions mapping node identifiers (precedences) to
-- node contents and successor precedences.

record PrecedenceGraph : Set where
  field
    -- The number of precedence levels.
    levels : ℕ

  -- Precedence levels.
  Precedence : Set
  Precedence = Fin levels

  field
    -- The precedence level's operators.
    ops : Precedence → (fix : Fixity) → List (∃ (Operator fix))

    -- The immediate successors of the precedence level.
    ↑ : Precedence → List Precedence

  -- All precedence levels.
  anyPrecedence : List Precedence
  anyPrecedence = Vec.toList (allFin levels)

-- Potentially cyclic precedence graphs.

cyclic : PrecedenceGraphInterface
cyclic = record
  { PrecedenceGraph = PrecedenceGraph
  ; Precedence      = PrecedenceGraph.Precedence
  ; ops             = PrecedenceGraph.ops
  ; ↑               = PrecedenceGraph.↑
  ; anyPrecedence   = PrecedenceGraph.anyPrecedence
  }
