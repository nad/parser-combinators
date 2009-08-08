------------------------------------------------------------------------
-- Acyclic precedence graphs
------------------------------------------------------------------------

module Mixfix.Acyclic.PrecedenceGraph where

open import Data.List
open import Data.Product

open import Mixfix.Fixity
open import Mixfix.Operator
open import Mixfix.Expr

-- Precedence graphs are represented by their unfoldings as forests
-- (one tree for every node in the graph). This does not take into
-- account the sharing of the precedence graphs, but this code is
-- not aimed at efficiency.

-- Precedence trees.

data Precedence : Set where
  precedence : (o : (fix : Fixity) → List (∃ (Operator fix)))
               (s : List Precedence) →
               Precedence

-- Precedence forests.

PrecedenceGraph : Set
PrecedenceGraph = List Precedence

-- The operators of the given precedence.

ops : Precedence → (fix : Fixity) → List (∃ (Operator fix))
ops (precedence o s) = o

-- The immediate successors of the precedence level.

↑ : Precedence → List Precedence
↑ (precedence o s) = s

-- Acyclic precedence graphs.

acyclic : PrecedenceGraphInterface
acyclic = record
  { PrecedenceGraph = PrecedenceGraph
  ; Precedence      = λ _ → Precedence
  ; ops             = λ _ → ops
  ; ↑               = λ _ → ↑
  ; anyPrecedence   = λ g → g
  }
