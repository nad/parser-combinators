------------------------------------------------------------------------
-- A total parser combinator library
------------------------------------------------------------------------

-- This module just reexports some other modules, to make them easier
-- to use. See Everything.agda for an overview of the different
-- modules.

module StructurallyRecursiveDescentParsing where

-- Parser indices.

open import StructurallyRecursiveDescentParsing.Index public

-- Grammars.

open import StructurallyRecursiveDescentParsing.Grammar public

-- Derived parser combinators.

open import StructurallyRecursiveDescentParsing.Lib public

-- A depth-first parser backend.

open import StructurallyRecursiveDescentParsing.Backend.DepthFirst
  public
