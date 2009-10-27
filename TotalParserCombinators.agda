------------------------------------------------------------------------
-- A total parser combinator library
------------------------------------------------------------------------

-- This module just reexports some other modules, to make them easier
-- to use. See Everything.agda for an overview of the different
-- modules.

module TotalParserCombinators where

-- Parser indices.

open import TotalParserCombinators.Index public

-- Grammars.

open import TotalParserCombinators.Grammar public

-- Derived parser combinators.

open import TotalParserCombinators.Lib public

-- A depth-first parser backend.

open import TotalParserCombinators.Backend.DepthFirst
  public
