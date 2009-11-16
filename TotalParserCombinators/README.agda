------------------------------------------------------------------------
-- A total parser combinator library
--
-- Nils Anders Danielsson and Ulf Norell
------------------------------------------------------------------------

module TotalParserCombinators.README where

------------------------------------------------------------------------
-- The modules most related to the paper "Mixing Induction and
-- Coinduction"

-- Helper functions related to coinduction.

import TotalParserCombinators.Coinduction

-- The parser type, along with its semantics.

import TotalParserCombinators.Parser
import TotalParserCombinators.Parser.Semantics

-- A breadth-first backend. The backend uses code which simplifies
-- parsers.

import TotalParserCombinators.Backend.BreadthFirst
import TotalParserCombinators.Backend.Simplification

-- An extended example: mixfix operator parsing.

import Mixfix.README

------------------------------------------------------------------------
-- Remaining modules

-- A proof showing that all functions of type List Bool → List R can
-- be realised using parser combinators (for any R).

import TotalParserCombinators.Parser.ExpressiveStrength

-- An alternative, coinductive definition of equality between parsers.

import TotalParserCombinators.Parser.CoinductiveEquality

-- A very small library of derived parser combinators.

import TotalParserCombinators.Parser.Lib

-- Definition of unambiguity.

import TotalParserCombinators.Unambiguity

-- A simplified parser type, along with its semantics.

import TotalParserCombinators.Simplified
import TotalParserCombinators.Simplified.Semantics
import TotalParserCombinators.Simplified.Lemmas

-- Parser type indices, used by the grammars below.

import TotalParserCombinators.Index

-- Grammars.

import TotalParserCombinators.Grammar

-- A depth-first backend.

import TotalParserCombinators.Backend.DepthFirst

-- A library of derived parser combinators.

import TotalParserCombinators.Lib

-- A module which reexports some of the modules above.

import TotalParserCombinators

-- Some small examples.

import TotalParserCombinators.Examples

-- An example: parsing PBM image files.

import TotalParserCombinators.PBM
