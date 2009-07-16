------------------------------------------------------------------------
-- A total parser combinator library
--
-- Nils Anders Danielsson and Ulf Norell
------------------------------------------------------------------------

module StructurallyRecursiveDescentParsing.README where

------------------------------------------------------------------------
-- The modules most related to the paper "Mixing Induction and
-- Coinduction"

-- Helper functions related to coinduction.

import StructurallyRecursiveDescentParsing.Coinduction

-- The parser type, along with its semantics.

import StructurallyRecursiveDescentParsing.Parser
import StructurallyRecursiveDescentParsing.Parser.Semantics

-- A simplified parser type, along with its semantics.

import StructurallyRecursiveDescentParsing.Simplified
import StructurallyRecursiveDescentParsing.Simplified.Semantics
import StructurallyRecursiveDescentParsing.Simplified.Lemmas

-- A breadth-first backend. The backend uses code which simplifies
-- parsers.

import StructurallyRecursiveDescentParsing.Backend.BreadthFirst
import StructurallyRecursiveDescentParsing.Backend.Simplification

-- An extended example: mixfix operator parsing.

import StructurallyRecursiveDescentParsing.Mixfix.Fixity
import StructurallyRecursiveDescentParsing.Mixfix.Expr
import StructurallyRecursiveDescentParsing.Mixfix.Lib
import StructurallyRecursiveDescentParsing.Mixfix
import StructurallyRecursiveDescentParsing.Mixfix.Show
import StructurallyRecursiveDescentParsing.Mixfix.Example

------------------------------------------------------------------------
-- Remaining modules

-- Definition of unambiguity.

import StructurallyRecursiveDescentParsing.Unambiguity

-- Parser type indices, used by the grammars below.

import StructurallyRecursiveDescentParsing.Index

-- Grammars.

import StructurallyRecursiveDescentParsing.Grammar

-- A depth-first backend.

import StructurallyRecursiveDescentParsing.Backend.DepthFirst

-- A library of derived parser combinators.

import StructurallyRecursiveDescentParsing.Lib

-- A module which reexports some of the modules above.

import StructurallyRecursiveDescentParsing

-- Some small examples.

import StructurallyRecursiveDescentParsing.Examples

-- An example: parsing PBM image files.

import StructurallyRecursiveDescentParsing.PBM
