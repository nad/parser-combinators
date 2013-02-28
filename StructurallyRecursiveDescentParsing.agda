------------------------------------------------------------------------
-- Code related to the paper draft "Structurally Recursive Descent
-- Parsing"
--
-- Nils Anders Danielsson and Ulf Norell
------------------------------------------------------------------------

module StructurallyRecursiveDescentParsing where

-- The code presented here is not identical to that in the paper; it
-- has evolved.

-- Parser type indices.

import StructurallyRecursiveDescentParsing.Index

-- Parsers containing non-terminals, and grammars using such parsers.

import StructurallyRecursiveDescentParsing.Grammar

-- A library of derived parser combinators.

import StructurallyRecursiveDescentParsing.Lib

-- Some small examples.
--
-- This module is not included, because it type-checks really slowly
-- (if at all) using the current version of Agda (Feb 2013).

-- import StructurallyRecursiveDescentParsing.Examples

-- An example: parsing PBM image files.
--
-- This module is not included, because it type-checks really slowly
-- (if at all) using the current version of Agda (Oct 2011).

-- import StructurallyRecursiveDescentParsing.PBM

-- A depth-first backend.

import StructurallyRecursiveDescentParsing.DepthFirst

-- The backend does not work directly on the parsers in
-- StructurallyRecursiveDescentParsing.Grammar. The following
-- simplified parsers are used instead. The function
-- StructurallyRecursiveDescentParsing.Grammar.⟦_⟧ turns parsers
-- containing non-terminals into simplified parsers.

import StructurallyRecursiveDescentParsing.Simplified
import StructurallyRecursiveDescentParsing.Simplified.Semantics
import StructurallyRecursiveDescentParsing.Simplified.Lemmas
