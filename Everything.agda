------------------------------------------------------------------------
-- Imports all modules, so that it is easy to check if everything type
-- checks
------------------------------------------------------------------------

module Everything where

-- The parser type indices.

import StructurallyRecursiveDescentParsing.Index

-- The parser type.

import StructurallyRecursiveDescentParsing.Type

-- A simple backend.

import StructurallyRecursiveDescentParsing.Simple

-- An optimised backend. Unfortunately Agda is currently too slow to
-- be able to comfortably type check these modules (at least on my
-- machine).

-- import StructurallyRecursiveDescentParsing.Memoised
-- import StructurallyRecursiveDescentParsing.Memoised.Monad

-- A library of derived parser combinators.

import StructurallyRecursiveDescentParsing.Lib

-- Some small examples.

import StructurallyRecursiveDescentParsing.Examples

-- An example: parsing of PBM image files.

import StructurallyRecursiveDescentParsing.PBM

-- An extended example: mixfix operator parsing.

import StructurallyRecursiveDescentParsing.Mixfix.Fixity
import StructurallyRecursiveDescentParsing.Mixfix.Expr
import StructurallyRecursiveDescentParsing.Mixfix
import StructurallyRecursiveDescentParsing.Mixfix.Example

-- Less interesting modules.

import StructurallyRecursiveDescentParsing
import StructurallyRecursiveDescentParsing.Utilities
