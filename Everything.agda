------------------------------------------------------------------------
-- A total parser combinator library
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
-- machine). There is a risk that the code has bitrotted.

-- import StructurallyRecursiveDescentParsing.Memoised
-- import StructurallyRecursiveDescentParsing.Memoised.Monad

-- A library of derived parser combinators.

import StructurallyRecursiveDescentParsing.Lib

-- A module which reexports the modules above.

import StructurallyRecursiveDescentParsing

-- Some small examples.

import StructurallyRecursiveDescentParsing.Examples

-- An example: parsing PBM image files.

import StructurallyRecursiveDescentParsing.PBM

-- An extended example: mixfix operator parsing.

import StructurallyRecursiveDescentParsing.Mixfix.Fixity
import StructurallyRecursiveDescentParsing.Mixfix.Expr
import StructurallyRecursiveDescentParsing.Mixfix
import StructurallyRecursiveDescentParsing.Mixfix.Example

-- Helper function(s).

import StructurallyRecursiveDescentParsing.Utilities
