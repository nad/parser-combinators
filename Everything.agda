------------------------------------------------------------------------
-- A total parser combinator library
------------------------------------------------------------------------

module Everything where

-- Helper functions related to coinduction.

import StructurallyRecursiveDescentParsing.Coinduction

-- The parser type, along with its semantics

import StructurallyRecursiveDescentParsing.Parser
import StructurallyRecursiveDescentParsing.Parser.Semantics

-- Definition of unambiguity.

import StructurallyRecursiveDescentParsing.Unambiguity

-- A simplified parser type.

import StructurallyRecursiveDescentParsing.Simplified

-- Parser type indices, used by the grammars.

import StructurallyRecursiveDescentParsing.Index

-- Grammars.

import StructurallyRecursiveDescentParsing.Grammar

-- A simple backend.

import StructurallyRecursiveDescentParsing.Simple

-- A library of derived parser combinators.

import StructurallyRecursiveDescentParsing.Lib

-- A module which reexports some of the modules above.

import StructurallyRecursiveDescentParsing

-- Some small examples.

import StructurallyRecursiveDescentParsing.Examples

-- An example: parsing PBM image files.

import StructurallyRecursiveDescentParsing.PBM

-- An extended example: mixfix operator parsing.

import StructurallyRecursiveDescentParsing.Mixfix.Fixity
import StructurallyRecursiveDescentParsing.Mixfix.Expr
import StructurallyRecursiveDescentParsing.Mixfix.Lib
import StructurallyRecursiveDescentParsing.Mixfix
import StructurallyRecursiveDescentParsing.Mixfix.Show
import StructurallyRecursiveDescentParsing.Mixfix.Example
