------------------------------------------------------------------------
-- A total parser combinator library
--
-- Nils Anders Danielsson
------------------------------------------------------------------------

module TotalParserCombinators where

-- Check out TotalRecognisers for an introduction to the ideas used
-- below in the simplified setting of recognisers (as opposed to
-- parsers).

import TotalRecognisers

-- Helper functions related to coinduction.

import TotalParserCombinators.Coinduction

-- An alternative implementation of _⊛_ for lists, along with some
-- lemmas.

-- The parser type, and its semantics.

import TotalParserCombinators.Parser
import TotalParserCombinators.Semantics

-- A very small library of derived parser combinators.

import TotalParserCombinators.Lib

-- A breadth-first backend.

import TotalParserCombinators.BreadthFirst

-- A proof showing that the breadth-first backend does not introduce
-- any unneeded ambiguity. This proof currently contains some
-- postulates. It should be easy to remove these postulates once (what
-- is believed to be) a bug in Agda is fixed.

import TotalParserCombinators.BreadthFirst.LeftInverse

-- An alternative, coinductive definition of equality between parsers.

import TotalParserCombinators.CoinductiveEquality

-- Proofs of various laws, for instance the monad laws.

import TotalParserCombinators.Laws

-- A proof showing that all functions of type List Bool → List R can
-- be realised using parser combinators (for any R, assuming that set
-- equality is used for the lists of results).

import TotalParserCombinators.ExpressiveStrength

-- Simplification of parsers.

import TotalParserCombinators.Simplification

-- Definition of unambiguity.

import TotalParserCombinators.Unambiguity

-- An extended example: mixfix operator parsing.

import Mixfix

-- If you are only interested in code related to the paper "Mixing
-- Induction and Coinduction", see the following module:

import TotalParserCombinators.MixingInductionAndCoinduction

-- For code related to the paper "Structurally Recursive Descent
-- Parsing", developed together with Ulf Norell, see the following
-- module:

import StructurallyRecursiveDescentParsing
