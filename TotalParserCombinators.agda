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

import TotalParserCombinators.Applicative

-- The parser type, and its semantics.

import TotalParserCombinators.Parser
import TotalParserCombinators.Semantics

-- Some lemmas about the initial bag.

import TotalParserCombinators.InitialBag

-- A small library of derived parser combinators.

import TotalParserCombinators.Lib

-- A breadth-first backend.

import TotalParserCombinators.BreadthFirst

-- An alternative, coinductive definition of equality between parsers.

import TotalParserCombinators.CoinductiveEquality

-- The relation _≲_ is a partial order with respect to _≈_.

import TotalParserCombinators.PartialOrder

-- Language equivalence and parser equivalence are both congruences.

import TotalParserCombinators.Congruence
import TotalParserCombinators.Congruence.Sound

-- Proofs of various laws, for instance the monad laws.

import TotalParserCombinators.Laws

-- A proof showing that all functions of type List Bool → List R can
-- be realised using parser combinators (for any R, assuming that bag
-- equality is used for the lists of results).

import TotalParserCombinators.ExpressiveStrength

-- An alternative semantics.

import TotalParserCombinators.Semantics.Continuation

-- Simplification of parsers.

import TotalParserCombinators.Simplification

-- Definition of unambiguity.

import TotalParserCombinators.Unambiguity

-- An alternative definition of the parser type, which can lead to
-- less noisy definitions of parsers.

import TotalParserCombinators.LessNoisy

-- Some small examples, using both noisy and less noisy combinators.

import TotalParserCombinators.Examples.Noisy
import TotalParserCombinators.Examples.LessNoisy

-- An example: parsing PBM image files.

import TotalParserCombinators.Examples.PBM

-- An extended example: mixfix operator parsing.

import Mixfix

-- For code related to the paper "Structurally Recursive Descent
-- Parsing", developed together with Ulf Norell, see the following
-- module:

import StructurallyRecursiveDescentParsing
