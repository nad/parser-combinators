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

-- The parser type, and its semantics.

import TotalParserCombinators.Parser
import TotalParserCombinators.Semantics

-- Some lemmas about initial bags.

import TotalParserCombinators.InitialBag

-- A small library of derived parser combinators.

import TotalParserCombinators.Lib

-- A breadth-first backend, based on Brzozowski derivatives.

import TotalParserCombinators.BreadthFirst

-- An alternative, coinductive definition of equality between parsers.

import TotalParserCombinators.CoinductiveEquality

-- The relation _≲_ is a partial order with respect to _≈_.

import TotalParserCombinators.PartialOrder

-- Language equivalence and parser equivalence are both congruences.

import TotalParserCombinators.Congruence
import TotalParserCombinators.Congruence.Sound

-- However, it is possible to construct combinators which do not
-- preserve equality.

import TotalParserCombinators.NotACongruence

-- Proofs of various laws, for instance the monad laws.

import TotalParserCombinators.Laws

-- A proof showing that all functions of type List Bool → List R can
-- be realised using parser combinators (for any R, assuming that bag
-- equality is used for the lists of results).

import TotalParserCombinators.ExpressiveStrength

-- Definitions of asymmetric choice, and and not. Note that no
-- extension of the library is required to define these combinators,
-- which make use of a general operator which lifts initial bag
-- operations to parsers. This operator is defined using the
-- breadth-first backend's derivative operator.

import TotalParserCombinators.Pointwise
import TotalParserCombinators.AsymmetricChoice
import TotalParserCombinators.And
import TotalParserCombinators.Not

-- An alternative semantics.

import TotalParserCombinators.Semantics.Continuation

-- Simplification of parsers.

import TotalParserCombinators.Simplification

-- Definition of unambiguity.

import TotalParserCombinators.Unambiguity

-- An example: a left recursive expression grammar.

import TotalParserCombinators.Examples.Expression

-- Recognisers defined on top of the parsers, and a variant of the
-- left recursive expression grammar mentioned above.

import TotalParserCombinators.Recogniser
import TotalParserCombinators.Recogniser.Expression

-- Another example: parsing PBM image files.

import TotalParserCombinators.Examples.PBM

-- An extended example: mixfix operator parsing.

import Mixfix

-- For code related to the paper "Structurally Recursive Descent
-- Parsing", developed together with Ulf Norell, see the following
-- module:

import StructurallyRecursiveDescentParsing
