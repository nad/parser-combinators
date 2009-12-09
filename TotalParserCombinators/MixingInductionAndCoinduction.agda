------------------------------------------------------------------------
-- Code related to the paper "Mixing Induction and Coinduction"
--
-- Nils Anders Danielsson
------------------------------------------------------------------------

module TotalParserCombinators.MixingInductionAndCoinduction where

-- Helper functions related to coinduction.

import TotalParserCombinators.Coinduction

-- The parser type, along with its semantics.

import TotalParserCombinators.Parser
import TotalParserCombinators.Semantics

-- A very small library of derived parser combinators.

import TotalParserCombinators.Lib

-- A breadth-first backend.

import TotalParserCombinators.BreadthFirst

-- An extended example: mixfix operator parsing.

import Mixfix

-- For a full overview of the TotalParserCombinators library, see the
-- module TotalParserCombinators.
