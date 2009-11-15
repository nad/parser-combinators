------------------------------------------------------------------------
-- Total recognisers based on the same principles as the parsers in
-- TotalParserCombinators.Parsers
--
-- Nils Anders Danielsson
------------------------------------------------------------------------

-- Recognisers are less complicated than parsers, and the following
-- code should be easier to follow than the code under
-- TotalParserCombinators.

module TotalRecognisers where

-- Very simple recognisers, including a formal semantics and a proof
-- of decidability.

import TotalRecognisers.Simple

-- Proof showing that the set of languages accepted by these
-- recognisers is exactly the set of languages which can be decided by
-- Agda programs (when the alphabet is {true, false}).

import TotalRecognisers.Simple.ExpressiveStrength

-- More complicated recognisers, which can handle left recursion. (The
-- set of basic combinators is also different: tok has been replaced
-- by sat, and nonempty and cast have been added.)

import TotalRecognisers.LeftRecursion

-- These recognisers have the same expressive strength as the ones
-- above, as long as the alphabet is finite. (For infinite alphabets
-- the increased expressive power of sat comes into play.)

import TotalRecognisers.LeftRecursion.ExpressiveStrength

-- A tiny library of derived combinators.

import TotalRecognisers.LeftRecursion.Lib

-- The recognisers form a *-continuous Kleene algebra.

import TotalRecognisers.LeftRecursion.KleeneAlgebra

-- A direct proof which shows that the context-sensitive language
-- { aⁿbⁿcⁿ | n ∈ ℕ } can be decided.

import TotalRecognisers.LeftRecursion.NotOnlyContextFree
