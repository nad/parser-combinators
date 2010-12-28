------------------------------------------------------------------------
-- Total recognisers based on the same principles as the parsers in
-- TotalParserCombinators.Parser
--
-- Nils Anders Danielsson
------------------------------------------------------------------------

-- Recognisers are less complicated than parsers, and the following
-- code should (generally) be easier to follow than the code under
-- TotalParserCombinators.

module TotalRecognisers where

------------------------------------------------------------------------
-- Recognisers which do not support left recursion

-- Very simple recognisers, including a formal semantics and a proof
-- of decidability.

import TotalRecognisers.Simple

-- Proof showing that the set of languages accepted by these
-- recognisers is exactly the set of languages which can be decided by
-- Agda programs (when the alphabet is {true, false}).

import TotalRecognisers.Simple.ExpressiveStrength

-- An example: a right recursive expression grammar.

import TotalRecognisers.Simple.Expression

-- An alternative backend (without correctness proof).

import TotalRecognisers.Simple.AlternativeBackend

------------------------------------------------------------------------
-- Recognisers which do support left recursion

-- More complicated recognisers, which can handle left recursion. (The
-- set of basic combinators is also different: tok has been replaced
-- by sat, and nonempty and cast have been added.)

import TotalRecognisers.LeftRecursion

-- These recognisers have the same (maximal) expressive strength as
-- the simple ones, as long as the alphabet is finite. For infinite
-- alphabets it is shown that the expressive strength is not maximal.

import TotalRecognisers.LeftRecursion.ExpressiveStrength

-- A tiny library of derived combinators.

import TotalRecognisers.LeftRecursion.Lib

-- An example: a left recursive expression grammar.

import TotalRecognisers.LeftRecursion.Expression

-- The recognisers form a *-continuous Kleene algebra.

import TotalRecognisers.LeftRecursion.KleeneAlgebra

-- A direct proof which shows that the context-sensitive language
-- { aⁿbⁿcⁿ | n ∈ ℕ } can be decided.

import TotalRecognisers.LeftRecursion.NotOnlyContextFree
