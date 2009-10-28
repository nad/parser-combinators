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

-- More complicated recognisers, which can handle left recursion.
-- (Some extra combinators have also been added: nonempty and cast.)

import TotalRecognisers.LeftRecursion

-- These recognisers have the same expressive strength as the ones
-- above (for finite alphabets).

import TotalRecognisers.LeftRecursion.ExpressiveStrength

-- The recognisers form a Kleene algebra.

import TotalRecognisers.LeftRecursion.KleeneAlgebra

-- A direct proof which shows that the context-sensitive language
-- { aⁿbⁿcⁿ | n ∈ ℕ } can be decided.

import TotalRecognisers.LeftRecursion.NotOnlyContextFree
