------------------------------------------------------------------------
-- Total recognisers based on the same principles as the parsers in
-- TotalParserCombinators.Parsers
--
-- Nils Anders Danielsson
------------------------------------------------------------------------

-- Recognisers are less complicated than parsers, and the following
-- code should be easier to follow than the code under
-- TotalParserCombinators.

module TotalRecognisers.README where

-- Total recognisers, including a formal semantics and a proof of
-- decidability.

import TotalRecognisers

-- Proof showing that the set of languages accepted by these
-- recognisers is exactly the set of languages which can be decided by
-- Agda programs (when the alphabet is {true, false}).

import TotalRecognisers.ExpressiveStrength

-- A more direct proof showing that the language { aⁿbⁿcⁿ | n ∈ ℕ }
-- can be decided.

import TotalRecognisers.NotOnlyContextFree
