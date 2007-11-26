------------------------------------------------------------------------
-- A type signature for parsers
------------------------------------------------------------------------

module Parser.Type where

open import Data.Bool

------------------------------------------------------------------------
-- Indices to the parser type

-- Does the parser accept empty strings?

Empty : Set
Empty = Bool

-- The spine of the parser, except that the right argument of _·_ is
-- omitted if the left one does not accept empty strings.

-- This can also be seen as the spine of the parser's first set (the
-- set of first characters which the parser can accept).

data Depth : Set where
  leaf : Depth
  step : Depth -> Depth
  node : Depth -> Depth -> Depth

------------------------------------------------------------------------
-- The parser type signature

ParserType : Set2
ParserType = Empty -> Depth -> Set -> Set1
