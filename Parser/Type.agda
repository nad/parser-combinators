------------------------------------------------------------------------
-- A type signature for parsers
------------------------------------------------------------------------

module Parser.Type where

open import Data.Bool
open import Data.Product.Record

------------------------------------------------------------------------
-- Indices to the parser type

-- Does the parser accept empty strings?
--
-- Since we have a "forget" combinator this is actually a conservative
-- approximation, so a true value means that the parser _may_ accept
-- empty strings, but is not guaranteed to.

Empty : Set
Empty = Bool

-- The proper left corners of the parser, represented as a tree. See
-- the definition of Parser.Internal.Parser.

data Corners : Set where
  leaf : Corners
  step : Corners -> Corners
  node : Corners -> Corners -> Corners

Index : Set
Index = Empty × Corners

------------------------------------------------------------------------
-- The parser type signature

ParserType : Set2
ParserType =  Index  -- The indices above.
           -> Set    -- The result type.
           -> Set1
