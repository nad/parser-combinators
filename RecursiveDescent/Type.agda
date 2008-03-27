------------------------------------------------------------------------
-- A type signature for parsers
------------------------------------------------------------------------

module RecursiveDescent.Type where

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
-- the definition of RecursiveDescent.(Coi|I)nductive.Internal.Parser.

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

------------------------------------------------------------------------
-- Operations on indices

infixr 40 _∣I_

0I : Index
0I = (false , leaf)

1I : Index
1I = (true , leaf)

_∣I_ : Index -> Index -> Index
i₁ ∣I i₂ = (proj₁ i₁ ∨ proj₁ i₂ , node (proj₂ i₁) (proj₂ i₂))
