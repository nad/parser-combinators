------------------------------------------------------------------------
-- Some type(s) used by the library
------------------------------------------------------------------------

module Parser.Lib.Types where

-- Associativity.

data Assoc : Set where
  left  : Assoc
  right : Assoc
