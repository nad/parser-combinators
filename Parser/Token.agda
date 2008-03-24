------------------------------------------------------------------------
-- Some parsers which require a decidable token equality
------------------------------------------------------------------------

open import Relation.Binary

module Parser.Token (D : DecSetoid) where

open DecSetoid D using (_≟_) renaming (carrier to tok)

open import Parser

open import Data.Maybe
open import Relation.Nullary

-- Parsing a given token (or, really, a given equivalence class of
-- tokens).

sym : forall {nt} -> tok -> Parser tok nt _ tok
sym c = sat p
  where
  p : tok -> Maybe tok
  p x with c ≟ x
  ... | yes _ = just x
  ... | no  _ = nothing
