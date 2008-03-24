------------------------------------------------------------------------
-- Some parsers which require a decidable token equality
------------------------------------------------------------------------

open import Relation.Binary

module Parser.Token (D : DecSetoid) where

open DecSetoid D using (_≟_) renaming (carrier to tok)

open import Parser
open import Parser.SimpleLib

open import Data.Maybe
open import Relation.Nullary
open import Data.Vec
open import Data.Vec1

-- Parsing a given token (or, really, a given equivalence class of
-- tokens).

sym : forall {nt} -> tok -> Parser tok nt _ tok
sym c = sat p
  where
  p : tok -> Maybe tok
  p x with c ≟ x
  ... | yes _ = just x
  ... | no  _ = nothing

-- Parsing a sequence of tokens.

string : forall {nt n} -> Vec tok n -> Parser tok nt _ (Vec tok n)
string cs = sequence (map₀₁ sym cs)
