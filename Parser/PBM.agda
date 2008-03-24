------------------------------------------------------------------------
-- A parser for PBM images; illustrates essential use of bind
------------------------------------------------------------------------

-- Note that I am using a simplified version of the PBM file format
-- below.

-- The idea to write this particular parser was taken from "The Power
-- of Pi" by Oury and Swierstra.

module Parser.PBM where

import Data.Vec as Vec
open Vec using (Vec)
import Data.List as List
open import Data.Nat
import Data.String as String
open String using (String)
import Data.Char as Char
open Char using (Char)
open import Logic
open import Data.Product.Record
open import Data.Function
open import Data.Bool
import Data.Nat.Show as N

open import Parser
open import Parser.SimpleLib
import Parser.Token as Tok; open Tok Char.decSetoid
import Parser.Lib as Lib
module L = Lib Char
import Parser.Char as CharLib

------------------------------------------------------------------------
-- The PBM type

data Colour : Set where
  white : Colour
  black : Colour

Matrix : Set -> ℕ -> ℕ -> Set
Matrix a rows cols = Vec (Vec a cols) rows

record PBM : Set where
  field
    rows   : ℕ
    cols   : ℕ
    matrix : Matrix Colour rows cols

open PBM

makePBM : forall {rows cols} -> Matrix Colour rows cols -> PBM
makePBM m = record { rows = _; cols = _; matrix = m }

------------------------------------------------------------------------
-- Showing PBM images

showColour : Colour -> Char
showColour white = '0'
showColour black = '1'

show : PBM -> String
show i = "P4 " ++ N.show (cols i) ++ " " ++ N.show (rows i) ++ "\n" ++
         showMatrix (matrix i)
  where
  open String
  showMatrix = String.fromList ∘ List.map showColour ∘
               Vec.toList ∘ Vec.concat

------------------------------------------------------------------------
-- Parsing PBM images

data NT : ParserType where
  lib    : forall {i r} -> L.Nonterminal       NT i r -> NT _ r
  cLib   : forall {i r} -> CharLib.Nonterminal NT i r -> NT _ r
  colour : NT _ Colour
  pbm    : NT _ PBM

open Lib.Combinators Char lib
open CharLib.Combinators cLib

grammar : Grammar Char NT
grammar (lib p)  = library p
grammar (cLib p) = charLib p
grammar colour   = white <$ sym '0'
                 ∣ black <$ sym '1'
grammar pbm      =
  whitespace ⋆ ⊛>
  string (String.toVec "P4") ⊛>
  whitespace ⋆ ⊛>
  number >>= \cols ->
  whitespace ⋆ ⊛>
  number >>= \rows ->
  whitespace ⋆ ⊛>
  (makePBM <$> image rows cols) <⊛
  whitespace ⋆
  where
  i = (false ,
       node leaf
            (step (node leaf (node (node (node leaf leaf) leaf) leaf))))
  image : forall rows cols ->
          Parser Char NT i (Matrix Colour rows cols)
  image r@(suc _) c@(suc _) = whitespace ⊛> exactly r (exactly c (! colour))
  image zero      cols      = whitespace ⊛> return Vec.[]
  image rows      zero      = whitespace ⊛> return (Vec.replicate Vec.[])

module Example where

  open Vec

  image = makePBM ((white ∷ black ∷ []) ∷
                   (black ∷ white ∷ []) ∷
                   (black ∷ black ∷ []) ∷ [])

  ex₁ : parse-complete (! pbm) grammar (String.toList (show image)) ≡
        List.singleton image
  ex₁ = ≡-refl
