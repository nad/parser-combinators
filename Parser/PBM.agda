------------------------------------------------------------------------
-- A parser for PBM images; illustrates essential use of bind
------------------------------------------------------------------------

-- Note that I am using the simple "Plain PBM" format, and I do not
-- adhere to the following statement from the pbm man page:
--
--   "Programs that read this format should be as lenient as possible,
--   accepting anything that looks remotely like a bitmap."
--
-- Furthermore I do not require every line in the "raster" to be at
-- most 70 characters long.
--
-- Finally note that the format is not formally specified, and my
-- interpretation of the informal specification may not be entirely
-- "correct".

-- The idea to write this particular parser was taken from "The Power
-- of Pi" by Oury and Swierstra.

module Parser.PBM where

import Data.Vec as Vec
open Vec using (Vec; _++_)
import Data.List as List
open import Data.Nat
import Data.String as String
open String using (String) renaming (_++_ to _<+>_)
import Data.Char as Char
open Char using (Char)
open import Logic
open import Data.Product.Record
open import Data.Function
open import Data.Bool
open import Data.Unit
open import Data.Maybe
import Data.Nat.Show as N
open import Data.Bool.Properties
open import Algebra.Structures
open import Relation.Nullary

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
show i = "P1 # Generated using Agda.\n" <+>
         N.show (cols i) <+> " " <+> N.show (rows i) <+> "\n" <+>
         showMatrix (matrix i)
  where
  showMatrix = String.fromList ∘
               Vec.toList ∘
               Vec.concat ∘
               Vec.map ((\xs -> xs ++ Vec.singleton '\n') ∘
                        Vec.map showColour)

------------------------------------------------------------------------
-- Parsing PBM images

data NT : ParserType where
  lib     : forall {i r} -> L.Nonterminal       NT i r -> NT _ r
  cLib    : forall {i r} -> CharLib.Nonterminal NT i r -> NT _ r
  comment : NT _ ⊤
  colour  : NT _ Colour
  pbm     : NT _ PBM

open Lib.Combinators Char lib
open CharLib.Combinators cLib

grammar : Grammar Char NT
grammar (lib p)  = library p
grammar (cLib p) = charLib p
grammar comment  = tt <$ sym '#'
                      <⊛ (sat' (not ∘ Char._==_ '\n')) ⋆
                      <⊛ sym '\n'
grammar colour   = white <$ sym '0'
                 ∣ black <$ sym '1'
grammar pbm      =
  (! comment) ⋆ ⊛>
  string (String.toVec "P1") ⊛>
  (whitespace ∣ ! comment) ⋆ ⊛>
  whitespace ⊛>
  (whitespace ∣ ! comment) ⋆ ⊛>
  number >>= \cols ->
  whitespace + ⊛>
  number >>= \rows ->
  whitespace ⋆ ⊛>
  (makePBM <$> image rows cols) <⊛
  (return tt ∣ whitespace <⊛ any ⋆)
  where
  i = (false ,
       node leaf
            (step (node leaf (node (node (node leaf leaf) leaf) leaf))))

  image : forall rows cols ->
          Parser Char NT i (Matrix Colour rows cols)
  image zero         cols = whitespace ⊛> (whitespace ⋆ ⊛> return Vec.[])
  image rows@(suc _) cols =
    whitespace ⊛>
    exactly rows (cast lem ≡-refl
                  (whitespace ⋆ ⊛>
                   exactly cols (! colour <⊛ whitespace ⋆) <⊛
                   sym '\n'))
    where
    open IsCommutativeSemiring _ Bool-isCommutativeSemiring-∨-∧
    lem = *-comm ((decToBool (cols ℕ-≟ 0) ∧ true) ∧ true) false

module Example where

  open Vec

  image = makePBM ((white ∷ black ∷ []) ∷
                   (black ∷ white ∷ []) ∷
                   (black ∷ black ∷ []) ∷ [])

  ex₁ : parse-complete (! pbm) grammar (String.toList (show image)) ≡
        List.singleton image
  ex₁ = ≡-refl
