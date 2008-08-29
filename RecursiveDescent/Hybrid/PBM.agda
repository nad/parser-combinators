------------------------------------------------------------------------
-- A parser for PBM images; illustrates essential use of bind
------------------------------------------------------------------------

-- Note that I am using the simple "Plain PBM" format, and I try to
-- adhere to the following statement from the pbm man page:
--
--   "Programs that read this format should be as lenient as possible,
--   accepting anything that looks remotely like a bitmap."

-- The idea to write this particular parser was taken from "The Power
-- of Pi" by Oury and Swierstra.

module RecursiveDescent.Hybrid.PBM where

import Data.Vec as Vec
open Vec using (Vec; _++_; [_])
import Data.List as List
open import Data.Nat
import Data.String as String
open String using (String) renaming (_++_ to _<+>_)
import Data.Char as Char
open Char using (Char; _==_)
open import Data.Product.Record
open import Data.Function
open import Data.Bool
open import Data.Unit
open import Data.Maybe
import Data.Nat.Show as N
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import RecursiveDescent.Index
open import RecursiveDescent.Hybrid
open import RecursiveDescent.Hybrid.Lib
open Token Char.decSetoid

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
               Vec.map ((\xs -> xs ++ [ '\n' ]) ∘ Vec.map showColour)

------------------------------------------------------------------------
-- Parsing PBM images

data NT : ParserType where
  comment : NT _ ⊤
  colour  : NT _ Colour
  pbm     : NT _ PBM

grammar : Grammar Char NT
grammar comment  = tt <$ sym '#' <⊛ sat' (not ∘ _==_ '\n') ⋆ <⊛ sym '\n'
grammar colour   = white <$ sym '0'
                 ∣ black <$ sym '1'
grammar pbm      =
  w∣c ⋆ ⊛>
  string (String.toVec "P1") ⊛>
  w∣c ⋆ ⊛>
  number !>>= \cols ->  -- _>>=_ works just as well.
  w∣c + ⊛>
  number >>=  \rows ->  -- _!>>=_ works just as well.
  w∣c ⊛>
  (makePBM <$> exactly rows (exactly cols (w∣c ⋆ ⊛> ! colour))) <⊛
  any ⋆
  where w∣c = whitespace ∣ ! comment

module Example where

  open Vec

  image = makePBM ((white ∷ black ∷ []) ∷
                   (black ∷ white ∷ []) ∷
                   (black ∷ black ∷ []) ∷ [])

  ex₁ : parse-complete (! pbm) grammar (String.toList (show image)) ≡
        List.[_] image
  ex₁ = ≡-refl
