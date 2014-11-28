------------------------------------------------------------------------
-- A parser for PBM images; illustrates "essential" use of bind
------------------------------------------------------------------------

-- Note that I am using the simple "Plain PBM" format, and I try to
-- adhere to the following statement from the pbm man page:
--
--   "Programs that read this format should be as lenient as possible,
--   accepting anything that looks remotely like a bitmap."

-- I got the idea to write this particular parser from "The Power of
-- Pi" by Oury and Swierstra.

module StructurallyRecursiveDescentParsing.PBM where

import Data.Vec as Vec
import Data.List as List
open import Coinduction
open import Data.Bool
open import Data.Char as Char using (_==_)
import Data.String as String
open import Data.Unit
open import Function
open import Relation.Binary.PropositionalEquality

open import StructurallyRecursiveDescentParsing.Grammar
open import StructurallyRecursiveDescentParsing.Lib
open import StructurallyRecursiveDescentParsing.DepthFirst
open Token Char.decSetoid

open import TotalParserCombinators.Examples.PBM using (module PBM)
open PBM

mutual

  comment : Parser EmptyNT _ _ _
  comment = tt <$ tok '#'
               <⊛ sat' (not ∘ _==_ '\n') ⋆
               <⊛ tok '\n'

  colour = white <$ tok '0'
         ∣ black <$ tok '1'

  pbm =
     w∣c ⋆ ⊛>
     theString (String.toVec "P1") ⊛>
     w∣c ⋆ ⊛>
     number !>>= λ cols → ♯ -- _>>=_ works just as well.
    (w∣c + ⊛>
     number >>=  λ rows →   -- _!>>=_ works just as well.
     w∣c ⊛>
     (toPBM <$> exactly rows (exactly cols (w∣c ⋆ ⊛> colour))) <⊛
     any ⋆)
    where w∣c = whitespace ∣ comment

module Example where

  open Vec

  image = toPBM ((white ∷ black ∷ white ∷ []) ∷
                 (black ∷ white ∷ black ∷ []) ∷
                 (white ∷ black ∷ white ∷ []) ∷ [])

  ex : parseComplete (⟦ pbm ⟧ emptyGrammar)
                     (String.toList (show image)) ≡
       List.[_] image
  ex = refl
