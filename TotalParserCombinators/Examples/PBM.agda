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

module TotalParserCombinators.Examples.PBM where

open import Data.Bool
open import Data.Char as Char using (Char; _==_)
open import Data.List as List using (List)
open import Data.Maybe
open import Data.Nat
import Data.Nat.Show as ℕ
open import Data.String as String
  using (String) renaming (_++_ to _<+>_)
open import Data.Unit
open import Data.Vec as Vec using (Vec; _++_; [_])
open import Function
open import Relation.Binary.PropositionalEquality as P using (_≡_)

open import TotalParserCombinators.BreadthFirst
open import TotalParserCombinators.Lib
open import TotalParserCombinators.Parser

open Token Char Char._≟_

------------------------------------------------------------------------
-- PBM images

module PBM where

  -- Colours.

  data Colour : Set where
    white : Colour
    black : Colour

  -- Matrices.

  Matrix : Set → ℕ → ℕ → Set
  Matrix A rows cols = Vec (Vec A cols) rows

  -- PBM images.

  record PBM : Set where
    constructor toPBM
    field
      {rows cols} : ℕ
      matrix      : Matrix Colour rows cols

  open PBM public

  -- Showing PBM images.

  showColour : Colour → Char
  showColour white = '0'
  showColour black = '1'

  show : PBM → String
  show i = "P1\n" <+>
           ℕ.show (cols i) <+> " " <+> ℕ.show (rows i) <+> "\n" <+>
           showMatrix (matrix i)
    where
    showMatrix = String.fromList ∘
                 Vec.toList ∘
                 Vec.concat ∘
                 Vec.map ((λ xs → xs ++ [ '\n' ]) ∘ Vec.map showColour)

open PBM

------------------------------------------------------------------------
-- Parsing PBM images

comment : Parser Char ⊤ _
comment =
  tok '#'                  >>= λ _ →
  sat′ (not ∘ _==_ '\n') ⋆ >>= λ _ →
  tok '\n'                 >>= λ _ →
  return tt

colour : Parser Char Colour _
colour = const white <$> tok '0'
       ∣ const black <$> tok '1'

pbm : Parser Char PBM _
pbm =
  w∣c ⋆                                  >>= λ _ →
  tok 'P' >>= λ _ → tok '1'              >>= λ _ →
  w∣c ⋆                                  >>= λ _ →
  number                                 >>= λ cols →
  w∣c +                                  >>= λ _ →
  number                                 >>= λ rows →
  w∣c                                    >>= λ _ →
  (w∣c ⋆ >>= λ _ → colour) ^ cols ^ rows >>= λ m →
  token ⋆                                >>= λ _ →
  return (toPBM m)
  where
  w∣c = whitespace ∣ comment

-- The example is commented out, because it takes ages to run this
-- parser.

-- module Example where

--   open Vec

--   image = toPBM ((white ∷ black ∷ []) ∷
--                  (black ∷ white ∷ []) ∷
--                  (black ∷ black ∷ []) ∷ [])

--   ex : parse pbm (String.toList $ show image) ≡ List.[_] image
--   ex = P.refl
