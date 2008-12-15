------------------------------------------------------------------------
-- A simple backend
------------------------------------------------------------------------

module StructurallyRecursiveDescentParsing.Simple where

open import Data.Bool renaming (true to ⊤; false to ⊥)
open import Data.Product
open import Data.Maybe
open import Data.BoundedVec.Inefficient
import Data.List as L
open import Data.Nat
open import Data.Function using (id; _∘_)
open import Category.Applicative.Indexed
open import Category.Monad.Indexed
open import Category.Monad.State

open import StructurallyRecursiveDescentParsing.Index
open import StructurallyRecursiveDescentParsing.Type
open import StructurallyRecursiveDescentParsing.Utilities

------------------------------------------------------------------------
-- Parser monad

private

  P : Set -> IFun ℕ
  P Tok = IStateT (BoundedVec Tok) L.List

  open module M₁ {Tok} =
    RawIMonadPlus (StateTIMonadPlus (BoundedVec Tok) L.ListMonadPlus)
    renaming (return to ret)

  open module M₂ {Tok} =
    RawIMonadState (StateTIMonadState (BoundedVec Tok) L.ListMonad)
    using (get; put; modify)

------------------------------------------------------------------------
-- Run function for the parsers

-- For every successful parse the run function returns the remaining
-- string. (Since there can be several successful parses a list of
-- strings is returned.)

-- This function is structurally recursive with respect to the
-- following lexicographic measure:
--
-- 1) The upper bound of the length of the input string.
-- 2) The parser's proper left corner tree.

private

 module Dummy {Tok NT} (g : Grammar Tok NT) where

  mutual
    parse : forall n {e c R} ->
            Parser Tok NT (e ◇ c) R ->
            P Tok n (if e then n else pred n) R
    parse n       (! x)           = parse n (g x)
    parse zero    token           = ∅
    parse (suc n) token           = eat =<< get
    parse n       (return x)      = ret x
    parse n       fail            = ∅
    parse n       (p₁ ?>>= p₂)    = parse  n      p₁ >>= parse  n ∘′ p₂
    parse zero    (p₁ !>>= p₂)    = ∅
    parse (suc n) (p₁ !>>= p₂)    = parse (suc n) p₁ >>= parse↑ n ∘′ p₂
    parse n       (alt ⊤ _ p₁ p₂) = parse  n      p₁ ∣   parse↑ n    p₂
    parse n       (alt ⊥ ⊤ p₁ p₂) = parse↑ n      p₁ ∣   parse  n    p₂
    parse n       (alt ⊥ ⊥ p₁ p₂) = parse  n      p₁ ∣   parse  n    p₂

    parse↑ : forall n {e c R} -> Parser Tok NT (e ◇ c) R -> P Tok n n R
    parse↑ n       {⊤} p = parse n p
    parse↑ zero    {⊥} p = ∅
    parse↑ (suc n) {⊥} p = parse (suc n) p >>= \r ->
                           modify ↑ >>
                           ret r

    eat : forall {n} -> BoundedVec Tok (suc n) -> P Tok (suc n) n Tok
    eat []      = ∅
    eat (c ∷ s) = put s >> ret c

-- Exported run function.

parse : forall {Tok NT i R} ->
        Parser Tok NT i R -> Grammar Tok NT ->
        L.List Tok -> L.List (R × L.List Tok)
parse p g s = L.map (map-× id toList)
                    (Dummy.parse g _ p (fromList s))

-- A variant which only returns parses which leave no remaining input.

parse-complete : forall {Tok NT i R} ->
                 Parser Tok NT i R -> Grammar Tok NT ->
                 L.List Tok -> L.List R
parse-complete p g s =
  L.map proj₁ (L.filter (L.null ∘ proj₂) (parse p g s))
