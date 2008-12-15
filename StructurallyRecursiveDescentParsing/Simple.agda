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
  P tok = IStateT (BoundedVec tok) L.List

  open module M₁ {tok} =
    RawIMonadPlus (StateTIMonadPlus (BoundedVec tok) L.ListMonadPlus)
    renaming (return to ret)

  open module M₂ {tok} =
    RawIMonadState (StateTIMonadState (BoundedVec tok) L.ListMonad)
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

 module Dummy {tok nt} (g : Grammar tok nt) where

  mutual
    parse : forall n {e c r} ->
            Parser tok nt (e ◇ c) r ->
            P tok n (if e then n else pred n) r
    parse n       (! x)           = parse n (g x)
    parse zero    symbol          = ∅
    parse (suc n) symbol          = eat =<< get
    parse n       (return x)      = ret x
    parse n       fail            = ∅
    parse n       (p₁ ?>>= p₂)    = parse  n      p₁ >>= parse  n ∘′ p₂
    parse zero    (p₁ !>>= p₂)    = ∅
    parse (suc n) (p₁ !>>= p₂)    = parse (suc n) p₁ >>= parse↑ n ∘′ p₂
    parse n       (alt ⊤ _ p₁ p₂) = parse  n      p₁ ∣   parse↑ n    p₂
    parse n       (alt ⊥ ⊤ p₁ p₂) = parse↑ n      p₁ ∣   parse  n    p₂
    parse n       (alt ⊥ ⊥ p₁ p₂) = parse  n      p₁ ∣   parse  n    p₂

    parse↑ : forall n {e c r} -> Parser tok nt (e ◇ c) r -> P tok n n r
    parse↑ n       {⊤} p = parse n p
    parse↑ zero    {⊥} p = ∅
    parse↑ (suc n) {⊥} p = parse (suc n) p >>= \r ->
                           modify ↑ >>
                           ret r

    eat : forall {n} -> BoundedVec tok (suc n) -> P tok (suc n) n tok
    eat []      = ∅
    eat (c ∷ s) = put s >> ret c

-- Exported run function.

parse :  forall {tok nt i r}
      -> Parser tok nt i r -> Grammar tok nt
      -> L.List tok -> L.List (r × L.List tok)
parse p g s = L.map (map-× id toList)
                    (Dummy.parse g _ p (fromList s))

-- A variant which only returns parses which leave no remaining input.

parse-complete :  forall {tok nt i r}
               -> Parser tok nt i r -> Grammar tok nt
               -> L.List tok -> L.List r
parse-complete p g s =
  L.map proj₁ (L.filter (L.null ∘ proj₂) (parse p g s))
