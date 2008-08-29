------------------------------------------------------------------------
-- A simple backend
------------------------------------------------------------------------

module RecursiveDescent.Hybrid.Simple where

open import Data.Bool
open import Data.Product.Record
import Data.Product as Prod
open import Data.Maybe
open import Data.BoundedVec.Inefficient
import Data.List as L
open import Data.Nat
open import Data.Function using (id; _∘_)
open import Category.Applicative.Indexed
open import Category.Monad.Indexed
open import Category.Monad.State

open import RecursiveDescent.Hybrid.Type
open import Utilities

------------------------------------------------------------------------
-- Parser monad

private

  P : Set -> IFun ℕ
  P tok = IStateT (BoundedVec tok) L.List

  PIMonadPlus : (tok : Set) -> RawIMonadPlus (P tok)
  PIMonadPlus tok = StateTIMonadPlus (BoundedVec tok) L.ListMonadPlus

  PIMonadState : (tok : Set) -> RawIMonadState (BoundedVec tok) (P tok)
  PIMonadState tok = StateTIMonadState (BoundedVec tok) L.ListMonad

  open module LM {tok} = RawIMonadPlus  (PIMonadPlus  tok)
  open module SM {tok} = RawIMonadState (PIMonadState tok)
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
            Parser tok nt (e , c) r ->
            P tok n (if e then n else pred n) r
    parse n       (! x)                   = parse n (g x)
    parse zero    symbol                  = ∅
    parse (suc n) symbol                  = eat =<< get
    parse n       (ret x)                 = return x
    parse n       fail                    = ∅
    parse n       (bind₁           p₁ p₂) = parse  n      p₁ >>= parse  n ∘′ p₂
    parse zero    (bind₂           p₁ p₂) = ∅
    parse (suc n) (bind₂           p₁ p₂) = parse (suc n) p₁ >>= parse↑ n ∘′ p₂
    parse n       (alt true  _     p₁ p₂) = parse  n      p₁ ∣   parse↑ n    p₂
    parse n       (alt false true  p₁ p₂) = parse↑ n      p₁ ∣   parse  n    p₂
    parse n       (alt false false p₁ p₂) = parse  n      p₁ ∣   parse  n    p₂

    parse↑ : forall n {e c r} -> Parser tok nt (e , c) r -> P tok n n r
    parse↑ n       {true}  p = parse n p
    parse↑ zero    {false} p = ∅
    parse↑ (suc n) {false} p = parse (suc n) p >>= \r ->
                               modify ↑ >>
                               return r

    eat : forall {n} -> BoundedVec tok (suc n) -> P tok (suc n) n tok
    eat []      = ∅
    eat (c ∷ s) = put s >> return c

-- Exported run function.

parse :  forall {tok nt i r}
      -> Parser tok nt i r -> Grammar tok nt
      -> L.List tok -> L.List (Prod._×_ r (L.List tok))
parse p g s = L.map (Prod.map-× id toList)
                    (Dummy.parse g _ p (fromList s))

-- A variant which only returns parses which leave no remaining input.

parse-complete :  forall {tok nt i r}
               -> Parser tok nt i r -> Grammar tok nt
               -> L.List tok -> L.List r
parse-complete p g s =
  L.map Prod.proj₁ (L.filter (L.null ∘ Prod.proj₂) (parse p g s))
