------------------------------------------------------------------------
-- A terminating parser data type and the accompanying interpreter
------------------------------------------------------------------------

module Parser.Internal where

open import Parser.Type
open import Data.Bool
open import Data.Product.Record
open import Data.Maybe
open import Data.Function
open import Data.BoundedVec.Inefficient
import Data.List as L
open import Data.Nat
open import Category.Applicative.Indexed
open import Category.Monad.Indexed
open import Category.Monad.State

------------------------------------------------------------------------
-- Parser data type

-- A type for parsers which can be implemented using recursive
-- descent. The types used ensure that the implementation below is
-- structurally recursive.

-- The parsers are indexed on a type of nonterminals.

data Parser (tok : Set) (nt : ParserType) : ParserType where
  !_     :  forall {e d r}
         -> nt (e , d) r -> Parser tok nt (e , step d) r
  ε      :  forall {r} -> r -> Parser tok nt (true , leaf) r
  sat    :  forall {r}
         -> (tok -> Maybe r)
         -> Parser tok nt (false , leaf) r
  forget :  forall e {d r}
         -> Parser tok nt (e , d) r
         -> Parser tok nt (true , d) r
  seq₀   :  forall {d₁ e₂ d₂ r₁ r₂}
         -> Parser tok nt (true , d₁)         (r₁ -> r₂)
         -> Parser tok nt (e₂   , d₂)         r₁
         -> Parser tok nt (e₂   , node d₁ d₂) r₂
  seq₁   :  forall {d₁} e₂ {d₂ r₁ r₂}
         -> Parser tok nt (false , d₁)      (r₁ -> r₂)
         -> Parser tok nt (e₂    , d₂)      r₁
         -> Parser tok nt (false , d₁) r₂
  alt₀   :  forall {d₁} e₂ {d₂ r}
         -> Parser tok nt (true , d₁)         r
         -> Parser tok nt (e₂   , d₂)         r
         -> Parser tok nt (true , node d₁ d₂) r
  alt₁   :  forall {d₁ e₂ d₂ r}
         -> Parser tok nt (false , d₁)         r
         -> Parser tok nt (e₂    , d₂)         r
         -> Parser tok nt (e₂    , node d₁ d₂) r

------------------------------------------------------------------------
-- Run function for the parsers

-- Grammars.

Grammar : Set -> ParserType -> Set1
Grammar tok nt = forall {i r} -> nt i r -> Parser tok nt i r

-- Parser monad.

P : Set -> IFun ℕ
P tok = IStateT (BoundedVec tok) L.[_]

PIMonadPlus : (tok : Set) -> RawIMonadPlus (P tok)
PIMonadPlus tok = StateTIMonadPlus (BoundedVec tok) L.ListMonadPlus

PIMonadState : (tok : Set) -> RawIMonadState (BoundedVec tok) (P tok)
PIMonadState tok = StateTIMonadState (BoundedVec tok) L.ListMonad

private
  open module LM {tok : Set} = RawIMonadPlus  (PIMonadPlus  tok)
  open module SM {tok : Set} = RawIMonadState (PIMonadState tok)
                                 using (get; put; modify)

-- For every successful parse the run function returns the remaining
-- string. (Since there can be several successful parses a list of
-- strings is returned.)

-- This function is structurally recursive with respect to the
-- following lexicographic measure:
--
-- 1) The upper bound of the length of the input string.
-- 2) The depth of the parser.
-- 3) The structure of the parser.

private
  module Dummy {tok : Set} {nt : ParserType}
               (g : Grammar tok nt)
               where

    mutual
      parse₀ : forall {d r} ->
               Parser tok nt (true , d) r ->
               forall n -> P tok n n r
      parse₀ (! x)              n = parse₀ (g x) n
      parse₀ (ε x)              n = return x
      parse₀ (forget true  p)   n = parse₀  p n
      parse₀ (forget false p)   n = parse₁↑ p n
      parse₀ (seq₀       p₁ p₂) n = parse₀  p₁ n ⊛ parse₀  p₂ n
      parse₀ (alt₀ true  p₁ p₂) n = parse₀  p₁ n ∣ parse₀  p₂ n
      parse₀ (alt₀ false p₁ p₂) n = parse₀  p₁ n ∣ parse₁↑ p₂ n
      parse₀ (alt₁       p₁ p₂) n = parse₁↑ p₁ n ∣ parse₀  p₂ n

      parse₁ : forall {d r} ->
               Parser tok nt (false , d) r ->
               forall n -> P tok n (pred n) r
      parse₁ _                   zero    = ∅
      parse₁ (! x)               (suc n) = parse₁ (g x) (suc n)
      parse₁ (seq₀        p₁ p₂) (suc n) = parse₀ p₁ (suc n) ⊛ parse₁  p₂ (suc n)
      parse₁ (seq₁  true  p₁ p₂) (suc n) = parse₁ p₁ (suc n) ⊛ parse₀  p₂ n
      parse₁ (seq₁  false p₁ p₂) (suc n) = parse₁ p₁ (suc n) ⊛ parse₁↑ p₂ n
      parse₁ (alt₁        p₁ p₂) (suc n) = parse₁ p₁ (suc n) ∣ parse₁  p₂ (suc n)
      parse₁ {r = r} (sat p)     (suc n) = eat =<< get
        where
          eat : forall {n} ->
                BoundedVec tok (suc n) ->
                P tok (suc n) n r
          eat []      = ∅
          eat (c ∷ s) with p c
          ... | just x  = put s >> return x
          ... | nothing = ∅

      parse₁↑ : forall {d r} ->
                Parser tok nt (false , d) r ->
                forall n -> P tok n n r
      parse₁↑ p zero    = ∅
      parse₁↑ p (suc n) = parse₁ p (suc n) >>= \r ->
                          modify ↑ >>
                          return r

    parse : forall {e d r n} ->
            Parser tok nt (e , d) r ->
            P tok n (if e then n else pred n) r
    parse {e = true}  {n = n} p = parse₀ p n
    parse {e = false} {n = n} p = parse₁ p n

open Dummy public
