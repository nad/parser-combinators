------------------------------------------------------------------------
-- A terminating parser data type and the accompanying interpreter
------------------------------------------------------------------------

module Parser.Internal where

open import Parser.Type
open import Data.Bool
open import Data.Product.Record
open import Data.Maybe
open import Data.Function hiding (_∘_)
open import Data.BoundedVec.Inefficient
import Data.List as L
open import Data.Nat
open import Category.Applicative.Indexed
open import Category.Monad.Indexed
open import Category.Monad.State

------------------------------------------------------------------------
-- A suitably typed composition operator

private

  infixr 9 _∘_

  _∘_ : {a c : Set} {b : Set1} -> (b -> c) -> (a -> b) -> (a -> c)
  f ∘ g = \x -> f (g x)

------------------------------------------------------------------------
-- Parser data type

-- A type for parsers which can be implemented using recursive
-- descent. The types used ensure that the implementation below is
-- structurally recursive.

-- The parsers are indexed on a type of nonterminals.

data Parser (tok : Set) (nt : ParserType) : ParserType where
  !_     :  forall {e c r}
         -> nt (e , c) r -> Parser tok nt (e , step c) r
  ret    :  forall {r} -> r -> Parser tok nt (true , leaf) r
  bind₀  :  forall {c₁ e₂ c₂ r₁ r₂}
         -> Parser tok nt (true , c₁) r₁
         -> (r₁ -> Parser tok nt (e₂ , c₂) r₂)
         -> Parser tok nt (e₂ , node c₁ c₂) r₂
  bind₁  :  forall {c₁} e₂ {c₂ r₁ r₂}
         -> Parser tok nt (false , c₁) r₁
         -> (r₁ -> Parser tok nt (e₂ , c₂) r₂)
         -> Parser tok nt (false , c₁) r₂
  alt₀   :  forall {c₁} e₂ {c₂ r}
         -> Parser tok nt (true , c₁)         r
         -> Parser tok nt (e₂   , c₂)         r
         -> Parser tok nt (true , node c₁ c₂) r
  alt₁   :  forall {c₁} e₂ {c₂ r}
         -> Parser tok nt (false , c₁)         r
         -> Parser tok nt (e₂    , c₂)         r
         -> Parser tok nt (e₂    , node c₁ c₂) r
  sat    :  forall {r}
         -> (tok -> Maybe r)
         -> Parser tok nt (false , leaf) r

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
-- 2) The parser's proper left corner tree.
-- 3) The structure of the parser.

private

 module Dummy {tok : Set} {nt : ParserType}
              (g : Grammar tok nt)
              where

  -- The pattern matching on {e = ...} below is only there to work
  -- around a bug in Agda's coverage checker.

  mutual
    parse : forall n {e c r} ->
            Parser tok nt (e , c) r ->
            P tok n (if e then n else pred n) r
    parse n       (! x)               = parse n (g x)
    parse n       (ret x)             = return x
    parse n       (bind₀       p₁ p₂) = parse  n      p₁ >>= parse  n ∘ p₂
    parse zero    (bind₁ _     p₁ p₂) = ∅
    parse (suc n) (bind₁ true  p₁ p₂) = parse (suc n) p₁ >>= parse  n ∘ p₂
    parse (suc n) (bind₁ false p₁ p₂) = parse (suc n) p₁ >>= parse↑ n ∘ p₂
    parse n       (alt₀  true  p₁ p₂) = parse  n      p₁ ∣   parse  n   p₂
    parse n       (alt₀  false p₁ p₂) = parse  n      p₁ ∣   parse↑ n   p₂
    parse n {e = true}  (alt₁  .true  p₁ p₂) = parse↑ n      p₁ ∣   parse  n   p₂
    parse n {e = false} (alt₁  .false p₁ p₂) = parse  n      p₁ ∣   parse  n   p₂
    parse zero    (sat p)             = ∅
    parse (suc n) {r = r} (sat p)     = eat =<< get
      where
        eat : forall {n} ->
              BoundedVec tok (suc n) ->
              P tok (suc n) n r
        eat []      = ∅
        eat (c ∷ s) with p c
        ... | just x  = put s >> return x
        ... | nothing = ∅

    parse↑ : forall n {c r} ->
             Parser tok nt (false , c) r ->
             P tok n n r
    parse↑ zero    p = ∅
    parse↑ (suc n) p = parse (suc n) p >>= \r ->
                       modify ↑ >>
                       return r

open Dummy public
