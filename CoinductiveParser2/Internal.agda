------------------------------------------------------------------------
-- A terminating parser data type and the accompanying interpreter
------------------------------------------------------------------------

-- Note that Parser is assumed to be coinductive.

module CoinductiveParser2.Internal where

open import Parser.Type
open import Data.Bool
open import Data.Product.Record
open import Data.Maybe
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

  _∘_ : {a c : Set} {b : a -> Set1} ->
        (forall {x} -> b x -> c) -> ((x : a) -> b x) -> (a -> c)
  f ∘ g = \x -> f (g x)

------------------------------------------------------------------------
-- Parser data type

-- A type for parsers which can be implemented using recursive
-- descent. The types used ensure that the implementation below is
-- structurally recursive.

{- co -}
data Parser (tok : Set) : Index -> Set -> Set1 where
  symbol :  Parser tok (false , leaf) tok
  ret    :  forall {r} -> r -> Parser tok (true , leaf) r
  fail   :  forall {r} -> Parser tok (false , leaf) r
  bind₀  :  forall {c₁ e₂ c₂ r₁ r₂}
         -> Parser tok (true , c₁) r₁
         -> (r₁ -> Parser tok (e₂ , c₂) r₂)
         -> Parser tok (e₂ , node c₁ c₂) r₂
  bind₁  :  forall {c₁ r₁ r₂} {i₂ : r₁ -> Index}
         -> Parser tok (false , c₁) r₁
         -> ((x : r₁) -> Parser tok (i₂ x) r₂)
         -> Parser tok (false , step c₁) r₂
  alt₀   :  forall {c₁ e₂ c₂ r}
         -> Parser tok (true , c₁)         r
         -> Parser tok (e₂   , c₂)         r
         -> Parser tok (true , node c₁ c₂) r
  alt₁   :  forall {c₁} e₂ {c₂ r}
         -> Parser tok (false , c₁)         r
         -> Parser tok (e₂    , c₂)         r
         -> Parser tok (e₂    , node c₁ c₂) r

------------------------------------------------------------------------
-- Run function for the parsers

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

mutual

  -- The pattern matching on {e = ...} in parse is only there to work
  -- around a bug in Agda's coverage checker.

  parse : forall n {tok e c r} ->
          Parser tok (e , c) r ->
          P tok n (if e then n else pred n) r
  parse zero    symbol             = ∅
  parse (suc n) symbol             = eat =<< get
  parse n       (ret x)            = return x
  parse n       fail               = ∅
  parse n       (bind₀      p₁ p₂) = parse  n      p₁ >>= parse  n ∘ p₂
  parse zero    (bind₁      p₁ p₂) = ∅
  parse (suc n) (bind₁      p₁ p₂) = parse (suc n) p₁ >>= parse↑ n ∘ p₂
  parse n       (alt₀       p₁ p₂) = parse  n      p₁ ∣   parse↑ n   p₂
  parse n {e = true}  (alt₁ .true  p₁ p₂) = parse↑ n      p₁ ∣   parse  n   p₂
  parse n {e = false} (alt₁ .false p₁ p₂) = parse  n      p₁ ∣   parse  n   p₂

  parse↑ : forall n {e tok c r} -> Parser tok (e , c) r -> P tok n n r
  parse↑ n       {true}  p = parse n p
  parse↑ zero    {false} p = ∅
  parse↑ (suc n) {false} p = parse (suc n) p >>= \r ->
                             modify ↑ >>
                             return r

  eat : forall {tok n} -> BoundedVec tok (suc n) -> P tok (suc n) n tok
  eat []      = ∅
  eat (c ∷ s) = put s >> return c
