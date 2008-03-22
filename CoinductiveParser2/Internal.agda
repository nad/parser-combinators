------------------------------------------------------------------------
-- A terminating parser data type and the accompanying interpreter
------------------------------------------------------------------------

-- Note that Parser is assumed to be coinductive.

module CoinductiveParser2.Internal where

open import Parser.Type
open import Data.Bool
open import Data.Product.Record
open import Data.Maybe
open import Category.Applicative.Indexed
open import Data.Nat
open import Category.Monad.State
open import Data.BoundedVec.Inefficient
import Data.List as L
open import Category.Monad.Indexed

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

{- co -}
data Parser (tok : Set) : Index -> Set -> Set1 where
  ret    :  forall {r} -> r -> Parser tok (true , leaf) r
  sat    :  forall {r}
         -> (tok -> Maybe r)
         -> Parser tok (false , leaf) r
  forget :  forall e {c r}
         -> Parser tok (e , c) r
         -> Parser tok (true , step c) r
  bind₀  :  forall {c₁ e₂ c₂ r₁ r₂}
         -> Parser tok (true , c₁) r₁
         -> (r₁ -> Parser tok (e₂ , c₂) r₂)
         -> Parser tok (e₂ , node c₁ c₂) r₂
  bind₁  :  forall {c₁} e₂ {c₂ r₁ r₂}
         -> Parser tok (false , c₁) r₁
         -> (r₁ -> Parser tok (e₂ , c₂) r₂)
         -> Parser tok (false , step c₁) r₂
  alt₀   :  forall {c₁} e₂ {c₂ r}
         -> Parser tok (true , c₁)         r
         -> Parser tok (e₂   , c₂)         r
         -> Parser tok (true , node c₁ c₂) r
  alt₁   :  forall {c₁ e₂ c₂ r}
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
  parse₀ : forall n {tok c r} ->
           Parser tok (true , c) r ->
           P tok n n r
  parse₀ n (ret x)            = return x
  parse₀ n (forget true  p)   = parse₀  n p
  parse₀ n (forget false p)   = parse₁↑ n p
  parse₀ n (bind₀      p₁ p₂) = parse₀  n p₁ >>= parse₀  n ∘ p₂
  parse₀ n (alt₀ true  p₁ p₂) = parse₀  n p₁ ∣   parse₀  n   p₂
  parse₀ n (alt₀ false p₁ p₂) = parse₀  n p₁ ∣   parse₁↑ n   p₂
  parse₀ n (alt₁       p₁ p₂) = parse₁↑ n p₁ ∣   parse₀  n   p₂

  parse₁ : forall n {tok r c} ->
           Parser tok (false , c) r ->
           P tok n (pred n) r
  parse₁ zero    _                   = ∅
  parse₁ (suc n) (bind₀       p₁ p₂) = parse₀ (suc n) p₁ >>= parse₁  (suc n) ∘ p₂
  parse₁ (suc n) (bind₁ true  p₁ p₂) = parse₁ (suc n) p₁ >>= parse₀  n       ∘ p₂
  parse₁ (suc n) (bind₁ false p₁ p₂) = parse₁ (suc n) p₁ >>= parse₁↑ n       ∘ p₂
  parse₁ (suc n) (alt₁        p₁ p₂) = parse₁ (suc n) p₁ ∣   parse₁  (suc n)   p₂
  parse₁ (suc n) {tok} {r} (sat p)   = eat =<< get
    where
      eat : forall {n} ->
            BoundedVec tok (suc n) ->
            P tok (suc n) n r
      eat []      = ∅
      eat (c ∷ s) with p c
      ... | just x  = put s >> return x
      ... | nothing = ∅

  parse₁↑ : forall n {tok c r} ->
            Parser tok (false , c) r ->
            P tok n n r
  parse₁↑ zero    p = ∅
  parse₁↑ (suc n) p = parse₁ (suc n) p >>= \r ->
                      modify ↑ >>
                      return r

parse : forall {tok e c r n} ->
        Parser tok (e , c) r ->
        P tok n (if e then n else pred n) r
parse {e = true}  {n = n} p = parse₀ n p
parse {e = false} {n = n} p = parse₁ n p
