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
  seq₀   :  forall {c₁ e₂ c₂ r₁ r₂}
         -> Parser tok (true , c₁)         (r₁ -> r₂)
         -> Parser tok (e₂   , c₂)         r₁
         -> Parser tok (e₂   , node c₁ c₂) r₂
  seq₁   :  forall {c₁} e₂ {c₂ r₁ r₂}
         -> Parser tok (false , c₁)      (r₁ -> r₂)
         -> Parser tok (e₂    , c₂)      r₁
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
  parse₀ : forall {tok c r} ->
           Parser tok (true , c) r ->
           forall n -> P tok n n r
  parse₀ (ret x)            n = return x
  parse₀ (forget true  p)   n = parse₀  p n
  parse₀ (forget false p)   n = parse₁↑ p n
  parse₀ (seq₀       p₁ p₂) n = parse₀  p₁ n ⊛ parse₀  p₂ n
  parse₀ (alt₀ true  p₁ p₂) n = parse₀  p₁ n ∣ parse₀  p₂ n
  parse₀ (alt₀ false p₁ p₂) n = parse₀  p₁ n ∣ parse₁↑ p₂ n
  parse₀ (alt₁       p₁ p₂) n = parse₁↑ p₁ n ∣ parse₀  p₂ n

  parse₁ : forall {tok c r} ->
           Parser tok (false , c) r ->
           forall n -> P tok n (pred n) r
  parse₁ _                     zero    = ∅
  parse₁ (seq₀        p₁ p₂)   (suc n) = parse₀ p₁ (suc n) ⊛ parse₁  p₂ (suc n)
  parse₁ (seq₁  true  p₁ p₂)   (suc n) = parse₁ p₁ (suc n) ⊛ parse₀  p₂ n
  parse₁ (seq₁  false p₁ p₂)   (suc n) = parse₁ p₁ (suc n) ⊛ parse₁↑ p₂ n
  parse₁ (alt₁        p₁ p₂)   (suc n) = parse₁ p₁ (suc n) ∣ parse₁  p₂ (suc n)
  parse₁ {tok} {r = r} (sat p) (suc n) = eat =<< get
    where
      eat : forall {n} ->
            BoundedVec tok (suc n) ->
            P tok (suc n) n r
      eat []      = ∅
      eat (c ∷ s) with p c
      ... | just x  = put s >> return x
      ... | nothing = ∅

  parse₁↑ : forall {tok c r} ->
            Parser tok (false , c) r ->
            forall n -> P tok n n r
  parse₁↑ p zero    = ∅
  parse₁↑ p (suc n) = parse₁ p (suc n) >>= \r ->
                      modify ↑ >>
                      return r

parse : forall {tok e c r n} ->
        Parser tok (e , c) r ->
        P tok n (if e then n else pred n) r
parse {e = true}  {n = n} p = parse₀ p n
parse {e = false} {n = n} p = parse₁ p n
