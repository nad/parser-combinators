------------------------------------------------------------------------
-- A terminating parser data type and the accompanying interpreter
------------------------------------------------------------------------

module Parser.Internal where

open import Parser.Type
open import Data.Bool
open import Data.Maybe
open import Data.Function
import Data.BoundedVec as BVec
open BVec using (BoundedVec; []v; _∷v_; ↑)
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

-- The parsers are indexed on a type of names.

data Parser (tok : Set) (name : ParserType) : ParserType where
  ret   :  forall {r} -> r -> Parser tok name true leaf r
  sat   :  forall {r}
        -> (tok -> Maybe r)
        -> Parser tok name false leaf r
  seq₀  :  forall {d₁ e₂ d₂ r₁ r₂}
        -> Parser tok name true d₁           (r₁ -> r₂)
        -> Parser tok name e₂   d₂           r₁
        -> Parser tok name e₂   (node d₁ d₂) r₂
  seq₁  :  forall {d₁} e₂ {d₂ r₁ r₂}
        -> Parser tok name false d₁        (r₁ -> r₂)
        -> Parser tok name e₂    d₂        r₁
        -> Parser tok name false (step d₁) r₂
  alt₀  :  forall {d₁} e₂ {d₂ r}
        -> Parser tok name true d₁           r
        -> Parser tok name e₂   d₂           r
        -> Parser tok name true (node d₁ d₂) r
  alt₁  :  forall {d₁ e₂ d₂ r}
        -> Parser tok name false d₁           r
        -> Parser tok name e₂    d₂           r
        -> Parser tok name e₂    (node d₁ d₂) r
  !_    :  forall {e d r}
        -> name e d r -> Parser tok name e (step d) r
  bind₀ :  forall {d₁ e₂ d₂ r₁ r₂}
        -> Parser tok name true d₁ r₁
        -> (r₁ -> Parser tok name e₂ d₂ r₂)
        -> Parser tok name e₂ (node d₁ d₂) r₂
  bind₁ :  forall {d₁} e₂ {d₂ r₁ r₂}
        -> Parser tok name false d₁ r₁
        -> (r₁ -> Parser tok name e₂ d₂ r₂)
        -> Parser tok name false (step d₁) r₂

------------------------------------------------------------------------
-- Run function for the parsers

-- Grammars.

Grammar : Set -> ParserType -> Set1
Grammar tok name = forall {e d r} -> name e d r -> Parser tok name e d r

-- Parser monad.

P : Set -> IFun ℕ
P tok = IStateT (BoundedVec tok) L.[_]

PIMonadPlus : (tok : Set) -> RawIMonadPlus (P tok)
PIMonadPlus tok = StateTIMonadPlus (BoundedVec tok) L.ListMonadPlus

PIMonadState : (tok : Set) -> RawIMonadState (BoundedVec tok) (P tok)
PIMonadState tok = StateTIMonadState (BoundedVec tok) L.ListMonad

private
  open module LM {tok : Set} = IMonadPlusOps  (PIMonadPlus  tok)
  open module SM {tok : Set} = IMonadStateOps (PIMonadState tok)

-- For every successful parse the run function returns the remaining
-- string. (Since there can be several successful parses a list of
-- strings is returned.)

-- This function is structurally recursive with respect to the
-- following lexicographic measure:
--
-- 1) The upper bound of the input string.
-- 2) The depth of the parser.

private
  module Dummy {tok : Set} {name : ParserType}
               (g : Grammar tok name)
               where

    mutual
      parse₀ : forall d {r} ->
               Parser tok name true d r ->
               forall n -> P tok n n r
      parse₀ leaf       (ret x)            n = return x
      parse₀ (node _ _) (bind₀      p₁ p₂) n = parse₀ _ p₁ n >>= \x -> parse₀ _ (p₂ x) n
      parse₀ (node _ _) (seq₀       p₁ p₂) n = parse₀ _ p₁ n <*> parse₀ _ p₂ n
      parse₀ (node _ _) (alt₀ true  p₁ p₂) n = parse₀ _ p₁ n ++  parse₀ _ p₂ n
      parse₀ (node _ _) (alt₀ false p₁ p₂) n = parse₀ _ p₁ n ++  parse₁↑  p₂ n
      parse₀ (node _ _) (alt₁       p₁ p₂) n = parse₁↑  p₁ n ++  parse₀ _ p₂ n
      parse₀ (step _)   (! x)              n = parse₀ _ (g x) n

      parse₁↑ : forall {d r} ->
                Parser tok name false d r ->
                forall n -> P tok n n r
      parse₁↑ p zero    = mzero
      parse₁↑ p (suc n) = parse₁ _ p (suc n) >>= \r -> modify ↑ >> return r

      parse₁ : forall d {r} ->
               Parser tok name false d r ->
               forall n -> P tok n (pred n) r
      parse₁ _        _       zero     = mzero
      parse₁ leaf {r} (sat p) (suc n)  = eat ∘ BVec.view =<< get
        where
          eat : forall {n} -> BVec.View tok (suc n) -> P tok (suc n) n r
          eat []v      = mzero
          eat (c ∷v s) with p c
          ... | just x  = put s >> return x
          ... | nothing = mzero
      parse₁ (node _ _) (seq₀        p₁ p₂) (suc n) = parse₀ _ p₁ (suc n) <*> parse₁ _ p₂ (suc n)
      parse₁ (node _ _) (bind₀       p₁ p₂) (suc n) = parse₀ _ p₁ (suc n) >>= \x -> parse₁ _ (p₂ x) (suc n)
      parse₁ (step _)   (seq₁  true  p₁ p₂) (suc n) = parse₁ _ p₁ (suc n) <*> parse₀ _ p₂ n
      parse₁ (step _)   (seq₁  false p₁ p₂) (suc n) = parse₁ _ p₁ (suc n) <*> parse₁↑  p₂ n
      parse₁ (step _)   (bind₁ true  p₁ p₂) (suc n) = parse₁ _ p₁ (suc n) >>= \x -> parse₀ _ (p₂ x) n
      parse₁ (step _)   (bind₁ false p₁ p₂) (suc n) = parse₁ _ p₁ (suc n) >>= \x -> parse₁↑  (p₂ x) n
      parse₁ (node _ _) (alt₁        p₁ p₂) (suc n) = parse₁ _ p₁ (suc n) ++  parse₁ _ p₂ (suc n)
      parse₁ (step _)   (! x)               (suc n) = parse₁ _ (g x) (suc n)

    parse : forall e {d r} ->
            Parser tok name e d r -> (n : ℕ) ->
            P tok (suc n) (if e then suc n else n) r
    parse true  p n = parse₀ _ p (suc n)
    parse false p n = parse₁ _ p (suc n)

open Dummy public
