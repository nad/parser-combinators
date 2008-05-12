------------------------------------------------------------------------
-- A terminating parser data type and the accompanying interpreter
------------------------------------------------------------------------

module RecursiveDescent.InductiveWithFix.Internal where

open import RecursiveDescent.Type
open import Data.Bool
open import Data.Product.Record
open import Data.Maybe
open import Data.BoundedVec.Inefficient
import Data.List as L
open import Data.Nat
open import Category.Applicative.Indexed
open import Category.Monad.Indexed
open import Category.Monad.State
open import Utilities

------------------------------------------------------------------------
-- Lifting non-terminals

-- Extends a non-terminal type with a fresh non-terminal.

data Lift (i : Index) (r : Set) (nt : ParserType) : ParserType where
  fresh : Lift i r nt i r
  ↟     : forall {i' r'} -> nt i' r' -> Lift i r nt i' r'

------------------------------------------------------------------------
-- Parser data type

-- A type for parsers which can be implemented using recursive
-- descent. The types used ensure that the implementation below is
-- structurally recursive.

-- The parsers are indexed on a type of nonterminals.

data Parser (tok : Set) (nt : ParserType) : ParserType where
  !_     :  forall {e c r}
         -> nt (e , c) r -> Parser tok nt (e , step c) r
  fix    :  forall {i r}
         -> Parser tok (Lift i r nt) i r
         -> Parser tok nt i r
  symbol :  Parser tok nt (false , leaf) tok
  ret    :  forall {r} -> r -> Parser tok nt (true , leaf) r
  fail   :  forall {r} -> Parser tok nt (false , leaf) r
  bind₀  :  forall {c₁ e₂ c₂ r₁ r₂}
         -> Parser tok nt (true , c₁) r₁
         -> (r₁ -> Parser tok nt (e₂ , c₂) r₂)
         -> Parser tok nt (e₂ , node c₁ c₂) r₂
  bind₁  :  forall {c₁ r₁ r₂} {i₂ : r₁ -> Index}
         -> Parser tok nt (false , c₁) r₁
         -> ((x : r₁) -> Parser tok nt (i₂ x) r₂)
         -> Parser tok nt (false , c₁) r₂
  alt₀   :  forall {c₁ e₂ c₂ r}
         -> Parser tok nt (true , c₁)         r
         -> Parser tok nt (e₂   , c₂)         r
         -> Parser tok nt (true , node c₁ c₂) r
  alt₁   :  forall {c₁} e₂ {c₂ r}
         -> Parser tok nt (false , c₁)         r
         -> Parser tok nt (e₂    , c₂)         r
         -> Parser tok nt (e₂    , node c₁ c₂) r

------------------------------------------------------------------------
-- Lifting parsers

Map : (ParserType -> ParserType) -> Set2
Map F = forall {nt nt' i r} ->
        (nt i r -> nt' i r) -> (F nt i r -> F nt' i r)

liftMap : forall (F : ParserType -> ParserType) {i' r'} ->
          Map F -> Map (Lift i' r' ∘₂ F)
liftMap F map g fresh = fresh
liftMap F map g (↟ x) = ↟ (map g x)

lift' : forall {tok nt i r i' r'}
        (F : ParserType -> ParserType) -> Map F ->
        Parser tok (F nt) i r -> Parser tok (F (Lift i' r' nt)) i r
lift' F map (! x)           = ! (map ↟ x)
lift' F map (fix {i} {r} p) = fix (lift' (Lift i r ∘₂ F) (liftMap F map) p)
lift' F map symbol          = symbol
lift' F map (ret x)         = ret x
lift' F map fail            = fail
lift' F map (bind₀  p₁ p₂)  = bind₀  (lift' F map p₁) (\x -> lift' F map (p₂ x))
lift' F map (bind₁  p₁ p₂)  = bind₁  (lift' F map p₁) (\x -> lift' F map (p₂ x))
lift' F map (alt₀   p₁ p₂)  = alt₀   (lift' F map p₁) (lift' F map p₂)
lift' F map (alt₁ e p₁ p₂)  = alt₁ e (lift' F map p₁) (lift' F map p₂)

-- Note that lift p is linear in the size of p (in a sense; note that
-- p can contain higher-order components), assuming that p contains at
-- most <some constant> occurrences of fix.

lift : forall {tok nt i r i' r'} ->
       Parser tok nt i r -> Parser tok (Lift i' r' nt) i r
lift p = lift' (\nt -> nt) (\f -> f) p

------------------------------------------------------------------------
-- Run function for the parsers

-- Grammars.

Grammar : Set -> ParserType -> Set1
Grammar tok nt = forall {i r} -> nt i r -> Parser tok nt i r

-- Extends a grammar with a case for a fresh non-terminal.

_▷_ : forall {tok nt i r} ->
      Grammar tok nt -> Parser tok nt i r ->
      Grammar tok (Lift i r nt)
(g ▷ p) fresh = lift p
(g ▷ p) (↟ x) = lift (g x)

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

-- The pattern matching on {e = ...} in parse is only there to work
-- around a bug in Agda's coverage checker.

mutual
  parse : forall {tok nt} -> Grammar tok nt ->
          forall n {e c r} ->
          Parser tok nt (e , c) r ->
          P tok n (if e then n else pred n) r
  parse g n       (! x)              = parse g n (g x)
  parse g n       (fix p)            = parse (g ▷ fix p) n p
  parse g zero    symbol             = ∅
  parse g (suc n) symbol             = eat =<< get
  parse g n       (ret x)            = return x
  parse g n       fail               = ∅
  parse g n       (bind₀      p₁ p₂) = parse  g  n      p₁ >>= parse  g n ∘′ p₂
  parse g zero    (bind₁      p₁ p₂) = ∅
  parse g (suc n) (bind₁      p₁ p₂) = parse  g (suc n) p₁ >>= parse↑ g n ∘′ p₂
  parse g n       (alt₀       p₁ p₂) = parse  g  n      p₁ ∣   parse↑ g n    p₂
  parse g n {e = true}  (alt₁ .true  p₁ p₂) = parse↑ g  n      p₁ ∣   parse  g n    p₂
  parse g n {e = false} (alt₁ .false p₁ p₂) = parse  g  n      p₁ ∣   parse  g n    p₂

  parse↑ : forall {tok nt} -> Grammar tok nt ->
           forall n {e c r} -> Parser tok nt (e , c) r -> P tok n n r
  parse↑ g n       {true}  p = parse g n p
  parse↑ g zero    {false} p = ∅
  parse↑ g (suc n) {false} p = parse g (suc n) p >>= \r ->
                               modify ↑ >>
                               return r

  eat : forall {tok n} -> BoundedVec tok (suc n) -> P tok (suc n) n tok
  eat []      = ∅
  eat (c ∷ s) = put s >> return c
