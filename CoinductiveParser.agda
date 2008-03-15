------------------------------------------------------------------------
-- A terminating parser data type and the accompanying interpreter
------------------------------------------------------------------------

-- This code is based on "Parallel Parsing Processes" by Koen
-- Claessen.

-- Note that the type Base.Parser below is assumed to be coinductive.

module CoinductiveParser where

open import CoinductiveParser.Index

import Data.Product as Prod; open Prod using () renaming (_,_ to pair)
open import Data.Bool
open import Data.Nat
open import Data.Product.Record
open import Data.List
open import Category.Monad.State
open import Logic
open import Data.Function
open import Data.Maybe

------------------------------------------------------------------------
-- Parser monad

P : Set -> (Set -> Set)
P tok = StateT [ tok ] [_]

------------------------------------------------------------------------
-- Basic parsers (no CPS)

private
 module Base where

  -- returnPlus below takes a _list_ of immediate results, since
  -- otherwise the returnPlus/returnPlus case of _∣'_ would not type
  -- check. (Its type would have to be changed.)

  {- co -}
  data Parser (tok r : Set) : Index -> Set where
    symbolBind : forall {i : tok -> Index} ->
                 ((c : tok) -> Parser tok r (i c)) -> Parser tok r 0I
    fail       : Parser tok r 0I
    returnPlus : forall {e d} ->
                 [ r ] -> Parser tok r (e , d) ->
                 Parser tok r (true , suc d)

  -- Note that the type of this return function is not suitable if you
  -- want to state the monad laws (since (true , 1) is not a zero in
  -- the monoid which is used here). The return function defined below
  -- has a more suitable type, though.

  return : forall {tok r} -> r -> Parser tok r (true , 1)
  return x = returnPlus (x ∷ []) fail

  cast : forall {tok i₁ i₂ r} ->
         i₁ ≡ i₂ -> Parser tok r i₁ -> Parser tok r i₂
  cast ≡-refl p = p

  -- Note that this function is productive.

  infixl 0 _∣_

  _∣_ : forall {tok r i₁ i₂} ->
         Parser tok r i₁ -> Parser tok r i₂ ->
         Parser tok r (i₁ ∣I i₂)
  fail                ∣ p₂                = p₂
  p₁@(returnPlus _ _) ∣ fail              = p₁
  p₁@(symbolBind _)   ∣ fail              = p₁
  symbolBind f₁       ∣ symbolBind f₂     = symbolBind (\c -> f₁ c ∣ f₂ c)
  p₁@(symbolBind _)   ∣ returnPlus xs p₂  = returnPlus xs (p₁ ∣ p₂)
  returnPlus xs p₁    ∣ p₂@(symbolBind _) = returnPlus xs (p₂ ∣ p₁)
  returnPlus xs₁ p₁   ∣ returnPlus xs₂ p₂ = returnPlus (xs₁ ++ xs₂) (p₁ ∣ p₂)

  -- parse is structurally recursive over the following lexicographic
  -- measure:
  --
  -- ⑴ The input string.
  -- ⑵ The Distance index.
  --
  -- Note that Parser is viewed as being coinductive.

  parse : forall {tok r e d} ->
          Parser tok r (e , d) -> P tok r
  parse (symbolBind f)    (c ∷ s) = parse (f c) s
  parse (symbolBind f)    []      = []
  parse fail              _       = []
  parse (returnPlus xs p) s       = map (\x -> pair x s) xs ++ parse p s

------------------------------------------------------------------------
-- CPS transformation

-- The code below manually applies the continuation-passing monad
-- transformer to the Base parser above to improve the efficiency of
-- left-nested uses of bind.

data Parser (tok r : Set) (i : Index) : Set1 where
  parser : (forall {i' r'} ->
            (r -> Base.Parser tok r' i') ->
            Base.Parser tok r' (i ·I i')) ->
           Parser tok r i

private

  unP : forall {tok r i r' i'} ->
        Parser tok r i ->
        (r -> Base.Parser tok r' i') ->
        Base.Parser tok r' (i ·I i')
  unP (parser p) = p

symbol : forall {tok} -> Parser tok tok 0I
symbol = parser Base.symbolBind

fail : forall {tok r} -> Parser tok r 0I
fail = parser \k -> Base.fail

return : forall {tok r} -> r -> Parser tok r 1I
return x = parser \k -> k x

-- Note that _>>=_ cannot easily be given a dependent type (where the
-- second argument has type (x : r₁) -> Parser tok r₂ (i₂ x)). What
-- would the type of the result of _>>=_ be? The type would depend on
-- the input string, which is not an argument to _>>=_.

infixl 1 _>>=_

_>>=_ : forall {tok r₁ r₂ i₁ i₂} ->
        Parser tok r₁ i₁ -> (r₁ -> Parser tok r₂ i₂) ->
        Parser tok r₂ (i₁ ·I i₂)
_>>=_ {tok} {r₁} {r₂} {i₁} {i₂} (parser p) f = parser
  \{i₃} k -> Base.cast (sym $ *-assoc i₁ i₂ i₃)
                       (p \x -> unP (f x) k)
  where open IndexSemiring

infixl 0 _∣_

_∣_ : forall {tok r i₁ i₂} ->
      Parser tok r i₁ ->
      Parser tok r i₂ ->
      Parser tok r (i₁ ∣I i₂)
_∣_ {i₁ = i₁} {i₂ = i₂} (parser p₁) (parser p₂) =
  parser \{i₃} k ->
    Base.cast (sym $ Prod.proj₂ distrib i₃ i₁ i₂)
              (Base._∣_ (p₁ k) (p₂ k))
  where open IndexSemiring

-- Since _>>=_ has a non-dependent type it is hard to define sat
-- without using the underlying parsers in Base, and hence sat is
-- provided here.

sat : forall {tok r} ->
      (tok -> Maybe r) -> Parser tok r 0I
sat {tok} {r} p = parser \k -> Base.symbolBind (\c -> ok k (p c))
  where
  okIndex : Index -> Maybe r -> Index
  okIndex i' nothing  = 0I
  okIndex i' (just _) = i'

  ok : forall {r' i'} ->
       (r -> Base.Parser tok r' i') ->
       (x : Maybe r) -> Base.Parser tok r' (okIndex i' x)
  ok k nothing  = Base.fail
  ok k (just x) = k x

parse : forall {tok r i} ->
        Parser tok r i -> P tok r
parse (parser p) = Base.parse (p Base.return)

-- A variant which only returns parses which leave no remaining input.

parse-complete : forall {tok r i} ->
                 Parser tok r i -> [ tok ] -> [ r ]
parse-complete p s =
  map Prod.proj₁ (filter (null ∘ Prod.proj₂) (parse p s))
