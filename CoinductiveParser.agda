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
    symbolBind : forall {i} ->
                 (tok -> Parser tok r i) -> Parser tok r 0I
    fail       : Parser tok r 0I
    returnPlus : forall {e c} ->
                 [ r ] -> Parser tok r (e , c) ->
                 Parser tok r (true , suc c)

  -- Coinductive coeliminator.

  data ParserF (tok r : Set) (X : Index -> Set) : Index -> Set where
    symbolBindF : forall {i} ->
                  (tok -> X i) -> ParserF tok r X 0I
    failF       : ParserF tok r X 0I
    returnPlusF : forall {e c} ->
                  [ r ] -> X (e , c) ->
                  ParserF tok r X (true , suc c)
    -- Short-circuiting constructor; gives the final answer
    -- immediately, in one step.
    doneF       : forall {i} -> Parser tok r i -> ParserF tok r X i

  coelim : forall {tok r e d} -> let i = (e , d) in
           (X : Index -> Set) ->
           (forall {i} -> X i -> ParserF tok r X i) ->
           X i -> Parser tok r i
  coelim {e = e} {d = d} X step x with e | d | step x
  ... | ._ | ._ | symbolBindF f     = symbolBind (\c -> coelim X step (f c))
  ... | ._ | ._ | failF             = fail
  ... | ._ | ._ | returnPlusF xs x' = returnPlus xs (coelim X step x')
  ... | _  | _  | doneF p           = p

  cast : forall {tok i₁ i₂ r} ->
         i₁ ≡ i₂ -> Parser tok r i₁ -> Parser tok r i₂
  cast ≡-refl p = p

  -- Note that this function is productive.

  _∣_ : forall {tok r i₁ i₂} ->
        Parser tok r i₁ -> Parser tok r i₂ ->
        Parser tok r (i₁ ∣I i₂)
  _∣_ {tok} {r} p₁ p₂ = coelim X f < p₁ ∣ p₂ >
    where
    data X : Index -> Set where
      <_∣_> : forall {i₁ i₂} ->
              Parser tok r i₁ -> Parser tok r i₂ -> X (i₁ ∣I i₂)

    f : forall {i} -> X i -> ParserF tok r X i
    f < fail                ∣ p₂                > = doneF p₂
    f < p₁@(returnPlus _ _) ∣ fail              > = doneF p₁
    f < p₁@(symbolBind _)   ∣ fail              > = doneF p₁
    f < symbolBind f₁       ∣ symbolBind f₂     > = symbolBindF (\c -> < f₁ c ∣ f₂ c >)
    f < p₁@(symbolBind _)   ∣ returnPlus xs p₂  > = returnPlusF xs < p₁ ∣ p₂ >
    f < returnPlus xs p₁    ∣ p₂@(symbolBind _) > = returnPlusF xs < p₂ ∣ p₁ >
    f < returnPlus xs₁ p₁   ∣ returnPlus xs₂ p₂ > = returnPlusF (xs₁ ++ xs₂) < p₁ ∣ p₂ >

  -- parse is structurally recursive over the following lexicographic
  -- measure:
  --
  -- ⑴ The input string.
  -- ⑵ The Corners index.
  --
  -- Note that Parser is viewed as being coinductive.

  parse : forall {tok r e c} ->
          Parser tok r (e , c) -> P tok r
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

_>>=_ : forall {tok r₁ r₂ i₁ i₂} ->
        Parser tok r₁ i₁ -> (r₁ -> Parser tok r₂ i₂) ->
        Parser tok r₂ (i₁ ·I i₂)
_>>=_ {tok} {r₁} {r₂} {i₁} {i₂} (parser p) f = parser
  \{i₃} k -> Base.cast (sym $ *-assoc i₁ i₂ i₃)
                       (p \x -> unP (f x) k)
  where open IndexSemiring

_∣_ : forall {tok r i₁ i₂} ->
      Parser tok r i₁ ->
      Parser tok r i₂ ->
      Parser tok r (i₁ ∣I i₂)
_∣_ {i₁ = i₁} {i₂ = i₂} (parser p₁) (parser p₂) =
  parser \{i₃} k ->
    Base.cast (sym $ Prod.proj₂ distrib i₃ i₁ i₂)
              (Base._∣_ (p₁ k) (p₂ k))
  where open IndexSemiring

parse : forall {tok r i} ->
        Parser tok r i -> P tok r
parse {tok} {r} (parser p) = Base.parse (p k)
  where
  k : r -> Base.Parser tok r (true , 1)
  k x = Base.returnPlus (x ∷ []) Base.fail
