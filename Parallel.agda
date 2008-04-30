------------------------------------------------------------------------
-- A terminating parser data type and the accompanying interpreter
------------------------------------------------------------------------

-- This code is based on "Parallel Parsing Processes" by Koen
-- Claessen.

-- Note that the type Base.Parser below is assumed to be coinductive.

module Parallel where

open import Parallel.Index

open import Data.Product renaming (_,_ to pair)
open import Data.Bool
open import Data.Nat
open import Data.Product.Record using (_,_)
import Data.List as List
open List using ([_]; []; _∷_; _++_)
import Data.Vec as Vec
open Vec using (Vec; []; _∷_) renaming (_++_ to _<+>_)
open import Category.Monad.State
open import Data.Function
open import Data.Maybe
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- Parser monad

P : Set -> (Set -> Set)
P tok = StateT [ tok ] [_]

------------------------------------------------------------------------
-- Basic parsers (no CPS)

private
 module Base where

  -- returnPlus below takes a _vector_ of immediate results, since
  -- otherwise the returnPlus/returnPlus case of _∣_ would not type
  -- check. (Its type would have to be changed.)
  --
  -- (The vector could just as well have been a list, if it were not
  -- for the unused module IncorrectBind below. However, documenting
  -- that this list is never empty is not a bad thing, and does not
  -- cost much.)

  {- co -}
  data Parser (tok r : Set) : Index -> Set where
    symbolBind : forall {i : tok -> Index} ->
                 ((c : tok) -> Parser tok r (i c)) -> Parser tok r 0I
    fail       : Parser tok r 0I
    returnPlus : forall {e d n} ->
                 Vec r (suc n) -> Parser tok r (e , d) ->
                 Parser tok r (true , suc d)

  -- Note that the type of this return function is not suitable if you
  -- want to state the monad laws (since (true , 1) is not a zero in
  -- the monoid which is used here). The return function defined below
  -- has a more suitable type, though.

  return : forall {tok r} -> r -> Parser tok r (true , 1)
  return x = returnPlus (Vec.singleton x) fail

  cast : forall {tok i₁ i₂ r} ->
         i₁ ≡ i₂ -> Parser tok r i₁ -> Parser tok r i₂
  cast ≡-refl p = p

  -- Note that this function is productive.

  infixl 0 _∣_

  _∣_ : forall {tok r i₁ i₂} ->
        Parser tok r i₁ -> Parser tok r i₂ -> Parser tok r (i₁ ∣I i₂)
  fail                ∣ p₂                = p₂
  p₁@(returnPlus _ _) ∣ fail              = p₁
  p₁@(symbolBind _)   ∣ fail              = p₁
  symbolBind f₁       ∣ symbolBind f₂     = symbolBind (\c -> f₁ c ∣ f₂ c)
  p₁@(symbolBind _)   ∣ returnPlus xs p₂  = returnPlus xs (p₁ ∣ p₂)
  returnPlus xs p₁    ∣ p₂@(symbolBind _) = returnPlus xs (p₂ ∣ p₁)
  returnPlus xs₁ p₁   ∣ returnPlus xs₂ p₂ = returnPlus (xs₁ <+> xs₂) (p₁ ∣ p₂)

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
  parse (returnPlus xs p) s       =
    List.map (\x -> pair x s) (Vec.toList xs) ++ parse p s

  -- It may be interesting to note that it is hard to define bind
  -- directly. Note that the module Incorrect is not used for
  -- anything; bind is defined further down using CPS.

  private
   module IncorrectBind where

    -- choice ≈ foldr₁ _∣_.

    choice : forall {tok r i n} ->
             Vec (Parser tok r i) (suc n) -> Parser tok r i
    choice {i = i} =
      Vec.foldr₁ (\p₁ p₂ -> cast (∣-idempotent i) (p₁ ∣ p₂))
      where open IndexSemiring

    -- This function is used to state the type of bind.

    bind-index : forall {tok r i} ->
                 Parser tok r i -> Index -> Index
    bind-index (symbolBind f)    _ = 0I
    bind-index fail              _ = 0I
    bind-index (returnPlus xs p) i = i

    open IndexSemiring

    bind-index-lemma : forall {tok r i₁} (p : Parser tok r i₁) i₂ ->
                       i₂ ∣I bind-index p i₂ ≡ i₂
    bind-index-lemma (symbolBind f)    i = proj₂ +-identity i
    bind-index-lemma fail              i = proj₂ +-identity i
    bind-index-lemma (returnPlus xs p) i = ∣-idempotent i

    -- Note that bind has a non-trivial type. This is not a
    -- fundamental problem, though. The big problem is that bind is
    -- not productive (in general). The recursive call p >>= g in the
    -- last line is not guarded if, for instance, g = const fail, in
    -- which case we have (ignoring some casts)
    --
    --   returnPlus xs p >>= g  =  p >>= g.
    --
    -- If furthermore p = returnPlus xs p, then we have a real
    -- problem.

    _>>=_ : forall {tok r₁ r₂ i₁ i₂} ->
            (p₁ : Parser tok r₁ i₁) -> (r₁ -> Parser tok r₂ i₂) ->
            Parser tok r₂ (bind-index p₁ i₂)
    symbolBind f    >>= g = symbolBind (\c -> f c >>= g)
    fail            >>= g = fail
    returnPlus xs p >>= g = cast (bind-index-lemma p _)
                                 (choice (Vec.map g xs) ∣ p >>= g)

------------------------------------------------------------------------
-- CPS transformation

-- The code below manually applies the continuation-passing monad
-- transformer to the Base parser above to improve the efficiency of
-- left-nested uses of bind. (And, in light of Base.Incorrect._>>=_,
-- to enable a well-founded definition of bind.)

data Parser (tok : Set) (i : Index) (r : Set) : Set1 where
  parser : (forall {i' r'} ->
            (r -> Base.Parser tok r' i') ->
            Base.Parser tok r' (i ·I i')) ->
           Parser tok i r

private

  unP : forall {tok r i r' i'} ->
        Parser tok i r ->
        (r -> Base.Parser tok r' i') ->
        Base.Parser tok r' (i ·I i')
  unP (parser p) = p

symbol : forall {tok} -> Parser tok 0I tok
symbol = parser Base.symbolBind

fail : forall {tok r} -> Parser tok 0I r
fail = parser \k -> Base.fail

return : forall {tok r} -> r -> Parser tok 1I r
return x = parser \k -> k x

-- Note that _>>=_ cannot easily be given a dependent type (where the
-- second argument has type (x : r₁) -> Parser tok r₂ (i₂ x)). What
-- would the type of the result of _>>=_ be? The type would depend on
-- the input string, which is not an argument to _>>=_.
--
-- Note also that the variant _!>>=_ from Parser/RecursiveDescent.Coinductive
-- cannot (?) be implemented, since the continuation given to p cannot
-- be dependently typed.

infixl 1 _>>=_

_>>=_ : forall {tok r₁ r₂ i₁ i₂} ->
        Parser tok i₁ r₁ -> (r₁ -> Parser tok i₂ r₂) ->
        Parser tok (i₁ ·I i₂) r₂
_>>=_ {i₁ = i₁} {i₂} (parser p) f = parser
  \{i₃} k -> Base.cast (sym $ *-assoc i₁ i₂ i₃)
                       (p \x -> unP (f x) k)
  where open IndexSemiring

infixl 0 _∣_

_∣_ : forall {tok r i₁ i₂} ->
      Parser tok i₁         r ->
      Parser tok i₂         r ->
      Parser tok (i₁ ∣I i₂) r
_∣_ {i₁ = i₁} {i₂ = i₂} (parser p₁) (parser p₂) =
  parser \{i₃} k ->
    Base.cast (sym $ proj₂ distrib i₃ i₁ i₂)
              (Base._∣_ (p₁ k) (p₂ k))
  where open IndexSemiring

-- Since _>>=_ has a non-dependent type it is hard to define sat
-- without using the underlying parsers in Base, and hence sat is
-- provided here.

sat : forall {tok r} ->
      (tok -> Maybe r) -> Parser tok 0I r
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
        Parser tok i r -> P tok r
parse (parser p) = Base.parse (p Base.return)

-- A variant which only returns parses which leave no remaining input.

parse-complete : forall {tok r i} ->
                 Parser tok i r -> [ tok ] -> [ r ]
parse-complete p s =
  List.map proj₁ (List.filter (List.null ∘ proj₂) (parse p s))
