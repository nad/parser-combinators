------------------------------------------------------------------------
-- Terminating parsers
------------------------------------------------------------------------

-- A DSEL for parsers which can be implemented using recursive
-- descent. The types used ensure that these implementations will
-- always terminate.

module ParserR where

open import Data.Bool
open import Data.Product
open import Data.Function
open import Data.BoundedVec
import Data.List as L
open import Data.Nat
open import Logic
open import Monad
open import Relation.Nullary
open import Relation.Binary

------------------------------------------------------------------------
-- Indices to the parser type

-- Does the parser accept empty strings?

Empty : Set
Empty = Bool

-- The spine of the parser, except that the right argument of _·_ is
-- omitted if the left one does not accept empty strings. (This is
-- encoded using maybeNode.)

data Depth : Set where
  leaf : Depth
  step : Depth -> Depth
  node : Depth -> Depth -> Depth

------------------------------------------------------------------------
-- Parsers

-- Parsers, indexed on a type of names.

infix  60 !_
infixr 50 _·₀_ _·₁_ _·_
infixr 40 _∣₀_ _∣₁_ _∣_

ParserType : Set2
ParserType = Empty -> Depth -> Set -> Set1

data Parser (tok : Set) (name : ParserType) : ParserType where
  fail  :  forall {r} -> Parser tok name false leaf r
  ret   :  forall {r} -> r -> Parser tok name true  leaf r
  sym   :  (tok -> Bool) -> Parser tok name false leaf tok
  _·₀_  :  forall {d₁ e₂ d₂ r₁ r₂}
        -> Parser tok name true d₁ (r₁ -> r₂) -> Parser tok name e₂ d₂ r₁
        -> Parser tok name e₂ (node d₁ d₂) r₂
  _·₁_  :  forall {d₁ e₂ d₂ r₁ r₂}
        -> Parser tok name false d₁ (r₁ -> r₂) -> Parser tok name e₂ d₂ r₁
        -> Parser tok name false (step d₁) r₂
  _∣₀_  :  forall {d₁ e₂ d₂ r}
        -> Parser tok name true d₁ r -> Parser tok name e₂ d₂ r
        -> Parser tok name true (node d₁ d₂) r
  _∣₁_  :  forall {d₁ e₂ d₂ r}
        -> Parser tok name false d₁ r -> Parser tok name e₂ d₂ r
        -> Parser tok name e₂ (node d₁ d₂) r
  !_    :  forall {e d r}
        -> name e d r -> Parser tok name e (step d) r

_·_ : forall {tok name e₁ d₁ e₂ d₂ r₁ r₂} ->
      Parser tok name e₁ d₁ (r₁ -> r₂) -> Parser tok name e₂ d₂ r₁ ->
      Parser tok name (e₁ ∧ e₂) (if e₁ then node d₁ d₂ else step d₁) r₂
_·_ {e₁ = true } = _·₀_
_·_ {e₁ = false} = _·₁_

_∣_ : forall {tok name e₁ d₁ e₂ d₂ r} ->
      Parser tok name e₁ d₁ r -> Parser tok name e₂ d₂ r ->
      Parser tok name (e₁ ∨ e₂) (node d₁ d₂) r
_∣_ {e₁ = true } = _∣₀_
_∣_ {e₁ = false} = _∣₁_


------------------------------------------------------------------------
-- Renaming parsers

-- Is this useful?

rename :  forall {tok name₁ name₂}
       -> (forall {e d r} -> name₁ e d r -> name₂ e d r)
       -> forall {e d r} -> Parser tok name₁ e d r -> Parser tok name₂ e d r
rename f fail      = fail
rename f (ret x)   = ret x
rename f (sym p)   = sym p
rename f (p₁ ·₀ p₂) = rename f p₁ ·₀ rename f p₂
rename f (p₁ ·₁ p₂) = rename f p₁ ·₁ rename f p₂
rename f (p₁ ∣₀ p₂) = rename f p₁ ∣₀ rename f p₂
rename f (p₁ ∣₁ p₂) = rename f p₁ ∣₁ rename f p₂
rename f (! x)     = ! f x


------------------------------------------------------------------------
-- Some derived parsers

module Token (a : DecSetoid) where

  private
    open module D = DecSetoid a
    open module S = Setoid setoid renaming (carrier to tok)

  -- Parses a given token.

  token : forall {name} -> tok -> Parser tok name false leaf tok
  token x = sym p
    where
    p : tok -> Bool
    p y with x ≟ y
    ... | yes _ = true
    ... | no  _ = false

------------------------------------------------------------------------
-- Run function for the parsers

-- Grammars.

Grammar : Set -> ParserType -> Set1
Grammar tok name = forall {e d r} -> name e d r -> Parser tok name e d r

-- Parser monad.

P : Set -> Set -> Set
P toks r = L.[_] (r × toks)

private
  open module LM = MonadPlusOps _ L.ListMonadPlus


-- For every successful parse the run function returns the remaining
-- string. (Since there can be several successful parses a list of
-- strings is returned.)

-- Implemented using an ugly workaround since the termination
-- checker does not take advantage of dotted patterns...

-- This function is structurally recursive with respect to the
-- following lexicographic measure:
--
-- 1) The upper bound of the input string.
-- 2) The depth of the parser.

private

  open L using ([_])

  _>>*_ : forall {a b c d} -> [ (a -> b) × c ] -> (c -> [ a × d ]) -> [ b × d ]
  fs >>* xs = fs            >>= \fc ->
              xs (proj₂ fc) >>= \xc ->
              return (proj₁ fc (proj₁ xc) , proj₂ xc)

  _<$>*_ : forall {a b c} -> (b -> c) -> [ a × b ] -> [ a × c ]
  f <$>* m = map-× id f <$> m

  maybeSuc : Empty -> ℕ -> ℕ
  maybeSuc e = if e then suc else id

  ⟦_⟧' :  forall {tok name e d r}
       -> Parser tok name e d r -> Grammar tok name
       -> forall {n}
       -> BoundedVec tok (suc n) -> P (BoundedVec tok (maybeSuc e n)) r
  ⟦_⟧' {tok = tok} {name = name} {e = e} p g = parse _ p _
    where
    mutual
      parse₀ : forall d {r} ->
               Parser tok name true d r -> (n : ℕ) -> BoundedVec tok n -> P (BoundedVec tok n) r
      parse₀ leaf       (ret x)                   n s = return (x , s)
      parse₀ (node _ _) (p₁ ·₀ p₂)                n s = parse₀ _ p₁ n s >>* parse₀ _ p₂ n
      parse₀ (node _ _) (_∣₀_ {e₂ = true } p₁ p₂) n s = parse₀ _ p₁ n s ++  parse₀ _ p₂ n s
      parse₀ (node _ _) (_∣₀_ {e₂ = false} p₁ p₂) n s = parse₀ _ p₁ n s ++  parse₁↑  p₂ n s
      parse₀ (node _ _) (p₁ ∣₁ p₂)                n s = parse₁↑  p₁ n s ++  parse₀ _ p₂ n s
      parse₀ (step _)   (! x)                     n s = parse₀ _ (g x) n s

      parse₁↑ : forall {d r} -> Parser tok name false d r -> (n : ℕ) ->
                BoundedVec tok n -> P (BoundedVec tok n) r
      parse₁↑ p zero    s = mzero
      parse₁↑ p (suc n) s = ↑ <$>* parse₁ _ p (suc n) s

      parse₁ : forall d {r} ->
               Parser tok name false d r -> (n : ℕ) -> BoundedVec tok n -> P (BoundedVec tok (pred n)) r
      parse₁ _          _                         zero    s  = mzero
      parse₁ leaf       fail                      (suc n) s  = mzero
      parse₁ leaf       (sym p)                   (suc n) [] = mzero
      parse₁ leaf       (sym p)                   (suc n) (c ∷ s) with p c
      ... | true  = return (c , s)
      ... | false = mzero
      parse₁ (node _ _) (p₁ ·₀ p₂)                (suc n) s = parse₀ _ p₁ _ s >>* parse₁ _ p₂ _
      parse₁ (step _)   (_·₁_ {e₂ = true } p₁ p₂) (suc n) s = parse₁ _ p₁ _ s >>* parse₀ _ p₂ _
      parse₁ (step _)   (_·₁_ {e₂ = false} p₁ p₂) (suc n) s = parse₁ _ p₁ _ s >>* parse₁↑  p₂ _
      parse₁ (node _ _) (p₁ ∣₁ p₂)                (suc n) s = parse₁ _ p₁ _ s ++  parse₁ _ p₂ _ s
      parse₁ (step _)   (! x)                     (suc n) s = parse₁ _ (g x) _ s

    parse : forall e {d r} ->
            Parser tok name e d r -> (n : ℕ) -> BoundedVec tok (suc n) -> P (BoundedVec tok (maybeSuc e n)) r
    parse true  p n s = parse₀ _ p _ s
    parse false p n s = parse₁ _ p _ s

open L

⟦_⟧ :  forall {tok name e d r}
    -> Parser tok name e d r -> Grammar tok name
    -> [ tok ] -> P [ tok ] r
⟦ p ⟧ g s = toList <$>* ⟦ p ⟧' g (↑ (fromList s))
