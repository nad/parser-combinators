------------------------------------------------------------------------
-- Terminating parsers
------------------------------------------------------------------------

-- A DSEL for parsers which can be implemented using recursive
-- descent. The types used ensure that these implementations will
-- always terminate.

module ParserR where

open import Data.Bool
open import Data.Maybe
open import Data.Product
open import Data.Function
import Data.BoundedVec as BVec
open BVec using (BoundedVec; []v; _∷v_; ↑)
import Data.List as L
open import Data.Nat
open import Logic
open import Category.Applicative.Indexed
open import Category.Monad
open import Category.Monad.Indexed
open import Category.Monad.State
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

ParserType : Set2
ParserType = Empty -> Depth -> Set -> Set1

mutual

  Parser : Set -> ParserType -> ParserType
  Parser = Parser'

  private

    -- The constructors are private, since they are overly specialised
    -- in order to simplify the implementation below.

    data Parser' (tok : Set) (name : ParserType) : ParserType where
      ret'  :  forall {r} -> r -> Parser tok name true leaf r
      sat'  :  forall {r}
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
      rec   :  forall {e d r}
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
-- Exported parsers

infix  60 !_
infixr 50 _·_
infixr 40 _∣_
infixl 30 _⟫=_

ret : forall {tok name r} -> r -> Parser tok name true leaf r
ret = ret'

sat : forall {tok name r} ->
      (tok -> Maybe r) -> Parser tok name false leaf r
sat = sat'

fail : forall {tok name r} -> Parser tok name false leaf r
fail = sat (const nothing)

_·_ : forall {tok name e₁ d₁ e₂ d₂ r₁ r₂} ->
      Parser tok name e₁ d₁ (r₁ -> r₂) ->
      Parser tok name e₂ d₂ r₁ ->
      Parser tok name (e₁ ∧ e₂) (if e₁ then node d₁ d₂ else step d₁) r₂
_·_ {e₁ = true } = seq₀
_·_ {e₁ = false} = seq₁ _

_∣_ : forall {tok name e₁ d₁ e₂ d₂ r} ->
      Parser tok name e₁ d₁ r ->
      Parser tok name e₂ d₂ r ->
      Parser tok name (e₁ ∨ e₂) (node d₁ d₂) r
_∣_ {e₁ = true } = alt₀ _
_∣_ {e₁ = false} = alt₁

_⟫=_
  : forall {tok name e₁ d₁ e₂ d₂ r₁ r₂} ->
    Parser tok name e₁ d₁ r₁ ->
    (r₁ -> Parser tok name e₂ d₂ r₂) ->
    Parser tok name (e₁ ∧ e₂) (if e₁ then node d₁ d₂ else step d₁) r₂
_⟫=_ {e₁ = true } = bind₀
_⟫=_ {e₁ = false} = bind₁ _

!_ : forall {tok name e d r} ->
     name e d r -> Parser tok name e (step d) r
!_ = rec

module Token (a : DecSetoid) where

  private
    open module D = DecSetoid a
    open module S = Setoid setoid renaming (carrier to tok)

  -- Parses a given token.

  token : forall {name} -> tok -> Parser tok name false leaf tok
  token x = sat p
    where
    p : tok -> Maybe tok
    p y with x ≟ y
    ... | yes _ = just y
    ... | no  _ = nothing

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

-- For every successful parse the run function returns the remaining
-- string. (Since there can be several successful parses a list of
-- strings is returned.)

-- This function is structurally recursive with respect to the
-- following lexicographic measure:
--
-- 1) The upper bound of the input string.
-- 2) The depth of the parser.

module Internal {tok : Set} {name : ParserType}
                (g : Grammar tok name)
                where
  private
    open module LM {tok : Set} = IMonadPlusOps  (PIMonadPlus  tok)
    open module SM {tok : Set} = IMonadStateOps (PIMonadState tok)

  mutual
    parse₀ : forall d {r} ->
             Parser tok name true d r ->
             forall n -> P tok n n r
    parse₀ leaf       (ret' x)           n = return x
    parse₀ (node _ _) (bind₀      p₁ p₂) n = parse₀ _ p₁ n >>= \x -> parse₀ _ (p₂ x) n
    parse₀ (node _ _) (seq₀       p₁ p₂) n = parse₀ _ p₁ n <*> parse₀ _ p₂ n
    parse₀ (node _ _) (alt₀ true  p₁ p₂) n = parse₀ _ p₁ n ++  parse₀ _ p₂ n
    parse₀ (node _ _) (alt₀ false p₁ p₂) n = parse₀ _ p₁ n ++  parse₁↑  p₂ n
    parse₀ (node _ _) (alt₁       p₁ p₂) n = parse₁↑  p₁ n ++  parse₀ _ p₂ n
    parse₀ (step _)   (rec x)            n = parse₀ _ (g x) n

    parse₁↑ : forall {d r} ->
              Parser tok name false d r ->
              forall n -> P tok n n r
    parse₁↑ p zero    = mzero
    parse₁↑ p (suc n) = parse₁ _ p (suc n) >>= \r -> modify ↑ >> return r

    parse₁ : forall d {r} ->
             Parser tok name false d r ->
             forall n -> P tok n (pred n) r
    parse₁ _        _        zero     = mzero
    parse₁ leaf {r} (sat' p) (suc n)  = eat ∘ BVec.view =<< get
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
    parse₁ (step _)   (rec x)             (suc n) = parse₁ _ (g x) (suc n)

  parse : forall e {d r} ->
          Parser tok name e d r -> (n : ℕ) ->
          P tok (suc n) (if e then suc n else n) r
  parse true  p n = parse₀ _ p (suc n)
  parse false p n = parse₁ _ p (suc n)

open L

⟦_⟧ :  forall {tok name e d r}
    -> Parser tok name e d r -> Grammar tok name
    -> [ tok ] -> [ r × [ tok ] ]
⟦ p ⟧ g s = map (map-× id BVec.toList)
                (Internal.parse g _ p _ (↑ (BVec.fromList s)))