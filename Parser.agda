------------------------------------------------------------------------
-- Terminating parsers
------------------------------------------------------------------------

-- A DSEL for parsers which can be implemented using recursive
-- descent. The types used ensure that these implementations will
-- always terminate.

module Parser where

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

maybeNode : Empty -> Depth -> Depth -> Depth
maybeNode e d₁ d₂ = if e then node d₁ d₂ else step d₁

------------------------------------------------------------------------
-- Parsers

-- Parsers, indexed on a type of names.

infix  60 !_
infixr 50 _·_
infixr 40 _∣_

ParserType : Set1
ParserType = Empty -> Depth -> Set

data Parser (tok : Set) (name : ParserType) : ParserType where
  fail  :  Parser tok name false leaf
  ε     :  Parser tok name true  leaf
  sym   :  (tok -> Bool) -> Parser tok name false leaf
  _·_   :  forall {e₁ d₁ e₂ d₂}
        -> Parser tok name e₁ d₁ -> Parser tok name e₂ d₂
        -> Parser tok name (e₁ ∧ e₂) (maybeNode e₁ d₁ d₂)
  _∣_   :  forall {e₁ d₁ e₂ d₂}
        -> Parser tok name e₁ d₁ -> Parser tok name e₂ d₂
        -> Parser tok name (e₁ ∨ e₂) (node d₁ d₂)
  !_    :  forall {e d}
        -> name e d -> Parser tok name e (step d)

------------------------------------------------------------------------
-- Renaming parsers

-- Is this useful?

rename :  forall {tok name₁ name₂}
       -> (forall {e d} -> name₁ e d -> name₂ e d)
       -> forall {e d} -> Parser tok name₁ e d -> Parser tok name₂ e d
rename f fail      = fail
rename f ε         = ε
rename f (sym p)   = sym p
rename f (p₁ · p₂) = rename f p₁ · rename f p₂
rename f (p₁ ∣ p₂) = rename f p₁ ∣ rename f p₂
rename f (! x)     = ! f x

------------------------------------------------------------------------
-- Some derived parsers

module Token (a : DecSetoid) where

  private
    open module D = DecSetoid a
    open module S = Setoid setoid renaming (carrier to tok)

  -- Parses a given token.

  token : forall {name} -> tok -> Parser tok name false leaf
  token x = sym p
    where
    p : tok -> Bool
    p y with x ≟ y
    ... | yes _ = true
    ... | no  _ = false

------------------------------------------------------------------------
-- Run function for the parsers

-- Grammars.

Grammar : Set -> ParserType -> Set
Grammar tok name = forall {e d} -> name e d -> Parser tok name e d

-- Parser monad.

P : Set -> Set
P = L.[_]

private
  open module LM = MonadPlusOps P L.ListMonadPlus

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

  maybeSuc : Empty -> ℕ -> ℕ
  maybeSuc e = if e then suc else id

  ⟦_⟧' :  forall {tok name e d}
       -> Parser tok name e d -> Grammar tok name
       -> forall {n}
       -> BoundedVec tok (suc n) -> P (BoundedVec tok (maybeSuc e n))
  ⟦_⟧' {tok = tok} {name = name} p g = parse _ p ≡-refl g
    where
    parse :  forall {e} d {d'}
          -> Parser tok name e d' -> d ≡ d' -> Grammar tok name
          -> forall {n} -> BoundedVec tok (suc n)
          -> P (BoundedVec tok (maybeSuc e n))
    parse ._ fail    ≡-refl g s       = mzero
    parse ._ ε       ≡-refl g s       = return s
    parse ._ (sym p) ≡-refl g []      = mzero
    parse ._ (sym p) ≡-refl g (c ∷ s) with p c
    ... | true  = return s
    ... | false = mzero

    parse (node d₁ d₂) (_·_ {e₁ = true}               p₁ p₂) ≡-refl g             s =        ⟦ p₂ ⟧' g =<< ⟦ p₁ ⟧' g s
    parse (step d₁)    (_·_ {e₁ = false} {e₂ = false} p₁ p₂) ≡-refl g {n = suc n} s = ↑ <$> (⟦ p₂ ⟧' g =<< ⟦ p₁ ⟧' g s)
    parse (step d₁)    (_·_ {e₁ = false} {e₂ = true}  p₁ p₂) ≡-refl g {n = suc n} s =        ⟦ p₂ ⟧' g =<< ⟦ p₁ ⟧' g s
    parse (step d₁)    (_·_ {e₁ = false} {e₂ = false} p₁ p₂) ≡-refl g {n = zero}  s = mzero
      -- None of p₁ and p₂ accept the empty string, and s has length at most 1.
    parse (step d₁)    (_·_ {e₁ = false} {e₂ = true}  p₁ p₂) ≡-refl g {n = zero}  []       = mzero
    parse (step d₁)    (_·_ {e₁ = false} {e₂ = true}  p₁ p₂) ≡-refl g {n = zero}  (c ∷ []) = ⟦ p₁ ⟧' g {n = zero} (c ∷ [])
      -- Note that p₁ does not accept the empty string, whereas p₂ does.

    parse (node d₁ d₂) (_∣_ {e₁ = true}  {e₂ = true}  p₁ p₂) ≡-refl g s =        ⟦ p₁ ⟧' g s  ++        ⟦ p₂ ⟧' g s
    parse (node d₁ d₂) (_∣_ {e₁ = true}  {e₂ = false} p₁ p₂) ≡-refl g s =        ⟦ p₁ ⟧' g s  ++ (↑ <$> ⟦ p₂ ⟧' g s)
    parse (node d₁ d₂) (_∣_ {e₁ = false} {e₂ = true}  p₁ p₂) ≡-refl g s = (↑ <$> ⟦ p₁ ⟧' g s) ++        ⟦ p₂ ⟧' g s
    parse (node d₁ d₂) (_∣_ {e₁ = false} {e₂ = false} p₁ p₂) ≡-refl g s =        ⟦ p₁ ⟧' g s  ++        ⟦ p₂ ⟧' g s

    parse (step d) (! x) ≡-refl g s = ⟦ g x ⟧' g s

    -- Impossible cases.
    parse leaf         (_·_ {e₁ = true}  p₁ p₂) () _ _
    parse (step d)     (_·_ {e₁ = true}  p₁ p₂) () _ _
    parse leaf         (_·_ {e₁ = false} p₁ p₂) () _ _
    parse (node d₁ d₂) (_·_ {e₁ = false} p₁ p₂) () _ _
    parse leaf         (! x)                    () _ _
    parse (node d₁ d₂) (! x)                    () _ _

open L

⟦_⟧ :  forall {tok name e d}
    -> Parser tok name e d -> Grammar tok name
    -> [ tok ] -> P [ tok ]
⟦ p ⟧ g s = toList <$> ⟦ p ⟧' g (↑ (fromList s))
