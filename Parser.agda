------------------------------------------------------------------------
-- Terminating parsers
------------------------------------------------------------------------

-- A DSEL for parsers which can be implemented using recursive
-- descent. The types used ensure that these implementations will
-- always terminate.

-- However, the parse function below is not (currently) accepted by
-- the termination checker, so the termination checker is turned
-- off...

{-# OPTIONS --dont-termination-check #-}

open import Relation.Binary

module Parser where

open import Data.Bool
open import Data.List hiding (_++_)
open import Data.Product
open import Logic
open import Monad
open import Relation.Nullary

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
maybeNode e d₁ d₂ = if e then node d₁ d₂ else d₁

-- The indices to the Parser type (used to instantiate the
-- heterogeneous collection module).

Index : Set
Index = Empty × Depth

private
  import HeterogeneousCollection as HC
  module HC' = HC Index
  open HC' public hiding (Coll)
  open HC' using (Coll)

------------------------------------------------------------------------
-- Parsers

-- Parsers. The context lists all named parsers which can be used.

infix  60 !_
infixr 50 _·_
infixr 40 _∣_

data Parser (tok : Set) (Γ : Ctxt) : Empty -> Depth -> Set where
  fail  :  Parser tok Γ false leaf
  empty :  Parser tok Γ true  leaf
  sym   :  (tok -> Bool) -> Parser tok Γ false leaf
  _·_   :  forall {e₁ d₁ e₂ d₂}
        -> Parser tok Γ e₁ d₁ -> Parser tok Γ e₂ d₂
        -> Parser tok Γ (e₁ ∧ e₂) (maybeNode e₁ d₁ d₂)
  _∣_   :  forall {e₁ d₁ e₂ d₂}
        -> Parser tok Γ e₁ d₁ -> Parser tok Γ e₂ d₂
        -> Parser tok Γ (e₁ ∨ e₂) (node d₁ d₂)
  !_    :  forall {e d}
        -> Label Γ (e , d) -> Parser tok Γ e (step d)

module Token (a : DecSetoid) where

  private
    open module D = DecSetoid a
    open module S = Setoid setoid

  token : forall {Γ} -> carrier -> Parser carrier Γ false leaf
  token x = sym p
    where
    p : carrier -> Bool
    p y with x ≟ y
    ... | yes _ = true
    ... | no  _ = false

------------------------------------------------------------------------
-- Run function for the parsers

-- Environments containing parsers.

Env : Set -> Ctxt -> Set
Env tok Γ = Coll P Γ
  where
  P : Index -> Set
  P (e , d) = Parser tok Γ e d

-- Parser monad.

P : Set -> Set
P = [_]

private
  open module LM = MonadPlusOps P ListMonadPlus

mutual

  -- For every successful parse the run function returns the remaining
  -- string. (Since there can be several successful parses a list of
  -- strings is returned.)

  -- Implemented using an ugly workaround since the termination
  -- checker does not take advantage of dotted patterns...

  ⟦_⟧ :  forall {tok Γ e d}
      -> Parser tok Γ e d -> Env tok Γ -> [ tok ] -> P [ tok ]
  ⟦ p ⟧ = parse _ p ≡-refl

  private

    parse :  forall {tok Γ e} d {d'}
          -> Parser tok Γ e d' -> d ≡ d'
          -> Env tok Γ -> [ tok ] -> P [ tok ]
    parse ._ fail    ≡-refl γ s       = zero
    parse ._ empty   ≡-refl γ s       = return s
    parse ._ (sym p) ≡-refl γ (c ∷ s) with p c
    ... | true  = return s
    ... | false = zero
    parse (node d₁ d₂) (_·_ {e₁ = true} p₁ p₂) ≡-refl γ s =
      ⟦ p₂ ⟧ γ =<< ⟦ p₁ ⟧ γ s
    parse d₁ (_·_ {e₁ = false} p₁ p₂) ≡-refl γ s =
      ⟦ p₂ ⟧ γ =<< ⟦ p₁ ⟧ γ s  -- This call is fine, but Agda cannot
                               -- see that it is.
    parse (node d₁ d₂) (p₁ ∣ p₂) ≡-refl γ s =
      ⟦ p₁ ⟧ γ s ++ ⟦ p₂ ⟧ γ s
    parse (step d) (! x) ≡-refl γ s = ⟦ lookup x γ ⟧ γ s
    parse _        _     _      γ s = zero
