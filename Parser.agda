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
P = L.[_]

private
  open module LM = MonadPlusOps P L.ListMonadPlus

maybeSuc : Empty -> ℕ -> ℕ
maybeSuc e = if e then suc else id

mutual

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

    ⟦_⟧' :  forall {tok Γ e d}
         -> Parser tok Γ e d -> Env tok Γ
         -> forall {n}
         -> BoundedVec tok (suc n) -> P (BoundedVec tok (maybeSuc e n))
    ⟦ p ⟧' γ = parse p ≡-refl γ

    parse :  forall {tok Γ e d d'}
          -> Parser tok Γ e d' -> d ≡ d' -> Env tok Γ
          -> forall {n}
          -> BoundedVec tok (suc n) -> P (BoundedVec tok (maybeSuc e n))
    parse fail    ≡-refl γ s = mzero
    parse empty   ≡-refl γ s = return s
    parse (sym p) ≡-refl γ s with view s
    ... | []v     = mzero
    ... | c ∷v s' with p c
    ...   | true  = return s'
    ...   | false = mzero

    parse {d = node d₁ d₂} (_·_ {e₁ = true}               p₁ p₂) ≡-refl γ             s =        ⟦ p₂ ⟧' γ =<< ⟦ p₁ ⟧' γ s
    parse {d = step d₁}    (_·_ {e₁ = false} {e₂ = true}  p₁ p₂) ≡-refl γ {n = suc n} s =        ⟦ p₂ ⟧' γ =<< ⟦ p₁ ⟧' γ s
    parse {d = step d₁}    (_·_ {e₁ = false} {e₂ = false} p₁ p₂) ≡-refl γ {n = suc n} s = ↑ <*> (⟦ p₂ ⟧' γ =<< ⟦ p₁ ⟧' γ s)

    parse {d = node d₁ d₂} (_∣_ {e₁ = true}  {e₂ = true}  p₁ p₂) ≡-refl γ s =        ⟦ p₁ ⟧' γ s  ++        ⟦ p₂ ⟧' γ s
    parse {d = node d₁ d₂} (_∣_ {e₁ = true}  {e₂ = false} p₁ p₂) ≡-refl γ s =        ⟦ p₁ ⟧' γ s  ++ (↑ <*> ⟦ p₂ ⟧' γ s)
    parse {d = node d₁ d₂} (_∣_ {e₁ = false} {e₂ = true}  p₁ p₂) ≡-refl γ s = (↑ <*> ⟦ p₁ ⟧' γ s) ++        ⟦ p₂ ⟧' γ s
    parse {d = node d₁ d₂} (_∣_ {e₁ = false} {e₂ = false} p₁ p₂) ≡-refl γ s =        ⟦ p₁ ⟧' γ s  ++        ⟦ p₂ ⟧' γ s

    parse {d = step d} (! x) ≡-refl γ s = ⟦ lookup x γ ⟧' γ s
    parse _ _ γ s = mzero

open L

⟦_⟧ :  forall {tok Γ e d}
    -> Parser tok Γ e d -> Env tok Γ
    -> [ tok ] -> P [ tok ]
⟦ p ⟧ γ s = toList <*> ⟦ p ⟧' γ (↑ (fromList s))
