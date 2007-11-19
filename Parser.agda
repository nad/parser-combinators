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
open import Data.BoundedVec as BVec
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

-- Possible future extensions (if we can figure out how to support
-- these features):
--
-- * Parameterised parsers.
--
-- * Left-recursive parsers.

infix  60 !_
infixr 50 _·_
infixr 40 _∣_

data Parser (tok : Set) (Γ : Ctxt) : Empty -> Depth -> Set where
  fail  :  Parser tok Γ false leaf
  ε     :  Parser tok Γ true  leaf
  sym   :  (tok -> Bool) -> Parser tok Γ false leaf
  _·_   :  forall {e₁ d₁ e₂ d₂}
        -> Parser tok Γ e₁ d₁ -> Parser tok Γ e₂ d₂
        -> Parser tok Γ (e₁ ∧ e₂) (maybeNode e₁ d₁ d₂)
  _∣_   :  forall {e₁ d₁ e₂ d₂}
        -> Parser tok Γ e₁ d₁ -> Parser tok Γ e₂ d₂
        -> Parser tok Γ (e₁ ∨ e₂) (node d₁ d₂)
  !_    :  forall {e d}
        -> Label Γ (e , d) -> Parser tok Γ e (step d)

------------------------------------------------------------------------
-- Some derived parsers

module Token (a : DecSetoid) where

  private
    open module D = DecSetoid a
    open module S = Setoid setoid

  -- Parses a given token.

  token : forall {Γ} -> carrier -> Parser carrier Γ false leaf
  token x = sym p
    where
    p : carrier -> Bool
    p y with x ≟ y
    ... | yes _ = true
    ... | no  _ = false

-- Parses zero or more occurrences of the given parser (which may not
-- accept the empty string).
--
-- Note that this parser may be quite inconvenient to use, since it
-- needs to be included as the last parser in the context, and can
-- only be used with a fixed parameter parser.

many :  forall {tok Γ d}
     -> let d' = node leaf (step d) in
        Parser tok (Γ ▻ (true , d')) false d
     -> Parser tok (Γ ▻ (true , d')) true  d'
many p = ε ∣ p · ! lz

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

  ⟦_⟧' :  forall {tok Γ e d}
       -> Parser tok Γ e d -> Env tok Γ
       -> forall {n}
       -> BoundedVec tok (suc n) -> P (BoundedVec tok (maybeSuc e n))
  ⟦_⟧' {tok = tok} {Γ = Γ} p γ = parse _ p ≡-refl γ
    where
    parse :  forall {e} d {d'}
          -> Parser tok Γ e d' -> d ≡ d' -> Env tok Γ
          -> forall {n} -> BoundedVec tok (suc n)
          -> P (BoundedVec tok (maybeSuc e n))
    parse ._ fail    ≡-refl γ s       = mzero
    parse ._ ε       ≡-refl γ s       = return s
    parse ._ (sym p) ≡-refl γ []      = mzero
    parse ._ (sym p) ≡-refl γ (c ∷ s) with p c
    ... | true  = return s
    ... | false = mzero

    parse (node d₁ d₂) (_·_ {e₁ = true}               p₁ p₂) ≡-refl γ             s =        ⟦ p₂ ⟧' γ =<< ⟦ p₁ ⟧' γ s
    parse (step d₁)    (_·_ {e₁ = false} {e₂ = false} p₁ p₂) ≡-refl γ {n = suc n} s = ↑ <$> (⟦ p₂ ⟧' γ =<< ⟦ p₁ ⟧' γ s)
    parse (step d₁)    (_·_ {e₁ = false} {e₂ = true}  p₁ p₂) ≡-refl γ {n = suc n} s =        ⟦ p₂ ⟧' γ =<< ⟦ p₁ ⟧' γ s
    parse (step d₁)    (_·_ {e₁ = false} {e₂ = false} p₁ p₂) ≡-refl γ {n = zero}  s = mzero
      -- None of p₁ and p₂ accept the empty string, and s has length at most 1.
    parse (step d₁)    (_·_ {e₁ = false} {e₂ = true}  p₁ p₂) ≡-refl γ {n = zero}  []       = mzero
    parse (step d₁)    (_·_ {e₁ = false} {e₂ = true}  p₁ p₂) ≡-refl γ {n = zero}  (c ∷ []) = ⟦ p₁ ⟧' γ {n = zero} (c ∷ [])
      -- Note that p₁ does not accept the empty string, whereas p₂ does.

    parse (node d₁ d₂) (_∣_ {e₁ = true}  {e₂ = true}  p₁ p₂) ≡-refl γ s =        ⟦ p₁ ⟧' γ s  ++        ⟦ p₂ ⟧' γ s
    parse (node d₁ d₂) (_∣_ {e₁ = true}  {e₂ = false} p₁ p₂) ≡-refl γ s =        ⟦ p₁ ⟧' γ s  ++ (↑ <$> ⟦ p₂ ⟧' γ s)
    parse (node d₁ d₂) (_∣_ {e₁ = false} {e₂ = true}  p₁ p₂) ≡-refl γ s = (↑ <$> ⟦ p₁ ⟧' γ s) ++        ⟦ p₂ ⟧' γ s
    parse (node d₁ d₂) (_∣_ {e₁ = false} {e₂ = false} p₁ p₂) ≡-refl γ s =        ⟦ p₁ ⟧' γ s  ++        ⟦ p₂ ⟧' γ s

    parse (step d) (! x) ≡-refl γ s = ⟦ lookup x γ ⟧' γ s

    -- Impossible cases.
    parse leaf         (_·_ {e₁ = true}  p₁ p₂) () _ _
    parse (step d)     (_·_ {e₁ = true}  p₁ p₂) () _ _
    parse leaf         (_·_ {e₁ = false} p₁ p₂) () _ _
    parse (node d₁ d₂) (_·_ {e₁ = false} p₁ p₂) () _ _
    parse leaf         (! x)                    () _ _
    parse (node d₁ d₂) (! x)                    () _ _

open L

⟦_⟧ :  forall {tok Γ e d}
    -> Parser tok Γ e d -> Env tok Γ
    -> [ tok ] -> P [ tok ]
⟦ p ⟧ γ s = toList <$> ⟦ p ⟧' γ (↑ (fromList s))
