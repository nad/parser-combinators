------------------------------------------------------------------------
-- Terminating parsers
------------------------------------------------------------------------

open import Relation.Binary

module Parser (a : DecSetoid) where

open import Data.Bool
open import Data.List
open import Data.Product
open import Data.Maybe
open import Logic
private
  open module D = DecSetoid a
  open module S = Setoid setoid

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
  open module HC' = HC Index

-- Parsers. The context lists all named parsers which can be used.

data Parser (Γ : Ctxt) : Empty -> Depth -> Set where
  fail  :  Parser Γ false leaf
  empty :  Parser Γ true  leaf
  sym   :  (carrier -> Bool) -> Parser Γ false leaf
  _·_   :  forall {e₁ d₁ e₂ d₂}
        -> Parser Γ e₁ d₁ -> Parser Γ e₂ d₂
        -> Parser Γ (e₁ ∧ e₂) (maybeNode e₁ d₁ d₂)
  _∣_   :  forall {e₁ d₁ e₂ d₂}
        -> Parser Γ e₁ d₁ -> Parser Γ e₂ d₂
        -> Parser Γ (e₁ ∨ e₂) (node d₁ d₂)
  named :  forall {e d}
        -> Label Γ (e , d) -> Parser Γ e (step d)

-- Environments.

Env : Ctxt -> Set
Env Γ = Coll (P Γ) Γ
  where
  P : Ctxt -> Index -> Set
  P Γ (e , d) = Parser Γ e d

mutual

  -- The run function for the parsers.

  -- Implemented using an ugly workaround since the termination
  -- checker does not take advantage of dotted patterns...

  ⟦_⟧ :  forall {Γ e d}
      -> Parser Γ e d -> Env Γ -> [ carrier ] -> Maybe [ carrier ]
  ⟦ p ⟧ = parse _ p ≡-refl

  private

    parse :  forall {Γ e} d {d'} -> Parser Γ e d' -> d ≡ d'
          -> Env Γ -> [ carrier ] -> Maybe [ carrier ]
    parse ._ fail    ≡-refl ρ s       = nothing
    parse ._ empty   ≡-refl ρ s       = just s
    parse ._ (sym p) ≡-refl ρ (c ∷ s) with p c
    ... | true  = just s
    ... | false = nothing
    parse (node d₁ d₂) (_·_ {e₁ = true} p₁ p₂) ≡-refl ρ s
      with ⟦ p₁ ⟧ ρ s
    ... | nothing = nothing
    ... | just s' = ⟦ p₂ ⟧ ρ s'
    parse d₁ (_·_ {e₁ = false} p₁ p₂) ≡-refl ρ s
      with ⟦ p₁ ⟧ ρ s
    ... | nothing = nothing
    -- ... | just s' = ⟦ p₂ ⟧ ρ s'  -- This call is fine, but Agda cannot see it.
    parse (node d₁ d₂) (p₁ ∣ p₂) ≡-refl ρ s =
      lift₂ _++_ (⟦ p₁ ⟧ ρ s) (⟦ p₂ ⟧ ρ s)
    parse (step d) (named x) ≡-refl ρ s = ⟦ lookup x ρ ⟧ ρ s
    parse _        _         _      ρ s = nothing
