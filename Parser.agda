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

NonEmpty : Set
NonEmpty = Bool

data Depth : Set where
  leaf : Depth
  step : Depth -> Depth
  node : Depth -> Depth -> Depth

maybeNode : NonEmpty -> Depth -> Depth -> Depth
maybeNode n d₁ d₂ = if n then d₁ else node d₁ d₂

Index : Set
Index = NonEmpty × Depth

private
  import HeterogeneousCollection as HC
  open module HC' = HC Index

data Parser (Γ : Ctxt) : NonEmpty -> Depth -> Set where
  fail  :  Parser Γ true  leaf
  empty :  Parser Γ false leaf
  sym   :  (carrier -> Bool) -> Parser Γ true leaf
  _·_   :  forall {n₁ d₁ n₂ d₂}
        -> Parser Γ n₁ d₁ -> Parser Γ n₂ d₂
        -> Parser Γ (n₁ ∨ n₂) (maybeNode n₁ d₁ d₂)
  _∣_   :  forall {n₁ d₁ n₂ d₂}
        -> Parser Γ n₁ d₁ -> Parser Γ n₂ d₂
        -> Parser Γ (n₁ ∧ n₂) (node d₁ d₂)
  named :  forall {n d}
        -> Label Γ (n , d) -> Parser Γ n (step d)

T : Ctxt -> Index -> Set
T Γ (n , d) = Parser Γ n d

Env : Ctxt -> Set
Env Γ = Coll (T Γ) Γ

mutual

  -- Ugly workaround since the termination checker does not take
  -- advantage of dotted patterns...

  ⟦_⟧ :  forall {Γ n d}
      -> Parser Γ n d -> Env Γ -> [ carrier ] -> Maybe [ carrier ]
  ⟦ p ⟧ = parse _ p ≡-refl

  private

    parse :  forall {Γ n} d {d'} -> Parser Γ n d' -> d ≡ d'
          -> Env Γ -> [ carrier ] -> Maybe [ carrier ]
    parse ._ fail    ≡-refl ρ s       = nothing
    parse ._ empty   ≡-refl ρ s       = just s
    parse ._ (sym p) ≡-refl ρ (c ∷ s) with p c
    ... | true  = just s
    ... | false = nothing
    parse (node d₁ d₂) (_·_ {n₁ = false} p₁ p₂) ≡-refl ρ s
      with ⟦ p₁ ⟧ ρ s
    ... | nothing = nothing
    ... | just s' = ⟦ p₂ ⟧ ρ s'
    parse d₁ (_·_ {n₁ = true} p₁ p₂) ≡-refl ρ s
      with ⟦ p₁ ⟧ ρ s
    ... | nothing = nothing
    -- ... | just s' = ⟦ p₂ ⟧ ρ s'
    parse (node d₁ d₂) (p₁ ∣ p₂) ≡-refl ρ s =
      lift₂ _++_ (⟦ p₁ ⟧ ρ s) (⟦ p₂ ⟧ ρ s)
    parse (step d) (named x) ≡-refl ρ s = ⟦ lookup x ρ ⟧ ρ s
    parse _ _ _ ρ s = nothing

-- TODO: Keep track of the length of the list, needed for the "true"
-- case.
