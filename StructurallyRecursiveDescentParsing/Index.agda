------------------------------------------------------------------------
-- Parser indices
------------------------------------------------------------------------

module StructurallyRecursiveDescentParsing.Index where

open import Data.Bool
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.Function

------------------------------------------------------------------------
-- Indices to the parser type

-- Does the parser accept empty strings?

Empty : Set
Empty = Bool

-- The proper left corners of the parser, represented as a tree. See
-- StructurallyRecursiveDescentParsing.Type.

infix 5 _∪_

data Corners : Set where
  ε    : Corners
  step : (c : Corners) → Corners
  _∪_  : (c₁ c₂ : Corners) → Corners

-- The index type.

record Index : Set where
  field
    empty   : Empty
    corners : Corners

open Index public

infix 4 _◇_

_◇_ : Empty → Corners → Index
e ◇ c = record { empty = e; corners = c }

-- Type signature for non-terminals. The second argument is the result
-- type.

NonTerminalType : Set2
NonTerminalType = Index → Set → Set1

------------------------------------------------------------------------
-- Operations on indices

infixr 50 _·_
infixr 40 _∥_

0I : Index
0I = false ◇ ε

1I : Index
1I = true ◇ ε

_∥_ : Index → Index → Index
i₁ ∥ i₂ = empty i₁ ∨ empty i₂ ◇ corners i₁ ∪ corners i₂

_·_ : Index → Index → Index
i₁ · i₂ = (empty i₁ ∧ empty i₂)
          ◇
          (if empty i₁ then corners i₁ ∪ corners i₂
                       else corners i₁ ∪ ε)

drop-steps : Corners → Corners
drop-steps ε         = ε
drop-steps (step c)  = drop-steps c
drop-steps (c₁ ∪ c₂) = drop-steps c₁ ∪ drop-steps c₂

------------------------------------------------------------------------
-- Testing indices for equality

infix 15 _Index-≟_ _Corners-≟_

private

  drop-step : ∀ {c₁ c₂} → step c₁ ≡ step c₂ → c₁ ≡ c₂
  drop-step ≡-refl = ≡-refl

  drop-∪₁ : ∀ {c₁ c₂ c₃ c₄} → c₁ ∪ c₂ ≡ c₃ ∪ c₄ → c₁ ≡ c₃
  drop-∪₁ ≡-refl = ≡-refl

  drop-∪₂ : ∀ {c₁ c₂ c₃ c₄} → c₁ ∪ c₂ ≡ c₃ ∪ c₄ → c₂ ≡ c₄
  drop-∪₂ ≡-refl = ≡-refl

_Corners-≟_ : Decidable {Corners} _≡_
ε         Corners-≟ ε           = yes ≡-refl
step c₁   Corners-≟ step  c₂    with c₁ Corners-≟ c₂
step c₁   Corners-≟ step .c₁    | yes ≡-refl = yes ≡-refl
step c₁   Corners-≟ step  c₂    | no  ¬c₁≡c₂ = no (¬c₁≡c₂ ∘ drop-step)
(c₁ ∪ c₂) Corners-≟ ( c₃ ∪  c₄) with c₁ Corners-≟ c₃ | c₂ Corners-≟ c₄
(c₁ ∪ c₂) Corners-≟ (.c₁ ∪ .c₂) | yes ≡-refl | yes ≡-refl = yes ≡-refl
(c₁ ∪ c₂) Corners-≟ ( c₃ ∪  c₄) | no  ¬c₁≡c₂ | _          = no (¬c₁≡c₂ ∘ drop-∪₁)
(c₁ ∪ c₂) Corners-≟ ( c₃ ∪  c₄) | _          | no  ¬c₁≡c₂ = no (¬c₁≡c₂ ∘ drop-∪₂)
ε         Corners-≟ step _      = no λ()
ε         Corners-≟ (_ ∪ _)     = no λ()
step _    Corners-≟ ε           = no λ()
step _    Corners-≟ (_ ∪ _)     = no λ()
(_ ∪ _)   Corners-≟ ε           = no λ()
(_ ∪ _)   Corners-≟ step _      = no λ()

_Index-≟_ : Decidable {Index} _≡_
i₁ Index-≟ i₂ with empty i₁ Bool-≟ empty i₂
                 | corners i₁ Corners-≟ corners i₂
... | yes e₁≡e₂ | yes c₁≡c₂ = yes (≡-cong₂ _◇_ e₁≡e₂ c₁≡c₂)
... | no ¬e₁≡e₂ | _         = no (¬e₁≡e₂ ∘ ≡-cong empty)
... | _         | no ¬c₁≡c₂ = no (¬c₁≡c₂ ∘ ≡-cong corners)
