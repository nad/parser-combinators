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

data Corners : Set where
  leaf : Corners
  step : Corners -> Corners
  node : Corners -> Corners -> Corners

-- The index type.

record Index : Set where
  field
    empty   : Empty
    corners : Corners

open Index public

infix 4 _◇_

_◇_ : Empty -> Corners -> Index
e ◇ c = record { empty = e; corners = c }

-- The parser type signature. The second argument is the result type.

ParserType : Set1
ParserType = Index -> Set -> Set

ParserType₁ : Set2
ParserType₁ = Index -> Set -> Set1

------------------------------------------------------------------------
-- Operations on indices

infixr 50 _·I_
infixr 40 _∣I_

0I : Index
0I = false ◇ leaf

1I : Index
1I = true ◇ leaf

_∣I_ : Index -> Index -> Index
i₁ ∣I i₂ = empty i₁ ∨ empty i₂ ◇ node (corners i₁) (corners i₂)

_·I_ : Index -> Index -> Index
i₁ ·I i₂ = empty i₁ ∧ empty i₂
           ◇
           (if empty i₁ then node (corners i₁) (corners i₂)
                        else step (corners i₁))

------------------------------------------------------------------------
-- Testing indices for equality

infix 15 _Index-≟_ _Corners-≟_

private

  drop-step : forall {c₁ c₂} -> step c₁ ≡ step c₂ -> c₁ ≡ c₂
  drop-step ≡-refl = ≡-refl

  drop-node₁ : forall {c₁ c₂ c₃ c₄} ->
               node c₁ c₂ ≡ node c₃ c₄ -> c₁ ≡ c₃
  drop-node₁ ≡-refl = ≡-refl

  drop-node₂ : forall {c₁ c₂ c₃ c₄} ->
               node c₁ c₂ ≡ node c₃ c₄ -> c₂ ≡ c₄
  drop-node₂ ≡-refl = ≡-refl

_Corners-≟_ : Decidable {Corners} _≡_
leaf       Corners-≟ leaf         = yes ≡-refl
step c₁    Corners-≟ step  c₂     with c₁ Corners-≟ c₂
step c₁    Corners-≟ step .c₁     | yes ≡-refl = yes ≡-refl
step c₁    Corners-≟ step  c₂     | no  ¬c₁≡c₂ = no (¬c₁≡c₂ ∘ drop-step)
node c₁ c₂ Corners-≟ node  c₃  c₄ with c₁ Corners-≟ c₃ | c₂ Corners-≟ c₄
node c₁ c₂ Corners-≟ node .c₁ .c₂ | yes ≡-refl | yes ≡-refl = yes ≡-refl
node c₁ c₂ Corners-≟ node  c₃  c₄ | no  ¬c₁≡c₂ | _          = no (¬c₁≡c₂ ∘ drop-node₁)
node c₁ c₂ Corners-≟ node  c₃  c₄ | _          | no  ¬c₁≡c₂ = no (¬c₁≡c₂ ∘ drop-node₂)
leaf       Corners-≟ step _       = no \()
leaf       Corners-≟ node _ _     = no \()
step _     Corners-≟ leaf         = no \()
step _     Corners-≟ node _ _     = no \()
node _ _   Corners-≟ leaf         = no \()
node _ _   Corners-≟ step _       = no \()

_Index-≟_ : Decidable {Index} _≡_
i₁ Index-≟ i₂ with empty i₁ Bool-≟ empty i₂
                 | corners i₁ Corners-≟ corners i₂
... | yes e₁≡e₂ | yes c₁≡c₂ = yes (≡-cong₂ _◇_ e₁≡e₂ c₁≡c₂)
... | no ¬e₁≡e₂ | _         = no (¬e₁≡e₂ ∘ ≡-cong empty)
... | _         | no ¬c₁≡c₂ = no (¬c₁≡c₂ ∘ ≡-cong corners)
