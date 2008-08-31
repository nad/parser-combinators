------------------------------------------------------------------------
-- Parser indices
------------------------------------------------------------------------

module RecursiveDescent.Index where

open import Data.Bool
open import Data.Product.Record
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
-- the definition of RecursiveDescent.(Coi|I)nductive.Internal.Parser.

data Corners : Set where
  leaf : Corners
  step : Corners -> Corners
  node : Corners -> Corners -> Corners

Index : Set
Index = Empty × Corners

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
0I = (false , leaf)

1I : Index
1I = (true , leaf)

_∣I_ : Index -> Index -> Index
i₁ ∣I i₂ = (proj₁ i₁ ∨ proj₁ i₂ , node (proj₂ i₁) (proj₂ i₂))

_·I_ : Index -> Index -> Index
i₁ ·I i₂ = ( proj₁ i₁ ∧ proj₁ i₂
           , (if proj₁ i₁ then node (proj₂ i₁) (proj₂ i₂)
                          else step (proj₂ i₁))
           )

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

  leaf≢step : forall {c} -> leaf ≢ step c
  leaf≢step ()

  leaf≢node : forall {c₁ c₂} -> leaf ≢ node c₁ c₂
  leaf≢node ()

  step≢node : forall {c₁ c₂ c₃} -> step c₁ ≢ node c₂ c₃
  step≢node ()

_Corners-≟_ : Decidable {Corners} _≡_
leaf       Corners-≟ leaf         = yes ≡-refl
step c₁    Corners-≟ step  c₂     with c₁ Corners-≟ c₂
step c₁    Corners-≟ step .c₁     | yes ≡-refl = yes ≡-refl
step c₁    Corners-≟ step  c₂     | no  ¬c₁≡c₂ = no (¬c₁≡c₂ ∘ drop-step)
node c₁ c₂ Corners-≟ node  c₃  c₄ with c₁ Corners-≟ c₃ | c₂ Corners-≟ c₄
node c₁ c₂ Corners-≟ node .c₁ .c₂ | yes ≡-refl | yes ≡-refl = yes ≡-refl
node c₁ c₂ Corners-≟ node  c₃  c₄ | no  ¬c₁≡c₂ | _          = no (¬c₁≡c₂ ∘ drop-node₁)
node c₁ c₂ Corners-≟ node  c₃  c₄ | _          | no  ¬c₁≡c₂ = no (¬c₁≡c₂ ∘ drop-node₂)
leaf       Corners-≟ step _       = no leaf≢step
leaf       Corners-≟ node _ _     = no leaf≢node
step _     Corners-≟ leaf         = no (leaf≢step ∘ ≡-sym)
step _     Corners-≟ node _ _     = no step≢node
node _ _   Corners-≟ leaf         = no (leaf≢node ∘ ≡-sym)
node _ _   Corners-≟ step _       = no (step≢node ∘ ≡-sym)

_Index-≟_ : Decidable {Index} _≡_
i₁ Index-≟ i₂ with proj₁ i₁ Bool-≟ proj₁ i₂
                 | proj₂ i₁ Corners-≟ proj₂ i₂
... | yes e₁≡e₂ | yes c₁≡c₂ = yes (≡-cong₂ (_,_) e₁≡e₂ c₁≡c₂)
... | no ¬e₁≡e₂ | _         = no (¬e₁≡e₂ ∘ ≡-cong proj₁)
... | _         | no ¬c₁≡c₂ = no (¬c₁≡c₂ ∘ ≡-cong proj₂)
