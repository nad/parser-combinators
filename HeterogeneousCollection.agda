module HeterogeneousCollection where

open import Logic
open import Data.Maybe
open import Relation.Binary.PropositionalEquality1

postulate
  -- Label should be positivity-monotone in its argument.
  Label     :  Set -> Set
  dropLabel :  forall {a b} -> Label a ≡₁ Label b -> a ≡₁ b
  _=?=_     :  forall {a₁ a₂}
            -> (x : Label a₁) -> (y : Label a₂) -> Maybe (x ≅ y)

data Coll : Set1 where
  ∅     : Coll
  _,_≔_ : forall {a} -> Coll -> Label a -> a -> Coll

typesEqual : forall {a b} {x : a} {y : b} -> x ≅ y -> a ≡₁ b
typesEqual ≅-refl = ≡₁-refl

lookup : forall {a} -> Label a -> Coll -> Maybe a
lookup x ∅           = nothing
lookup x (ρ , y ≔ p) with x =?= y
... | nothing = lookup x ρ
... | just eq = just (≡₁-subst (≡₁-sym (dropLabel (typesEqual eq))) p)
