------------------------------------------------------------------------
-- Indices
------------------------------------------------------------------------

module Parallel.Index where

open import Data.Product.Record
import Data.Product as Prod; open Prod using () renaming (_,_ to pair)

open import Data.Bool using (Bool; true; false; _∨_; _∧_; if_then_else_)
open import Data.Bool.Properties

open import Data.Nat using (ℕ; zero; suc; _⊔_)
open import Data.Nat.Properties

open import Algebra
import Algebra.Props.BooleanAlgebra as BAlg
import Algebra.Props.DistributiveLattice as DL
private
  module NR = CommutativeSemiringWithoutOne
                ℕ-⊔-⊓-0-commutativeSemiringWithoutOne
  module NL = DL ℕ-distributiveLattice
  module BR = CommutativeSemiring Bool-commutativeSemiring-∨-∧
  module BA = BAlg Bool-booleanAlgebra

open import Logic
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Data.Function

------------------------------------------------------------------------
-- The index type

-- Does the parser accept the empty string?

Empty : Set
Empty = Bool

-- The maximum "distance" to the next parser which is guaranteed to
-- either consume a token or fail.

Distance : Set
Distance = ℕ

-- Parser indices. Note that it is important that the record type used
-- here has η-equality, since otherwise it would be harder to infer
-- the types.

Index : Set
Index = Empty × Distance

import Algebra.FunctionProperties as P; open P (≡-setoid Index)

------------------------------------------------------------------------
-- The basic operations on indices

infixl 50 _·I_
infixl 40 _∣I_

0I : Index
0I = (false , zero)

1I : Index
1I = (true , zero)

_·I_ : Index -> Index -> Index
i₁ ·I i₂ = ( proj₁ i₁ ∧ proj₁ i₂
           , (if proj₁ i₁ then proj₂ i₁ ⊔ proj₂ i₂
                          else proj₂ i₁)
           )

_∣I_ : Index -> Index -> Index
i₁ ∣I i₂ = (proj₁ i₁ ∨ proj₁ i₂ , proj₂ i₁ ⊔ proj₂ i₂)

------------------------------------------------------------------------
-- These operations satisfy some algebraic properties

private

  -- TODO: General code for taking the product of two commutative
  -- monoids. However, I don't want to define this operation for both
  -- Data.Product and Data.Product.Record. Hence I'll probably wait
  -- (at least) until pattern matching on records is possible, since I
  -- plan to merge Data.Product and Data.Product.Record then.

  ∣-assoc : Associative _∣I_
  ∣-assoc i₁ i₂ i₃ =
    ≡-cong₂ _,_ (BR.+-assoc (proj₁ i₁) (proj₁ i₂) (proj₁ i₃))
                (NR.+-assoc (proj₂ i₁) (proj₂ i₂) (proj₂ i₃))

  ∣-comm : Commutative _∣I_
  ∣-comm i₁ i₂ =
    ≡-cong₂ _,_ (BR.+-comm (proj₁ i₁) (proj₁ i₂))
                (NR.+-comm (proj₂ i₁) (proj₂ i₂))

  ∣-identity : Identity 0I _∣I_
  ∣-identity = pair
    (\i -> ≡-cong₂ _,_ (Prod.proj₁ BR.+-identity (proj₁ i))
                       (Prod.proj₁ NR.+-identity (proj₂ i)))
    (\i -> ≡-cong₂ _,_ (Prod.proj₂ BR.+-identity (proj₁ i))
                       (Prod.proj₂ NR.+-identity (proj₂ i)))

  ·-assoc : Associative _·I_
  ·-assoc i₁ i₂ i₃ with proj₁ i₁ | proj₁ i₂
  ·-assoc i₁ i₂ i₃ | false | e₂    = ≡-refl
  ·-assoc i₁ i₂ i₃ | true  | false = ≡-refl
  ·-assoc i₁ i₂ i₃ | true  | true  =
    ≡-cong (_,_ (proj₁ i₃))
           (NR.+-assoc (proj₂ i₁) (proj₂ i₂) (proj₂ i₃))

  ·-identity : Identity 1I _·I_
  ·-identity = pair (\_ -> ≡-refl) (\x -> helper (proj₁ x) (proj₂ x))
    where
    helper : forall e d ->
             _≡_ {a = Index} (e ∧ true , (if e then d ⊔ zero else d))
                             (e        , d)
    helper false d = ≡-refl
    helper true  d = ≡-cong (_,_ true) (Prod.proj₂ NR.+-identity d)

  ·-∣-distrib : _·I_ DistributesOver _∣I_
  ·-∣-distrib = pair
    (\i₁ i₂ i₃ ->
        ≡-cong₂ _,_
                (Prod.proj₁ BR.distrib (proj₁ i₁) (proj₁ i₂) (proj₁ i₃))
                (distribˡ₂ (proj₂ i₁) (proj₂ i₂) (proj₂ i₃) (proj₁ i₁)))
    (\i₁ i₂ i₃ ->
        ≡-cong₂ _,_
                (Prod.proj₂ BR.distrib (proj₁ i₁) (proj₁ i₂) (proj₁ i₃))
                (distribʳ₂ (proj₂ i₁) (proj₂ i₂) (proj₂ i₃)
                                      (proj₁ i₂) (proj₁ i₃)))
    where
    lemma : forall d₁ d₂ d₃ -> d₁ ⊔ (d₂ ⊔ d₃) ≡ d₁ ⊔ d₂ ⊔ (d₁ ⊔ d₃)
    lemma d₁ d₂ d₃ = begin
      d₁       ⊔ (d₂ ⊔ d₃)   ≡⟨ ≡-sym (NL.∧-idempotent d₁)
                                  ⟨ NR.+-pres-≈ ⟩
                                byDef {x = d₂ ⊔ d₃} ⟩
      d₁ ⊔  d₁ ⊔ (d₂ ⊔ d₃)   ≡⟨ NR.+-assoc d₁ d₁ (d₂ ⊔ d₃) ⟩
      d₁ ⊔ (d₁ ⊔ (d₂ ⊔ d₃))  ≡⟨ byDef {x = d₁} ⟨ NR.+-pres-≈ ⟩
                                ≡-sym (NR.+-assoc d₁ d₂ d₃) ⟩
      d₁ ⊔ (d₁ ⊔  d₂ ⊔ d₃)   ≡⟨ byDef {x = d₁} ⟨ NR.+-pres-≈ ⟩
                                  (NR.+-comm d₁ d₂ ⟨ NR.+-pres-≈ ⟩
                                   byDef {x = d₃}) ⟩
      d₁ ⊔ (d₂ ⊔  d₁ ⊔ d₃)   ≡⟨ byDef {x = d₁} ⟨ NR.+-pres-≈ ⟩
                                NR.+-assoc d₂ d₁ d₃ ⟩
      d₁ ⊔ (d₂ ⊔ (d₁ ⊔ d₃))  ≡⟨ ≡-sym $ NR.+-assoc d₁ d₂ (d₁ ⊔ d₃) ⟩
      d₁ ⊔ d₂  ⊔ (d₁ ⊔ d₃)   ∎

    distribˡ₂ : forall d₁ d₂ d₃ e₁ ->
                (if e₁ then d₁ ⊔ (d₂ ⊔ d₃) else d₁) ≡
                (if e₁ then d₁ ⊔ d₂        else d₁) ⊔
                (if e₁ then d₁ ⊔ d₃        else d₁)
    distribˡ₂ d₁ d₂ d₃ true  = lemma d₁ d₂ d₃
    distribˡ₂ d₁ d₂ d₃ false = ≡-sym (NL.∧-idempotent d₁)

    distribʳ₂ : forall d₁ d₂ d₃ e₂ e₃ ->
                (if e₂ ∨ e₃ then d₂ ⊔ d₃ ⊔ d₁ else d₂ ⊔ d₃)
                ≡
                (if e₂ then d₂ ⊔ d₁ else d₂) ⊔
                (if e₃ then d₃ ⊔ d₁ else d₃)
    distribʳ₂ d₁ d₂ d₃ true true = begin
      d₂ ⊔ d₃ ⊔ d₁         ≡⟨ NR.+-comm (d₂ ⊔ d₃) d₁ ⟩
      d₁ ⊔ (d₂ ⊔ d₃)       ≡⟨ lemma d₁ d₂ d₃ ⟩
      d₁ ⊔ d₂ ⊔ (d₁ ⊔ d₃)  ≡⟨ NR.+-comm d₁ d₂ ⟨ NR.+-pres-≈ ⟩
                              NR.+-comm d₁ d₃ ⟩
      d₂ ⊔ d₁ ⊔ (d₃ ⊔ d₁)  ∎
    distribʳ₂ d₁ d₂ d₃ true false = begin
      d₂ ⊔  d₃ ⊔ d₁   ≡⟨ NR.+-assoc d₂ d₃ d₁ ⟩
      d₂ ⊔ (d₃ ⊔ d₁)  ≡⟨ byDef {x = d₂} ⟨ NR.+-pres-≈ ⟩
                         NR.+-comm d₃ d₁ ⟩
      d₂ ⊔ (d₁ ⊔ d₃)  ≡⟨ ≡-sym $ NR.+-assoc d₂ d₁ d₃ ⟩
      d₂ ⊔  d₁ ⊔ d₃   ∎
    distribʳ₂ d₁ d₂ d₃ false true  = NR.+-assoc d₂ d₃ d₁
    distribʳ₂ d₁ d₂ d₃ false false = ≡-refl

·-idempotent : Idempotent _·I_
·-idempotent i = ≡-cong₂ _,_ (BA.∧-idempotent (proj₁ i))
                             (lemma (proj₁ i) (proj₂ i))
  where
  lemma : forall b x -> (if b then x ⊔ x else x) ≡ x
  lemma true  x = NL.∧-idempotent x
  lemma false x = ≡-refl

∣-idempotent : Idempotent _∣I_
∣-idempotent i = ≡-cong₂ _,_ (BA.∨-idempotent (proj₁ i))
                             (NL.∧-idempotent (proj₂ i))

-- Not quite a semiring, but the proper name is too long...

indexSemiring : SemiringWithoutAnnihilatingZero
indexSemiring = record
  { setoid = ≡-setoid Index
  ; _+_    = _∣I_
  ; _*_    = _·I_
  ; 0#     = 0I
  ; 1#     = 1I
  ; isSemiringWithoutAnnihilatingZero = record
    { +-isCommutativeMonoid = record
      { isMonoid = record
        { isSemigroup = record
          { assoc    = ∣-assoc
          ; •-pres-≈ = ≡-cong₂ _∣I_
          }
        ; identity = ∣-identity
        }
      ; comm = ∣-comm
      }
    ; *-isMonoid = record
      { isSemigroup = record
        { assoc    = ·-assoc
        ; •-pres-≈ = ≡-cong₂ _·I_
        }
      ; identity = ·-identity
      }
    ; distrib = ·-∣-distrib
    }
  }

module IndexSemiring =
  SemiringWithoutAnnihilatingZero indexSemiring

nearSemiring : NearSemiring
nearSemiring = record
  { setoid = setoid
  ; _+_    = _+_
  ; _*_    = _*_
  ; 0#     = 0#
  ; isNearSemiring = record
    { +-isMonoid    = +-isMonoid
    ; *-isSemigroup = *-isSemigroup
    ; distribʳ      = Prod.proj₂ distrib
    ; zeroˡ         = \_ -> refl
    }
  }
  where open IndexSemiring

private

  lemma : suc zero ≡ zero -> ⊥
  lemma ()

  -- The indices very nearly form a semiring (∣I, ·I, 0I, 1I). The
  -- only missing piece is that 0I is not a right zero for ·I:

  notRightZero : ¬ RightZero 0I _·I_
  notRightZero zeroʳ = lemma $ ≡-cong proj₂ $
    zeroʳ (false , suc zero)

  -- It might also be worth noting that ·I is not commutative:

  notCommutative : ¬ Commutative _·I_
  notCommutative comm = lemma $ ≡-cong proj₂ $
    comm (true , suc zero) (false , zero)

  -- Note that we don't want these properties to be true. The second
  -- one implies the first, and the first implies that
  --   p = p ⊛> symbol
  -- is an OK definition, even though it is left recursive.
