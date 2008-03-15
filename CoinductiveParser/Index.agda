------------------------------------------------------------------------
-- Indices
------------------------------------------------------------------------

module CoinductiveParser.Index where

open import Data.Product.Record
import Data.Product as Prod; open Prod using () renaming (_,_ to pair)

open import Data.Bool using (Bool; true; false; _∨_; _∧_; if_then_else_)
open import Data.Bool.Properties

open import Data.Nat using (ℕ; zero; suc; _⊔_)
open import Data.Nat.Properties

open import Algebra
import Algebra.Props.DistributiveLattice as DL
private
  module NR = CommutativeSemiringWithoutOne
                ℕ-⊔-⊓-0-commutativeSemiringWithoutOne
  module NL = DL ℕ-distributiveLattice
  module BR = CommutativeSemiring Bool-commutativeSemiring-∨-∧

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
           , if proj₁ i₁ then proj₂ i₁ ⊔ proj₂ i₂
                         else proj₂ i₁
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
    helper : forall e c ->
             _≡_ {a = Index} (e ∧ true , if e then c ⊔ zero else c)
                             (e        , c)
    helper false c = ≡-refl
    helper true  c = ≡-cong (_,_ true) (Prod.proj₂ NR.+-identity c)

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
    lemma : forall c₁ c₂ c₃ -> c₁ ⊔ (c₂ ⊔ c₃) ≡ c₁ ⊔ c₂ ⊔ (c₁ ⊔ c₃)
    lemma c₁ c₂ c₃ = begin
      c₁       ⊔ (c₂ ⊔ c₃)   ≡⟨ ≡-sym (NL.∧-idempotent c₁)
                                  ⟨ NR.+-pres-≈ ⟩
                                byDef {x = c₂ ⊔ c₃} ⟩
      c₁ ⊔  c₁ ⊔ (c₂ ⊔ c₃)   ≡⟨ NR.+-assoc c₁ c₁ (c₂ ⊔ c₃) ⟩
      c₁ ⊔ (c₁ ⊔ (c₂ ⊔ c₃))  ≡⟨ byDef {x = c₁} ⟨ NR.+-pres-≈ ⟩
                                ≡-sym (NR.+-assoc c₁ c₂ c₃) ⟩
      c₁ ⊔ (c₁ ⊔  c₂ ⊔ c₃)   ≡⟨ byDef {x = c₁} ⟨ NR.+-pres-≈ ⟩
                                  (NR.+-comm c₁ c₂ ⟨ NR.+-pres-≈ ⟩
                                   byDef {x = c₃}) ⟩
      c₁ ⊔ (c₂ ⊔  c₁ ⊔ c₃)   ≡⟨ byDef {x = c₁} ⟨ NR.+-pres-≈ ⟩
                                NR.+-assoc c₂ c₁ c₃ ⟩
      c₁ ⊔ (c₂ ⊔ (c₁ ⊔ c₃))  ≡⟨ ≡-sym $ NR.+-assoc c₁ c₂ (c₁ ⊔ c₃) ⟩
      c₁ ⊔ c₂  ⊔ (c₁ ⊔ c₃)   ∎

    distribˡ₂ : forall c₁ c₂ c₃ e₁ ->
                 if e₁ then c₁ ⊔ (c₂ ⊔ c₃) else c₁ ≡
                (if e₁ then c₁ ⊔ c₂        else c₁) ⊔
                (if e₁ then c₁ ⊔ c₃        else c₁)
    distribˡ₂ c₁ c₂ c₃ true  = lemma c₁ c₂ c₃
    distribˡ₂ c₁ c₂ c₃ false = ≡-sym (NL.∧-idempotent c₁)

    distribʳ₂ : forall c₁ c₂ c₃ e₂ e₃ ->
                if e₂ ∨ e₃ then c₂ ⊔ c₃ ⊔ c₁ else (c₂ ⊔ c₃)
                ≡
                (if e₂ then c₂ ⊔ c₁ else c₂) ⊔
                (if e₃ then c₃ ⊔ c₁ else c₃)
    distribʳ₂ c₁ c₂ c₃ true true = begin
      c₂ ⊔ c₃ ⊔ c₁         ≡⟨ NR.+-comm (c₂ ⊔ c₃) c₁ ⟩
      c₁ ⊔ (c₂ ⊔ c₃)       ≡⟨ lemma c₁ c₂ c₃ ⟩
      c₁ ⊔ c₂ ⊔ (c₁ ⊔ c₃)  ≡⟨ NR.+-comm c₁ c₂ ⟨ NR.+-pres-≈ ⟩
                              NR.+-comm c₁ c₃ ⟩
      c₂ ⊔ c₁ ⊔ (c₃ ⊔ c₁)  ∎
    distribʳ₂ c₁ c₂ c₃ true false = begin
      c₂ ⊔  c₃ ⊔ c₁   ≡⟨ NR.+-assoc c₂ c₃ c₁ ⟩
      c₂ ⊔ (c₃ ⊔ c₁)  ≡⟨ byDef {x = c₂} ⟨ NR.+-pres-≈ ⟩
                         NR.+-comm c₃ c₁ ⟩
      c₂ ⊔ (c₁ ⊔ c₃)  ≡⟨ ≡-sym $ NR.+-assoc c₂ c₁ c₃ ⟩
      c₂ ⊔  c₁ ⊔ c₃   ∎
    distribʳ₂ c₁ c₂ c₃ false true  = NR.+-assoc c₂ c₃ c₁
    distribʳ₂ c₁ c₂ c₃ false false = ≡-refl

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
