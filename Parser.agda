------------------------------------------------------------------------
-- Terminating parser "combinator" interface
------------------------------------------------------------------------

module Parser where

open import Parser.Type public
import Parser.Internal as P
open P public using (Parser; Grammar)

open import Data.List
open import Data.Bool
open import Data.Maybe
open import Data.Product.Record
import Data.Product as Prod
open import Data.Function hiding (_$_)
import Data.BoundedVec.Inefficient as BVec
open import Relation.Nullary
open import Relation.Binary

------------------------------------------------------------------------
-- Run function for the parsers

⟦_⟧ :  forall {tok name i r}
    -> Parser tok name i r -> Grammar tok name
    -> [ tok ] -> [ Prod._×_ r [ tok ] ]
⟦ p ⟧ g s = map (Prod.map-× id BVec.toList)
                (P.parse g p (BVec.fromList s))

-- A variant which only returns parses which leave no remaining input.

⟦_⟧! :  forall {tok name i r}
     -> Parser tok name i r -> Grammar tok name
     -> [ tok ] -> [ r ]
⟦ p ⟧! g s = map Prod.proj₁ (filter (null ∘ Prod.proj₂) (⟦ p ⟧ g s))

------------------------------------------------------------------------
-- Operations on indices

-- (unitI, _·I_) almost forms a monoid.

infixr 50 _·I_

unitI : Index
unitI = (true , leaf)

_·I_ : Index -> Index -> Index
i₁ ·I i₂ = ( proj₁ i₁ ∧ proj₁ i₂
           , if proj₁ i₁ then node (proj₂ i₁) (proj₂ i₂)
                         else step (proj₂ i₁)
           )

------------------------------------------------------------------------
-- Exported combinators

infix  60 !_
infixl 50 _·_ _<·_ _·>_ _$_ _<$_
infixr 40 _∣_

ε : forall {tok name r} -> r -> Parser tok name unitI r
ε = P.ret

sat : forall {tok name r} ->
      (tok -> Maybe r) -> Parser tok name (false , leaf) r
sat = P.sat

fail : forall {tok name r} -> Parser tok name (false , leaf) r
fail = sat (const nothing)

_·_ : forall {tok name e₁ d₁ i₂ r₁ r₂} -> let i₁ = (e₁ , d₁) in
      Parser tok name i₁ (r₁ -> r₂) ->
      Parser tok name i₂ r₁ ->
      Parser tok name (i₁ ·I i₂) r₂
_·_ {e₁ = true } = P.seq₀
_·_ {e₁ = false} = P.seq₁ _

_$_ : forall {tok name i r₁ r₂} ->
      (r₁ -> r₂) ->
      Parser tok name i r₁ ->
      Parser tok name _ r₂
f $ x = ε f · x

_<·_ : forall {tok name i₁ i₂ r₁ r₂} ->
       Parser tok name i₁ r₁ ->
       Parser tok name i₂ r₂ ->
       Parser tok name _ r₁
x <· y = const $ x · y

_·>_ : forall {tok name i₁ i₂ r₁ r₂} ->
       Parser tok name i₁ r₁ ->
       Parser tok name i₂ r₂ ->
       Parser tok name _ r₂
x ·> y = flip const $ x · y

_<$_ : forall {tok name i r₁ r₂} ->
       r₁ ->
       Parser tok name i r₂ ->
       Parser tok name _ r₁
x <$ y = const x $ y

_∣_ : forall {tok name e₁ d₁ e₂ d₂ r} ->
      Parser tok name (e₁ , d₁) r ->
      Parser tok name (e₂ , d₂) r ->
      Parser tok name (e₁ ∨ e₂ , node d₁ d₂) r
_∣_ {e₁ = true } = P.alt₀ _
_∣_ {e₁ = false} = P.alt₁

!_ : forall {tok name e d r} ->
     name (e , d) r -> Parser tok name (e , step d) r
!_ = P.!_

module Token (a : DecSetoid) where

  private
    open module D = DecSetoid a
    open module S = Setoid setoid renaming (carrier to tok)

  -- Parses a given token.

  token : forall {name} -> tok -> Parser tok name (false , leaf) tok
  token x = sat p
    where
    p : tok -> Maybe tok
    p y with x ≟ y
    ... | yes _ = just y
    ... | no  _ = nothing
