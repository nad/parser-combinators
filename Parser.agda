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

⟦_⟧ :  forall {tok nt i r}
    -> Parser tok nt i r -> Grammar tok nt
    -> [ tok ] -> [ Prod._×_ r [ tok ] ]
⟦ p ⟧ g s = map (Prod.map-× id BVec.toList)
                (P.parse g p (BVec.fromList s))

-- A variant which only returns parses which leave no remaining input.

⟦_⟧! :  forall {tok nt i r}
     -> Parser tok nt i r -> Grammar tok nt
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
                         else proj₂ i₁
           )

------------------------------------------------------------------------
-- Exported combinators

infix  60 !_
infixl 50 _·_ _<·_ _·>_ _$_ _<$_
infixl 40 _∣_

ε : forall {tok nt r} -> r -> Parser tok nt unitI r
ε = P.ε

sat : forall {tok nt r} ->
      (tok -> Maybe r) -> Parser tok nt (false , leaf) r
sat = P.sat

fail : forall {tok nt r} -> Parser tok nt (false , leaf) r
fail = sat (const nothing)

-- Forget whether or not the parser accepts the empty string; take the
-- safe route and pretend that the empty string is accepted. This can
-- be used to make some functions simply typed.

forget : forall {tok nt e d r} ->
         Parser tok nt (e , d) r ->
         Parser tok nt (true , d) r
forget p = P.forget _ p

_·_ : forall {tok nt e₁ d₁ i₂ r₁ r₂} -> let i₁ = (e₁ , d₁) in
      Parser tok nt i₁ (r₁ -> r₂) ->
      Parser tok nt i₂ r₁ ->
      Parser tok nt (i₁ ·I i₂) r₂
_·_ {e₁ = true } = P.seq₀
_·_ {e₁ = false} = P.seq₁ _

_$_ : forall {tok nt i r₁ r₂} ->
      (r₁ -> r₂) ->
      Parser tok nt i r₁ ->
      Parser tok nt _ r₂
f $ x = ε f · x

_<·_ : forall {tok nt i₁ i₂ r₁ r₂} ->
       Parser tok nt i₁ r₁ ->
       Parser tok nt i₂ r₂ ->
       Parser tok nt _ r₁
x <· y = const $ x · y

_·>_ : forall {tok nt i₁ i₂ r₁ r₂} ->
       Parser tok nt i₁ r₁ ->
       Parser tok nt i₂ r₂ ->
       Parser tok nt _ r₂
x ·> y = flip const $ x · y

_<$_ : forall {tok nt i r₁ r₂} ->
       r₁ ->
       Parser tok nt i r₂ ->
       Parser tok nt _ r₁
x <$ y = const x $ y

_∣_ : forall {tok nt e₁ d₁ e₂ d₂ r} ->
      Parser tok nt (e₁ , d₁) r ->
      Parser tok nt (e₂ , d₂) r ->
      Parser tok nt (e₁ ∨ e₂ , node d₁ d₂) r
_∣_ {e₁ = true } = P.alt₀ _
_∣_ {e₁ = false} = P.alt₁

!_ : forall {tok nt e d r} ->
     nt (e , d) r -> Parser tok nt (e , step d) r
!_ = P.!_

module Sym (a : DecSetoid) where

  open DecSetoid a using (_≟_) renaming (carrier to tok)

  -- Parses a given token (symbol).

  sym : forall {nt} -> tok -> Parser tok nt (false , leaf) tok
  sym x = sat p
    where
    p : tok -> Maybe tok
    p y with x ≟ y
    ... | yes _ = just y
    ... | no  _ = nothing
