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
open import Data.Product
open import Data.Function
import Data.BoundedVec as BVec
open import Relation.Nullary
open import Relation.Binary

------------------------------------------------------------------------
-- Run function for the parsers

⟦_⟧ :  forall {tok name e d r}
    -> Parser tok name e d r -> Grammar tok name
    -> [ tok ] -> [ r × [ tok ] ]
⟦ p ⟧ g s = map (map-× id BVec.toList)
                (P.parse g p (BVec.↑ (BVec.fromList s)))

------------------------------------------------------------------------
-- Exported combinators

infix  60 !_
infixr 50 _·_
infixr 40 _∣_
infixl 30 _⟫=_

ret : forall {tok name r} -> r -> Parser tok name true leaf r
ret = P.ret

sat : forall {tok name r} ->
      (tok -> Maybe r) -> Parser tok name false leaf r
sat = P.sat

fail : forall {tok name r} -> Parser tok name false leaf r
fail = sat (const nothing)

_·_ : forall {tok name e₁ d₁ e₂ d₂ r₁ r₂} ->
      Parser tok name e₁ d₁ (r₁ -> r₂) ->
      Parser tok name e₂ d₂ r₁ ->
      Parser tok name (e₁ ∧ e₂) (if e₁ then node d₁ d₂ else step d₁) r₂
_·_ {e₁ = true } = P.seq₀
_·_ {e₁ = false} = P.seq₁ _

_∣_ : forall {tok name e₁ d₁ e₂ d₂ r} ->
      Parser tok name e₁ d₁ r ->
      Parser tok name e₂ d₂ r ->
      Parser tok name (e₁ ∨ e₂) (node d₁ d₂) r
_∣_ {e₁ = true } = P.alt₀ _
_∣_ {e₁ = false} = P.alt₁

_⟫=_
  : forall {tok name e₁ d₁ e₂ d₂ r₁ r₂} ->
    Parser tok name e₁ d₁ r₁ ->
    (r₁ -> Parser tok name e₂ d₂ r₂) ->
    Parser tok name (e₁ ∧ e₂) (if e₁ then node d₁ d₂ else step d₁) r₂
_⟫=_ {e₁ = true } = P.bind₀
_⟫=_ {e₁ = false} = P.bind₁ _

!_ : forall {tok name e d r} ->
     name e d r -> Parser tok name e (step d) r
!_ = P.!_

module Token (a : DecSetoid) where

  private
    open module D = DecSetoid a
    open module S = Setoid setoid renaming (carrier to tok)

  -- Parses a given token.

  token : forall {name} -> tok -> Parser tok name false leaf tok
  token x = sat p
    where
    p : tok -> Maybe tok
    p y with x ≟ y
    ... | yes _ = just y
    ... | no  _ = nothing
