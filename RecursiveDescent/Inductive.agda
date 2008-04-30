------------------------------------------------------------------------
-- Terminating parser "combinator" interface
------------------------------------------------------------------------

module RecursiveDescent.Inductive where

open import RecursiveDescent.Type public
import RecursiveDescent.Inductive.Internal as P
open P public using (Parser; Grammar)

open import Data.List
open import Data.Bool
open import Data.Maybe
open import Data.Product.Record
import Data.Product as Prod
open import Data.Function
import Data.BoundedVec.Inefficient as BVec

------------------------------------------------------------------------
-- Run function for the parsers

parse :  forall {tok nt i r}
      -> Parser tok nt i r -> Grammar tok nt
      -> [ tok ] -> [ Prod._×_ r [ tok ] ]
parse p g s = map (Prod.map-× id BVec.toList)
                  (P.parse g _ p (BVec.fromList s))

-- A variant which only returns parses which leave no remaining input.

parse-complete :  forall {tok nt i r}
               -> Parser tok nt i r -> Grammar tok nt
               -> [ tok ] -> [ r ]
parse-complete p g s =
  map Prod.proj₁ (filter (null ∘ Prod.proj₂) (parse p g s))

------------------------------------------------------------------------
-- Operations on indices

infixr 50 _·I_

_·I_ : Index -> Index -> Index
i₁ ·I i₂ = ( proj₁ i₁ ∧ proj₁ i₂
           , (if proj₁ i₁ then node (proj₂ i₁) (proj₂ i₂)
                          else proj₂ i₁)
           )

------------------------------------------------------------------------
-- Exported combinators

infix  60 !_
infixl 40 _∣_
infixl 10 _>>=_ _!>>=_

!_ : forall {tok nt e c r} ->
     nt (e , c) r -> Parser tok nt (e , step c) r
!_ = P.!_

symbol : forall {tok nt} -> Parser tok nt 0I tok
symbol = P.symbol

return : forall {tok nt r} -> r -> Parser tok nt 1I r
return = P.ret

fail : forall {tok nt r} -> Parser tok nt 0I r
fail = P.fail

_>>=_ : forall {tok nt e₁ c₁ i₂ r₁ r₂} -> let i₁ = (e₁ , c₁) in
        Parser tok nt i₁ r₁ ->
        (r₁ -> Parser tok nt i₂ r₂) ->
        Parser tok nt (i₁ ·I i₂) r₂
_>>=_ {e₁ = true } = P.bind₀
_>>=_ {e₁ = false} = P.bind₁

-- If the first parser is guaranteed to consume something, then the
-- second parser's index can depend on the result of the first parser.

_!>>=_ : forall {tok nt c₁ r₁ r₂} {i₂ : r₁ -> Index} ->
         let i₁ = (false , c₁) in
         Parser tok nt i₁ r₁ ->
         ((x : r₁) -> Parser tok nt (i₂ x) r₂) ->
         Parser tok nt i₁ r₂
_!>>=_ = P.bind₁

_∣_ : forall {tok nt e₁ c₁ i₂ r} -> let i₁ = (e₁ , c₁) in
      Parser tok nt i₁ r ->
      Parser tok nt i₂ r ->
      Parser tok nt (i₁ ∣I i₂) r
_∣_ {e₁ = true } = P.alt₀
_∣_ {e₁ = false} = P.alt₁ _
